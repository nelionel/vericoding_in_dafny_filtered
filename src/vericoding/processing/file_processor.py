"""File processing logic."""

import hashlib
import logging
import re
import time
import traceback
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, replace
from pathlib import Path
from collections.abc import Callable

import wandb
from tqdm import tqdm

from ..core.config import ProcessingConfig
from ..core.llm_providers import create_llm_provider, LLMProvider
from ..core.prompts import PromptLoader
from ..core.language_tools import verify_file
from ..core.llm_providers import call_llm, call_llm_detailed, increment_problems_processed
from ..utils.io_utils import save_iteration_code
from .code_fixer import apply_json_replacements
from .cheat_checker import has_final_failure_cheats, check_for_cheats

# Import for Lean preprocessing
from ..preprocessing import preprocess_lean_file, ensure_mathlib_import


def _get_path_relative_to_lean_root(file_path: str) -> Path | None:
    """Get path relative to Lean library root (benchmarks/lean or lean/).

    Returns None if no Lean library root found in path.

    Examples:
        benchmarks/lean/test/file.lean -> test/file.lean
        lean/Generated/Module.lean -> Generated/Module.lean
    """
    file_obj = Path(file_path)
    if "lean" in file_obj.parts:
        lean_idx = file_obj.parts.index("lean")
        return Path(*file_obj.parts[lean_idx + 1 :])
    return None


def get_relative_path_for_output(config: ProcessingConfig, file_path: str) -> Path:
    """Get relative path for output files, preserving Lean library structure.

    For Lean: preserves path relative to benchmarks/lean (library root)
    For others: relative to config.files_dir

    Examples:
        Lean: benchmarks/lean/test/file.lean -> test/file.lean
        Dafny: specs/subdir/file.dfy -> subdir/file.dfy (if files_dir=specs)
    """
    if config.language == "lean":
        relative = _get_path_relative_to_lean_root(file_path)
        if relative:
            return relative

    # Fallback to standard relative path
    return Path(file_path).relative_to(Path(config.files_dir))


def count_placeholders(original_code: str, language: str) -> int:
    """Count placeholders in original code for JSON array sizing.

    Args:
        original_code: The original code content
        language: The programming language ("lean", "dafny", "verus")

    Returns:
        Number of placeholders that need to be replaced

    Raises:
        ValueError: If unsupported language is provided
    """
    if language == "lean":
        # Count sorries only inside editable sections (vc-definitions, vc-theorems, vc-helpers)
        editable_sections = []
        for section_name in ["vc-definitions", "vc-theorems", "vc-helpers"]:
            pattern = rf"<{section_name}>(.*?)</{section_name}>"
            matches = list(re.finditer(pattern, original_code, re.DOTALL))
            editable_sections.extend(
                [(match.start(), match.end()) for match in matches]
            )

        sorry_count = 0
        search_start = 0
        while True:
            pos = original_code.find("sorry", search_start)
            if pos == -1:
                break
            # Only count if inside an editable section
            in_editable_section = any(
                start <= pos < end for start, end in editable_sections
            )
            if in_editable_section:
                sorry_count += 1
            search_start = pos + 1

        # Also count vc-helpers sections themselves (they can be replaced with helper content)
        placeholder_count = sorry_count + original_code.count("<vc-helpers>")
    elif language in ("dafny", "verus"):
        placeholder_count = original_code.count("<vc-code>") + original_code.count(
            "<vc-helpers>"
        )
    else:
        raise ValueError(
            f"Unsupported language: {language}. Supported languages are: lean, dafny, verus"
        )

    return placeholder_count


# Set up a basic logger
logging.basicConfig(level=logging.INFO, format="%(message)s")
logger = logging.getLogger(__name__)


@dataclass
class LLMResponse:
    """Individual LLM response data."""

    file: str
    response_type: str  # "generate_code" or "fix_verification"
    iteration: int
    prompt_hash: str
    response_content: str
    json_parsed_successfully: bool
    timestamp: float
    # Token usage and cost
    input_tokens: int = 0
    output_tokens: int = 0
    cost_usd: float = 0.0
    # Timing information
    llm_duration_sec: float = 0.0
    validation_duration_sec: float = 0.0
    total_duration_sec: float = 0.0
    # Additional data
    prompt: str = ""
    extracted_code: str = ""
    validation_result: str = "UNKNOWN"
    next_prompt: str = ""


@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool
    file: str
    output: str | None
    error: str | None
    has_bypass: bool
    original_compilation_failed: bool = False
    generate_prompt: str | None = None
    fix_prompts: list[str] | None = None
    llm_responses: list[LLMResponse] | None = None


def resolve_llm_provider(
    config: ProcessingConfig,
    llm_provider_factory: Callable[[], tuple[LLMProvider, str]] | None,
) -> tuple[LLMProvider, str]:
    """Return an LLM provider using the supplied factory when available."""
    if llm_provider_factory:
        return llm_provider_factory()
    return create_llm_provider(config.llm)


def process_spec_file(
    config: ProcessingConfig,
    prompt_loader: PromptLoader,
    file_path: str,
    llm_provider_factory: Callable[[], tuple[LLMProvider, str]] | None = None,
) -> ProcessingResult:
    """Process a single specification file."""
    # Initialize tracking tables and response collection
    failure_table = None
    llm_responses = []
    if wandb.run:
        failure_table = wandb.Table(
            columns=[
                "file",
                "iteration",
                "spec_hash",
                "code_hash",
                "error_msg",
                "proof_state",
                "timestamp",
            ]
        )

    try:
        logger.info(f"Processing: {Path(file_path).name}")

        # Read the original file
        with Path(file_path).open() as f:
            original_code = f.read()

        # Apply mandatory Lean preprocessing (Mathlib import)
        if config.language == "lean":
            original_code = ensure_mathlib_import(original_code)

        # Apply optional Lean preprocessing (sorry wrapping) if assume-unformatted-lean is enabled
        if config.language == "lean" and config.assume_unformatted_lean:
            original_code = preprocess_lean_file(original_code)

        # Calculate relative path from input directory to preserve hierarchy
        # For Lean, this preserves path relative to benchmarks/lean (library root)
        relative_path = get_relative_path_for_output(config, file_path)
        base_file_name = Path(file_path).stem

        # Track prompts for W&B logging
        all_fix_prompts = []

        # Save original code
        save_iteration_code(config, relative_path, 0, original_code, "original")

        # Check if original file has compilation errors
        logger.info("  Checking original file for compilation errors...")
        original_verification = verify_file(config, file_path)
        original_compilation_failed = not original_verification.success

        if original_compilation_failed:
            logger.info(f"  ⚠️  Original file has issues: {original_verification.error}")
            logger.info("  Will attempt to fix during processing...")

        # Step 1: Generate code from specifications
        logger.info("  Step 1: Generating code from specifications...")
        try:
            # Count placeholders in original code for JSON array sizing
            placeholder_count = count_placeholders(original_code, config.language)

            generate_prompt = prompt_loader.format_prompt(
                "generate_code",
                code=original_code,
                placeholder_count=placeholder_count,
                max_iterations=config.max_iterations,
            )
        except KeyError as e:
            logger.info(f"  ✗ Prompt error: {e}")
            logger.info(f"  Available prompts: {list(prompt_loader.prompts.keys())}")
            raise
        except Exception as e:
            logger.info(f"  ✗ Error formatting prompt: {e}")
            raise

        # Create LLM provider for this request (allows overriding backend)
        llm_provider, _ = resolve_llm_provider(config, llm_provider_factory)
        
        # Call LLM and capture full metadata
        llm_result = call_llm_detailed(llm_provider, config, generate_prompt, wandb)
        generated_response = llm_result["text"]
        generate_tokens_in = llm_result["input_tokens"]
        generate_tokens_out = llm_result["output_tokens"]
        generate_llm_duration = llm_result["llm_duration_sec"]
        generate_cost = llm_result["cost_usd"]

        # IMMEDIATELY save raw response to debug folder before any parsing
        if config.debug_mode:
            relative_path = get_relative_path_for_output(config, file_path)
            base_file_name = Path(file_path).stem
            debug_dir = (
                Path(config.output_dir) / "debug" / relative_path.parent
                if str(relative_path.parent) != "."
                else Path(config.output_dir) / "debug"
            )
            debug_dir.mkdir(parents=True, exist_ok=True)

            raw_response_file = (
                debug_dir / f"{base_file_name}_raw_generate_response.txt"
            )
            with raw_response_file.open("w") as f:
                f.write("=== Raw LLM Generate Response ===\n")
                f.write(f"Length: {len(generated_response)} characters\n")
                f.write("-" * 80 + "\n")
                f.write(generated_response)
                f.write("\n" + "-" * 80 + "\n")

        # Apply JSON replacements to original code (new approach)
        try:
            generated_code, json_error = apply_json_replacements(
                config, original_code, generated_response
            )
        except Exception as e:
            error_msg = f"Failed to apply JSON replacements: {str(e)}\n\nFull traceback:\n{traceback.format_exc()}"
            logger.error(error_msg)
            raise RuntimeError(error_msg) from e

        # If JSON parsing failed, try once more with a fresh LLM call
        if json_error and "JSON parsing failed" in json_error:
            logger.info("  ⚠️  JSON parsing failed, attempting retry...")
            try:
                retry_llm_result = call_llm_detailed(llm_provider, config, generate_prompt, wandb)
                retry_response = retry_llm_result["text"]
                generated_code, json_error = apply_json_replacements(
                    config, original_code, retry_response
                )

                if not json_error:
                    logger.info("  ✓ Retry successful - JSON parsed correctly")
                    # Update the response and metadata for logging
                    generated_response = retry_response
                    generate_tokens_in = retry_llm_result["input_tokens"]
                    generate_tokens_out = retry_llm_result["output_tokens"]
                    generate_llm_duration = retry_llm_result["llm_duration_sec"]
                    generate_cost = retry_llm_result["cost_usd"]
                else:
                    logger.info(f"  ✗ Retry also failed: {json_error}")
            except Exception as e:
                logger.error(f"  ✗ Retry attempt failed with error: {str(e)}")
                # Keep original error

        # Collect LLM response data with full metadata
        if wandb.run:
            llm_responses.append(
                LLMResponse(
                    file=file_path,
                    response_type="generate_code",
                    iteration=0,  # iteration 0 for initial generation
                    prompt_hash=hashlib.md5(generate_prompt.encode()).hexdigest()[:8],
                    response_content=generated_response,
                    json_parsed_successfully=json_error is None,
                    timestamp=time.time(),
                    input_tokens=generate_tokens_in,
                    output_tokens=generate_tokens_out,
                    cost_usd=generate_cost,
                    llm_duration_sec=generate_llm_duration,
                    validation_duration_sec=0.0,  # Will be set during verification
                    total_duration_sec=generate_llm_duration,  # Will be updated after verification
                    prompt=generate_prompt,
                    extracted_code=generated_code if not json_error else "",
                    validation_result="NOT_YET_VERIFIED",
                    next_prompt="",
                )
            )

        # If JSON parsing failed, treat it as a verification failure
        if json_error:
            logger.info(f"  ✗ {json_error}")

            # Log JSON parsing failure to wandb failure table only
            if wandb.run:
                if failure_table is not None:
                    failure_table.add_data(
                        file_path,
                        0,  # iteration 0 for JSON parsing failures
                        hashlib.md5(original_code.encode()).hexdigest()[:8],
                        "",  # no generated code hash since parsing failed
                        json_error,
                        "",  # no proof state for JSON errors
                        time.time(),
                    )

            # Increment problems processed counter
            increment_problems_processed()
            
            return ProcessingResult(
                success=False,
                file=file_path,
                output=None,
                error=json_error,
                has_bypass=False,
                original_compilation_failed=original_compilation_failed,
                generate_prompt=generate_prompt,
                fix_prompts=[],
                llm_responses=llm_responses if wandb.run and llm_responses else None,
            )

        # Save initial generated code
        save_iteration_code(config, relative_path, 1, generated_code, "generated")

        # Create output file path preserving directory structure
        relative_dir = relative_path.parent
        output_subdir = (
            Path(config.output_dir) / relative_dir
            if str(relative_dir) != "."
            else Path(config.output_dir)
        )

        # Thread-safe directory creation
        from ..utils.io_utils import file_write_lock

        with file_write_lock():
            output_subdir.mkdir(parents=True, exist_ok=True)

        output_path = (
            output_subdir
            / f"{base_file_name}_impl{config.language_config.file_extension}"
        )
        with output_path.open("w") as f:
            f.write(generated_code)

        # Run verification iterations
        current_code = generated_code
        success = False
        last_verification = None

        for iteration in range(1, config.max_iterations + 1):
            logger.info(
                f"  Iteration {iteration}/{config.max_iterations}: Verifying..."
            )

            # Write current code to file
            with output_path.open("w") as f:
                f.write(current_code)

            # Save current working version for this iteration
            save_iteration_code(
                config, relative_path, iteration, current_code, "current"
            )

            # Verify and capture timing
            verify_start = time.time()
            verification = verify_file(config, str(output_path))
            verification_duration = time.time() - verify_start
            last_verification = verification
            
            # Update the previous LLMResponse with verification result
            if wandb.run and llm_responses:
                # For iteration 1, update generate response (index 0)
                # For iteration N>1, update fix response from iteration N-1 (index N-1)
                resp_index = iteration - 1
                if resp_index < len(llm_responses):
                    llm_responses[resp_index] = replace(
                        llm_responses[resp_index],
                        validation_duration_sec=verification_duration,
                        total_duration_sec=llm_responses[resp_index].llm_duration_sec + verification_duration,
                        validation_result="PASS" if verification.success else "FAIL",
                        extracted_code=current_code,
                    )

            # Check for cheats in final code - combine with verification output
            if has_final_failure_cheats(current_code, config.language):
                cheats = check_for_cheats(current_code, config.language)
                cheat_descriptions = [desc for _, desc in cheats]
                logger.info(
                    f"    ⚠️ Final code contains verification bypasses: {'; '.join(cheat_descriptions)}"
                )

                # Combine cheat message with original verification result
                cheat_message = f"VERIFICATION BYPASSES DETECTED: {'; '.join(cheat_descriptions)}. Code contains verification bypasses and cannot be considered successfully verified."

                if verification.success:
                    # Verification succeeded but cheats found
                    combined_error = f"{cheat_message}\n\nNote: Verification succeeded but verification bypasses prevent final success."
                    logger.info(
                        "    ✗ Marking as failed due to verification bypasses (verification succeeded)"
                    )
                else:
                    # Verification failed AND cheats found - combine both messages
                    original_error = verification.error or "Verification failed"
                    combined_error = f"{cheat_message}\n\nOriginal verification output:\n{original_error}"
                    logger.info(
                        "    ✗ Failed due to both verification errors AND verification bypasses"
                    )

                verification = replace(
                    verification, success=False, error=combined_error
                )

            # Log failure details to wandb table only (no per-problem plots)
            if wandb.run:
                if not verification.success and failure_table is not None:
                    failure_table.add_data(
                        file_path,
                        iteration,
                        hashlib.md5(original_code.encode()).hexdigest()[:8],
                        hashlib.md5(current_code.encode()).hexdigest()[:8],
                        verification.error
                        if verification.error
                        else "Unknown error",  # Full error message
                        "",  # Proof state would come from lean tools
                        time.time(),
                    )

            if verification.success:
                logger.info("    ✓ Verification successful!")
                success = True
                break
            else:
                # Save full error log to debug directory
                if config.debug_mode and verification.error:
                    error_log_path = (
                        Path(config.output_dir) / "debug" / relative_path.parent
                        if str(relative_path.parent) != "."
                        else Path(config.output_dir) / "debug"
                    ) / f"{base_file_name}_iter{iteration}_error.log"

                    error_log_path.parent.mkdir(parents=True, exist_ok=True)
                    with error_log_path.open("w") as f:
                        f.write(f"=== Verification Error - Iteration {iteration} ===\n")
                        f.write(f"File: {file_path}\n")
                        f.write(f"Time: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                        f.write("\nFull Error Output:\n")
                        f.write("-" * 80 + "\n")
                        f.write(verification.error)
                        f.write("\n" + "-" * 80 + "\n")
                        if verification.output:
                            f.write("\nAdditional Output:\n")
                            f.write(verification.output)
                    logger.info(
                        f"    💾 Saved full error log to: debug/{relative_path.parent}/{base_file_name}_iter{iteration}_error.log"
                    )

                logger.info(
                    f"    ✗ Verification failed: {verification.error[:200] if verification.error else 'Unknown error'}..."
                )

            # Try to fix issues (both compilation and verification errors)
            error_details = verification.error or "Unknown error"

            # Only attempt fix if not on last iteration
            if iteration < config.max_iterations:
                logger.info("    Attempting to fix errors...")
                # Count placeholders in original code for JSON array sizing (not current code!)
                placeholder_count = count_placeholders(original_code, config.language)

                fix_prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=current_code,
                    original_code=original_code,
                    errorDetails=error_details,
                    iteration=iteration + 1,
                    placeholder_count=placeholder_count,
                    max_iterations=config.max_iterations,
                )

                # Track fix prompt for W&B logging
                all_fix_prompts.append(fix_prompt)

                try:
                    # Create LLM provider for fix request
                    llm_provider, _ = resolve_llm_provider(config, llm_provider_factory)
                    
                    # Call LLM and capture full metadata
                    fix_llm_result = call_llm_detailed(llm_provider, config, fix_prompt, wandb)
                    fix_response = fix_llm_result["text"]
                    fix_tokens_in = fix_llm_result["input_tokens"]
                    fix_tokens_out = fix_llm_result["output_tokens"]
                    fix_llm_duration = fix_llm_result["llm_duration_sec"]
                    fix_cost = fix_llm_result["cost_usd"]

                    # IMMEDIATELY save raw response to debug folder before any parsing
                    if config.debug_mode:
                        relative_path = Path(file_path).relative_to(
                            Path(config.files_dir)
                        )
                        base_file_name = Path(file_path).stem
                        debug_dir = (
                            Path(config.output_dir) / "debug" / relative_path.parent
                            if str(relative_path.parent) != "."
                            else Path(config.output_dir) / "debug"
                        )
                        debug_dir.mkdir(parents=True, exist_ok=True)

                        raw_response_file = (
                            debug_dir
                            / f"{base_file_name}_raw_fix_response_iter{iteration}.txt"
                        )
                        with raw_response_file.open("w") as f:
                            f.write(
                                f"=== Raw LLM Fix Response - Iteration {iteration} ===\n"
                            )
                            f.write(f"Length: {len(fix_response)} characters\n")
                            f.write("-" * 80 + "\n")
                            f.write(fix_response)
                            f.write("\n" + "-" * 80 + "\n")

                    # Apply JSON replacements for fix to the ORIGINAL file (which has placeholders)
                    # This ensures we're replacing sorry/vc-code tags, not broken implementations
                    try:
                        fixed_code, fix_json_error = apply_json_replacements(
                            config, original_code, fix_response
                        )
                    except Exception as e:
                        error_msg = f"Failed to apply JSON replacements: {str(e)}\n\nFull traceback:\n{traceback.format_exc()}"
                        logger.error(error_msg)
                        raise RuntimeError(error_msg) from e

                    # Collect LLM fix response data with full metadata
                    if wandb.run:
                        llm_responses.append(
                            LLMResponse(
                                file=file_path,
                                response_type="fix_verification",
                                iteration=iteration,
                                prompt_hash=hashlib.md5(
                                    fix_prompt.encode()
                                ).hexdigest()[:8],
                                response_content=fix_response,
                                json_parsed_successfully=fix_json_error is None,
                                timestamp=time.time(),
                                input_tokens=fix_tokens_in,
                                output_tokens=fix_tokens_out,
                                cost_usd=fix_cost,
                                llm_duration_sec=fix_llm_duration,
                                validation_duration_sec=0.0,  # Will be set in next iteration's verification
                                total_duration_sec=fix_llm_duration,  # Will be updated after next verification
                                prompt=fix_prompt,
                                extracted_code=fixed_code if not fix_json_error else "",
                                validation_result="NOT_YET_VERIFIED",
                                next_prompt="",
                            )
                        )

                    # If JSON parsing failed during fix, treat as iteration failure
                    if fix_json_error:
                        logger.info(f"    ✗ Fix JSON parsing failed: {fix_json_error}")

                        # Log fix parsing failure to wandb
                        if wandb.run and failure_table is not None:
                            failure_table.add_data(
                                file_path,
                                iteration,
                                hashlib.md5(original_code.encode()).hexdigest()[:8],
                                hashlib.md5(current_code.encode()).hexdigest()[:8],
                                f"Fix JSON parsing failed: {fix_json_error}",
                                "",
                                time.time(),
                            )
                        continue  # Skip to next iteration

                    current_code = fixed_code
                    logger.info(f"    Generated fix for iteration {iteration}")

                    # Fixed code will be saved in next iteration
                except Exception as e:
                    logger.info(f"    ✗ Failed to generate fix: {str(e)}")
                    break

        if success:
            logger.info(f"  ✓ Successfully generated and verified: {output_path.name}")

            # Track success in wandb (aggregate only, no per-problem plots)
            if wandb.run:
                wandb.log({"success_count": 1})

            # Increment problems processed counter
            increment_problems_processed()
            
            return ProcessingResult(
                success=True,
                file=str(relative_path),
                output=str(output_path),
                error=None,
                has_bypass=False,
                original_compilation_failed=original_compilation_failed,
                generate_prompt=generate_prompt,
                fix_prompts=all_fix_prompts if all_fix_prompts else None,
                llm_responses=llm_responses if wandb.run and llm_responses else None,
            )
        else:
            error_msg = (
                last_verification.error
                if last_verification
                else "Unknown verification error"
            )
            logger.info(
                f"  ✗ Failed to verify after {config.max_iterations} iterations: {error_msg[:200] if error_msg else 'Unknown error'}..."
            )

            # Track failure in wandb (aggregate only, no per-problem plots)
            if wandb.run:
                wandb.log({"failure_count": 1})

                # Add final failure to table
                if failure_table is not None:
                    failure_table.add_data(
                        file_path,
                        config.max_iterations,
                        hashlib.md5(original_code.encode()).hexdigest()[:8],
                        hashlib.md5(
                            current_code.encode()
                            if "current_code" in locals()
                            else generated_code.encode()
                        ).hexdigest()[:8],
                        error_msg
                        if error_msg
                        else "Unknown error",  # Full error message
                        "",
                        time.time(),
                    )

            # Increment problems processed counter
            increment_problems_processed()
            
            return ProcessingResult(
                success=False,
                file=str(relative_path),
                output=str(output_path),
                error=error_msg,
                has_bypass=False,
                original_compilation_failed=original_compilation_failed,
                generate_prompt=generate_prompt,
                fix_prompts=all_fix_prompts if all_fix_prompts else None,
                llm_responses=llm_responses if wandb.run and llm_responses else None,
            )

    except Exception as e:
        logger.info(f"✗ Failed: {Path(file_path).name} - {str(e)}")

        # Track exception in wandb (aggregate only, no per-problem plots)
        if wandb.run:
            wandb.log({"exception_count": 1})

        # Increment problems processed counter
        increment_problems_processed()
        
        return ProcessingResult(
            success=False,
            file=str(relative_path)
            if "relative_path" in locals()
            else Path(file_path).name,
            error=str(e),
            output=None,
            has_bypass=False,
            original_compilation_failed="original_compilation_failed" in locals()
            and original_compilation_failed,
            generate_prompt=generate_prompt if "generate_prompt" in locals() else None,
            fix_prompts=all_fix_prompts
            if "all_fix_prompts" in locals() and all_fix_prompts
            else None,
            llm_responses=llm_responses
            if wandb.run and "llm_responses" in locals() and llm_responses
            else None,
        )
    finally:
        # Log failure table to W&B and save LLM responses to debug folder
        if wandb.run:
            if failure_table is not None and len(failure_table.data) > 0:
                wandb.log({"verification_failures": failure_table})

            # Save LLM responses to debug folder
            if config.debug_mode and llm_responses:
                relative_path = get_relative_path_for_output(config, file_path)
                base_file_name = Path(file_path).stem
                debug_dir = (
                    Path(config.output_dir) / "debug" / relative_path.parent
                    if str(relative_path.parent) != "."
                    else Path(config.output_dir) / "debug"
                )
                debug_dir.mkdir(parents=True, exist_ok=True)

                for i, response in enumerate(llm_responses):
                    response_file = (
                        debug_dir
                        / f"{base_file_name}_llm_response_{response.response_type}_iter{response.iteration}.txt"
                    )
                    with response_file.open("w") as f:
                        f.write(
                            f"=== LLM Response - {response.response_type} - Iteration {response.iteration} ===\n"
                        )
                        f.write(f"File: {response.file}\n")
                        f.write(f"Prompt Hash: {response.prompt_hash}\n")
                        f.write(
                            f"JSON Parsed Successfully: {response.json_parsed_successfully}\n"
                        )
                        f.write(f"Timestamp: {response.timestamp}\n")
                        f.write(
                            f"Content Length: {len(response.response_content)} chars\n"
                        )
                        f.write("-" * 80 + "\n")
                        f.write(response.response_content)
                        f.write("\n" + "-" * 80 + "\n")


def process_files_parallel(
    config: ProcessingConfig,
    prompt_loader: PromptLoader,
    spec_files: list[str],
    llm_provider_factory: Callable[[], tuple[LLMProvider, str]] | None = None,
) -> list[ProcessingResult]:
    """Process files in parallel using ThreadPoolExecutor."""
    results = []
    completed_count = 0
    total_files = len(spec_files)

    print(
        f"Processing {total_files} files using {config.max_workers} parallel workers..."
    )
    print("")

    with ThreadPoolExecutor(max_workers=config.max_workers) as executor:
        # Submit all tasks
        future_to_file = {
            executor.submit(
                process_spec_file,
                config,
                prompt_loader,
                file_path,
                llm_provider_factory,
            ): file_path
            for file_path in spec_files
        }

        # Create progress bar
        passed_count = 0
        with tqdm(total=total_files, desc="Progress", unit="task") as pbar:
            # Process completed tasks as they finish
            for future in as_completed(future_to_file):
                file_path = future_to_file[future]
                completed_count += 1

                try:
                    result = future.result()
                    results.append(result)

                    # Update pass count
                    if result.success:
                        passed_count += 1
                    
                    # Update progress bar with current pass rate
                    pbar.set_postfix({
                        'Passed': f'{passed_count}/{completed_count}',
                        'Rate': f'{100*passed_count/completed_count:.1f}%'
                    })
                    pbar.update(1)

                    # Log to logger if verbose
                    if config.debug_mode:
                        status = "✓" if result.success else "✗"
                        logger.info(
                            f"[{completed_count}/{total_files}] {status} {Path(file_path).name}"
                        )

                except Exception as e:
                    # Handle unexpected exceptions
                    relative_path = get_relative_path_for_output(config, file_path)
                    error_result = ProcessingResult(
                        success=False,
                        file=str(relative_path),
                        error=f"Unexpected error: {str(e)}",
                        output=None,
                        has_bypass=False,
                        original_compilation_failed=False,  # Unknown since we didn't get that far
                        generate_prompt=None,
                        fix_prompts=None,
                    )
                    results.append(error_result)
                    
                    # Update progress bar
                    pbar.set_postfix({
                        'Passed': f'{passed_count}/{completed_count}',
                        'Rate': f'{100*passed_count/completed_count:.1f}%'
                    })
                    pbar.update(1)
                    
                    if config.debug_mode:
                        logger.info(
                            f"[{completed_count}/{total_files}] ✗ {Path(file_path).name} - Unexpected error: {str(e)}"
                        )

    # Create consolidated LLM responses table
    if wandb.run:
        all_llm_responses = []
        for result in results:
            if result.llm_responses:
                all_llm_responses.extend(result.llm_responses)

        if all_llm_responses:
            llm_responses_table = wandb.Table(
                columns=[
                    "file",
                    "response_type",
                    "iteration",
                    "prompt_hash",
                    "response_content",
                    "json_parsed_successfully",
                    "timestamp",
                ]
            )

            for response in all_llm_responses:
                llm_responses_table.add_data(
                    response.file,
                    response.response_type,
                    response.iteration,
                    response.prompt_hash,
                    response.response_content,
                    response.json_parsed_successfully,
                    response.timestamp,
                )

            wandb.log({"llm_responses": llm_responses_table})
            logger.info(
                f"  📊 Logged {len(all_llm_responses)} LLM responses to W&B table"
            )

    return results
