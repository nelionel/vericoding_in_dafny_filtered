"""
Command-line interface for the clean Dafny hard-subset evaluator.

This script is intentionally lightweight but still reuses the proven vericoding
processing pipeline that we vendored into this repository.  It adds:

- `--eval-all` and `--eval-hardest` convenience presets
- multi-model orchestration
- backend selection (OpenRouter via hosted APIs or local vLLM server)
"""

from __future__ import annotations

import argparse
import json
import logging
import os
from pathlib import Path
from dotenv import load_dotenv

from vericoding.core import ProcessingConfig
from vericoding.core.prompts import PromptLoader
from vericoding.processing import ProcessingResult, process_files_parallel
from vericoding.utils import generate_summary, generate_csv_results
from vericoding.core.rate_limiter import (
    initialize_global_rate_limiter,
    get_global_rate_limiter,
)

from clean_eval.providers import create_provider_for_backend


PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_TASKS_DIR = PROJECT_ROOT / "hard_subset" / "dafny_flat"
DEFAULT_OUTPUT_DIR = PROJECT_ROOT / "eval_results"


def load_hard_subset_metadata(hard_subset_dir: Path) -> dict[str, dict]:
    metadata_path = hard_subset_dir / "metadata.json"
    if not metadata_path.exists():
        raise FileNotFoundError(f"metadata.json not found at {metadata_path}")
    with metadata_path.open() as f:
        return json.load(f)


def select_tasks(
    metadata: dict[str, dict],
    files_dir: Path,
    args: argparse.Namespace,
) -> list[Path]:
    """Select spec files using filtering flags."""
    selected: list[str] = []

    items = list(metadata.items())

    if args.eval_hardest:
        hardest = [
            (fname, data)
            for fname, data in items
            if data.get("difficulty", 0) >= 3 or data.get("models_passed", 99) <= 1
        ]
        hardest = sorted(
            hardest,
            key=lambda item: (
                -item[1].get("difficulty", 0),
                item[1].get("models_passed", 99),
            ),
        )
        hardest = hardest[: args.hardest_count]
        selected = [fname for fname, _ in hardest]
    else:
        selected = [fname for fname, _ in items]

    if args.sources:
        selected = [
            fname
            for fname in selected
            if metadata[fname].get("source") in args.sources
        ]

    if args.min_difficulty is not None:
        selected = [
            fname
            for fname in selected
            if metadata[fname].get("difficulty", 0) >= args.min_difficulty
        ]

    if args.max_difficulty is not None:
        selected = [
            fname
            for fname in selected
            if metadata[fname].get("difficulty", 0) <= args.max_difficulty
        ]

    if args.min_models_passed is not None:
        selected = [
            fname
            for fname in selected
            if metadata[fname].get("models_passed", 0) >= args.min_models_passed
        ]

    if args.max_models_passed is not None:
        selected = [
            fname
            for fname in selected
            if metadata[fname].get("models_passed", 0) <= args.max_models_passed
        ]

    if args.eval_all:
        limit = None
    else:
        limit = args.limit

    if limit:
        selected = selected[:limit]

    return [files_dir / fname for fname in selected]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Clean Dafny hard subset evaluator",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    # Model + backend
    parser.add_argument(
        "--models",
        nargs="+",
        default=["claude-haiku", "qwen3-30b-thinking"],
        help="List of logical model aliases defined in providers.py",
    )
    parser.add_argument(
        "--backend",
        choices=["openrouter", "vllm"],
        default="openrouter",
        help="LLM backend to use",
    )
    parser.add_argument(
        "--vllm-base-url",
        default=os.getenv("VLLM_BASE_URL", "http://localhost:8000/v1"),
        help="Base URL for the local vLLM OpenAI-compatible server",
    )
    parser.add_argument(
        "--vllm-api-key",
        default=os.getenv("VLLM_API_KEY", "dummy"),
        help="API key forwarded to the local vLLM server (if required)",
    )
    parser.add_argument(
        "--vllm-max-tokens",
        type=int,
        default=int(os.getenv("VLLM_MAX_TOKENS", "4000")),
        help="Maximum completion tokens to request from the vLLM backend",
    )
    parser.add_argument(
        "--vllm-request-timeout",
        type=float,
        default=float(os.getenv("VLLM_REQUEST_TIMEOUT", "300")),
        help="Timeout (seconds) for each vLLM completion request",
    )
    parser.add_argument(
        "--wandb-mode",
        choices=["online", "offline", "disabled"],
        default=os.getenv("WANDB_MODE", "disabled"),
        help="Control Weights & Biases logging",
    )

    # Subset controls
    parser.add_argument(
        "--tasks-dir",
        type=Path,
        default=DEFAULT_TASKS_DIR,
        help="Directory that contains metadata.json and files/",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=20,
        help="Maximum number of tasks to run (ignored if --eval-all)",
    )
    parser.add_argument(
        "--eval-all",
        action="store_true",
        help="Ignore --limit and run the entire metadata list",
    )
    parser.add_argument(
        "--eval-hardest",
        action="store_true",
        help="Focus on the hardest tasks (difficulty>=3 or unsolved)",
    )
    parser.add_argument(
        "--hardest-count",
        type=int,
        default=200,
        help="Maximum number of tasks considered when --eval-hardest is used",
    )
    parser.add_argument("--sources", nargs="+", help="Filter by source tags")
    parser.add_argument(
        "--min-difficulty", type=int, choices=[0, 1, 2, 3], help="Minimum difficulty"
    )
    parser.add_argument(
        "--max-difficulty", type=int, choices=[0, 1, 2, 3], help="Maximum difficulty"
    )
    parser.add_argument(
        "--min-models-passed",
        type=int,
        help="Minimum number of historical model passes required",
    )
    parser.add_argument(
        "--max-models-passed",
        type=int,
        help="Maximum number of historical model passes allowed",
    )

    # Processing runtime config
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Directory to store evaluation artifacts",
    )
    parser.add_argument(
        "--parallel-workers",
        type=int,
        default=int(os.getenv("PARALLEL_WORKERS", "4")),
        help="Worker count when not using the async rate limiter",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=int(os.getenv("MAX_ITERATIONS", "5")),
        help="Maximum retry iterations per task",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=int(os.getenv("VERIFICATION_TIMEOUT", "60")),
        help="Verification timeout in seconds",
    )
    parser.add_argument(
        "--use-dynamic-rate-limit",
        action="store_true",
        default=os.getenv("USE_DYNAMIC_RATE_LIMIT", "true").lower()
        in ("1", "true", "yes"),
        help="Use the built-in async rate limiter",
    )
    parser.add_argument(
        "--rate-limit-rpm",
        type=int,
        default=int(os.getenv("RATE_LIMIT_RPM", "200")),
        help="Requests per minute budget for the async limiter",
    )
    parser.add_argument(
        "--max-concurrent-tasks",
        type=int,
        default=int(os.getenv("MAX_CONCURRENT_TASKS", "20")),
        help="Maximum concurrent tasks when using the async limiter",
    )

    # UX
    parser.add_argument("--dry-run", action="store_true", help="List tasks and exit")
    parser.add_argument("--verbose", action="store_true", help="Verbose logging")

    return parser.parse_args()


def configure_logging(verbose: bool) -> None:
    if verbose:
        logging.basicConfig(level=logging.INFO, format="%(message)s")
    else:
        logging.basicConfig(level=logging.ERROR)
        logging.getLogger("vericoding").setLevel(logging.ERROR)
        logging.getLogger("httpx").setLevel(logging.ERROR)
        logging.getLogger("httpcore").setLevel(logging.ERROR)
        logging.getLogger("openai").setLevel(logging.ERROR)


def ensure_env_loaded() -> None:
    load_dotenv()
    load_dotenv(".env.local")


def get_output_subdir(base_dir: Path, model_alias: str) -> Path:
    """Return a unique output directory path for the given model."""
    candidate = base_dir / model_alias
    if not candidate.exists():
        return candidate
    suffix = 1
    while True:
        candidate = base_dir / f"{model_alias}_{suffix}"
        if not candidate.exists():
            return candidate
        suffix += 1


def build_processing_config(
    language: str,
    language_config: LanguageConfig,
    files_dir: Path,
    args: argparse.Namespace,
    output_dir: Path,
    model_name: str,
) -> ProcessingConfig:
    effective_workers = (
        args.max_concurrent_tasks if args.use_dynamic_rate_limit else args.parallel_workers
    )
    return ProcessingConfig(
        language=language,
        language_config=language_config,
        files_dir=str(files_dir),
        max_iterations=args.max_iterations,
        output_dir=str(output_dir),
        summary_file=str(output_dir / "summary.txt"),
        debug_mode=args.verbose,
        max_workers=effective_workers,
        api_rate_limit_delay=0,
        llm=model_name,
        use_dynamic_rate_limit=args.use_dynamic_rate_limit,
        rate_limit_requests_per_minute=args.rate_limit_rpm,
    )


def run_for_model(
    args: argparse.Namespace,
    model_alias: str,
    files: list[Path],
    metadata: dict[str, dict],
) -> tuple[list[ProcessingResult], Path]:
    language_configs = ProcessingConfig.get_available_languages()
    dafny_config = language_configs["dafny"]

    model_output_dir = get_output_subdir(args.output_dir, model_alias)
    model_output_dir.mkdir(parents=True, exist_ok=True)

    processing_config = build_processing_config(
        language="dafny",
        language_config=dafny_config,
        files_dir=args.tasks_dir / "files",
        args=args,
        output_dir=model_output_dir,
        model_name=model_alias,
    )

    if args.use_dynamic_rate_limit:
        initialize_global_rate_limiter(
            requests_per_minute=args.rate_limit_rpm,
            window_seconds=60,
            safety_margin=0.95,
        )

    prompt_loader = PromptLoader(processing_config.language)
    resolved_model_name, provider_factory = create_provider_for_backend(
        backend=args.backend,
        llm_name=model_alias,
        vllm_base_url=args.vllm_base_url,
        vllm_api_key=args.vllm_api_key,
        vllm_max_tokens=args.vllm_max_tokens,
        vllm_request_timeout=args.vllm_request_timeout,
    )

    if args.verbose:
        print(
            f"\n=== {model_alias} → {resolved_model_name} | {len(files)} tasks | backend={args.backend} ==="
        )
    else:
        print(
            f"\n🚀 Evaluating {len(files)} tasks with {model_alias} ({args.backend})"
        )

    results = process_files_parallel(
        config=processing_config,
        prompt_loader=prompt_loader,
        spec_files=[str(p) for p in files],
        llm_provider_factory=provider_factory,
    )

    summary = generate_summary(processing_config, results)
    csv_path = generate_csv_results(processing_config, results)

    success_count = sum(1 for r in results if r.success)
    if not args.verbose:
        rate = (success_count / len(results) * 100) if results else 0
        print(f"✅ Complete: {success_count}/{len(results)} passed ({rate:.1f}%)")
        print(f"📁 Results: {model_output_dir}")
    else:
        print(summary)
        print(csv_path)

    if args.use_dynamic_rate_limit:
        limiter = get_global_rate_limiter()
        stats = limiter.get_stats()
        if args.verbose or not args.verbose:
            print(
                f"⚡ Rate limiter: {stats['total_requests']} requests, "
                f"{stats['utilization']*100:.1f}% utilization"
            )

    return results, model_output_dir

def main() -> None:
    ensure_env_loaded()
    args = parse_args()
    configure_logging(args.verbose)
    os.environ["WANDB_MODE"] = args.wandb_mode

    if args.eval_all and args.eval_hardest:
        raise SystemExit("--eval-all and --eval-hardest cannot be used together")

    metadata = load_hard_subset_metadata(args.tasks_dir)
    files = select_tasks(metadata, args.tasks_dir / "files", args)

    if args.dry_run:
        print(f"Model aliases: {args.models}")
        print(f"Backend: {args.backend}")
        print(f"Tasks selected: {len(files)}")
        for path in files[:10]:
            fname = path.name
            meta = metadata.get(fname, {})
            print(
                f" - {fname} (difficulty={meta.get('difficulty')}, "
                f"models_passed={meta.get('models_passed')}, source={meta.get('source')})"
            )
        if len(files) > 10:
            print(f" ... plus {len(files) - 10} more")
        return

    args.output_dir.mkdir(parents=True, exist_ok=True)

    for model_alias in args.models:
        run_for_model(args, model_alias, files, metadata)


if __name__ == "__main__":
    main()

