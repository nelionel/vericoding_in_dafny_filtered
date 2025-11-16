#!/usr/bin/env python3
"""
Quality check pipeline for vericoding benchmark using Claude 4.5 Sonnet via OpenRouter.
Evaluates each problem on spec-faithfulness and difficulty.
"""

import json
import os
import time
from pathlib import Path
from typing import Dict, List, Optional
import argparse
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
try:
    import requests
except ImportError:
    print("Error: requests library not found. Install with: pip install requests")
    sys.exit(1)


SCRIPT_DIR = Path(__file__).resolve().parent
FILTER_ENGINE_ROOT = SCRIPT_DIR.parents[1]
HARD_SUBSET_ROOT = FILTER_ENGINE_ROOT.parent
RAW_DATA_DIR = HARD_SUBSET_ROOT / "raw_data"
DEFAULT_BENCHMARK_DIR = RAW_DATA_DIR / "vericoding-benchmark"
DEFAULT_OUTPUT_DIR = FILTER_ENGINE_ROOT / "results"


# Language-specific system prompts
SYSTEM_PROMPTS = {
    "dafny": """You are an expert in formal verification and Dafny. You will evaluate verification tasks.

**Task Format**: Models receive a problem description, helper functions, and a method signature with formal specifications (requires/ensures). They must implement the method body to satisfy the specifications.

**Your Role**: Assess three independent properties of each task.

Rate each task on THREE axes:

1. **spec_faithfulness** (0-3): How well do the formal specifications capture what the description asks for?
   - 0: Spec completely misses description intent (e.g., "ensures result >= 0" when description asks for maximum)
   - 1: Spec captures some requirements but misses key ones from description
   - 2: Spec captures most requirements, minor gaps
   - 3: Spec faithfully and completely captures description requirements

2. **spec_leakage** (0-3): How much does the spec reveal the implementation steps?
   - 0: No leakage - spec only states WHAT, not HOW (e.g., "prove infinitely many primes")
   - 1: Minor leakage - spec hints at approach but leaves implementation open
   - 2: Significant leakage - spec suggests specific implementation structure
   - 3: Complete leakage - spec dictates implementation (e.g., "for each int 0-9, return English name" is just a lookup table)

3. **difficulty** (0-3): Inherent difficulty of the problem (ignore spec quality):
   - 0: Trivial (return constant, basic arithmetic)
   - 1: Easy (simple algorithms, basic loops)
   - 2: Moderate (algorithmic thinking, non-trivial invariants)
   - 3: Hard (complex algorithms, deep reasoning, sophisticated proofs)

**Key Distinction**: Faithfulness asks "does spec match description?" while leakage asks "does spec reveal how to implement?"

Respond ONLY with valid JSON:
{"spec_faithfulness": <0-3>, "spec_leakage": <0-3>, "difficulty": <0-3>, "explanation": "<1-2 sentences explaining your ratings>"}""",

    "lean": """You are an expert in formal verification and Lean 4. You will evaluate verification tasks.

**Task Format**: Models receive a problem description, helper functions/definitions, and a function signature with a theorem specifying postconditions. They must implement the function and prove the theorem (replacing `sorry`).

**Your Role**: Assess three independent properties of each task.

Rate each task on THREE axes:

1. **spec_faithfulness** (0-3): How well do the formal postconditions capture what the description asks for?
   - 0: Spec completely misses description intent
   - 1: Spec captures some requirements but misses key ones from description
   - 2: Spec captures most requirements, minor gaps
   - 3: Spec faithfully and completely captures description requirements

2. **spec_leakage** (0-3): How much does the spec reveal the proof/implementation steps?
   - 0: No leakage - spec only states WHAT, not HOW (e.g., "prove infinitely many primes")
   - 1: Minor leakage - spec hints at approach but leaves proof open
   - 2: Significant leakage - spec suggests specific proof structure
   - 3: Complete leakage - spec dictates implementation steps

3. **difficulty** (0-3): Inherent difficulty of the problem (ignore spec quality):
   - 0: Trivial (return constant, basic arithmetic)
   - 1: Easy (simple algorithms, basic proofs)
   - 2: Moderate (algorithmic thinking, non-trivial proofs)
   - 3: Hard (complex algorithms, deep reasoning, intricate proofs)

**Key Distinction**: Faithfulness asks "does spec match description?" while leakage asks "does spec reveal how to implement?"

Respond ONLY with valid JSON:
{"spec_faithfulness": <0-3>, "spec_leakage": <0-3>, "difficulty": <0-3>, "explanation": "<1-2 sentences explaining your ratings>"}""",

    "verus": """You are an expert in formal verification and Verus (Rust verification). You will evaluate verification tasks.

**Task Format**: Models receive a problem description, helper spec functions, and a function signature with formal specifications (requires/ensures). They must implement the function body to satisfy the specifications.

**Your Role**: Assess three independent properties of each task.

Rate each task on THREE axes:

1. **spec_faithfulness** (0-3): How well do the formal specifications capture what the description asks for?
   - 0: Spec completely misses description intent
   - 1: Spec captures some requirements but misses key ones from description
   - 2: Spec captures most requirements, minor gaps
   - 3: Spec faithfully and completely captures description requirements

2. **spec_leakage** (0-3): How much does the spec reveal the implementation steps?
   - 0: No leakage - spec only states WHAT, not HOW (e.g., "prove infinitely many primes")
   - 1: Minor leakage - spec hints at approach but leaves implementation open
   - 2: Significant leakage - spec suggests specific implementation structure
   - 3: Complete leakage - spec dictates implementation steps

3. **difficulty** (0-3): Inherent difficulty of the problem (ignore spec quality):
   - 0: Trivial (return constant, basic arithmetic)
   - 1: Easy (simple algorithms, straightforward logic)
   - 2: Moderate (algorithmic thinking, non-trivial invariants)
   - 3: Hard (complex algorithms, deep reasoning, intricate verification)

**Key Distinction**: Faithfulness asks "does spec match description?" while leakage asks "does spec reveal how to implement?"

Respond ONLY with valid JSON:
{"spec_faithfulness": <0-3>, "spec_leakage": <0-3>, "difficulty": <0-3>, "explanation": "<1-2 sentences explaining your ratings>"}"""
}


def create_user_prompt(task: Dict) -> str:
    """Create the user prompt from a task."""
    parts = []
    
    if task.get("vc-description"):
        parts.append(f"# Problem Description\n{task['vc-description']}")
    
    if task.get("vc-preamble"):
        parts.append(f"\n# Preamble (definitions, helpers)\n{task['vc-preamble']}")
    
    if task.get("vc-spec"):
        parts.append(f"\n# Specification\n{task['vc-spec']}")
    
    if task.get("vc-helpers"):
        parts.append(f"\n# Additional Helpers\n{task['vc-helpers']}")
    
    if not parts:
        # Fallback if no structured fields
        parts.append(f"# Task ID: {task.get('id', 'unknown')}\n# Source: {task.get('source', 'unknown')}")
    
    return "\n".join(parts)


def call_openrouter_api(
    system_prompt: str,
    user_prompt: str,
    api_key: str,
    model: str = "anthropic/claude-sonnet-4.5",
    max_retries: int = 3,
    timeout: int = 180
) -> Optional[Dict]:
    """Call OpenRouter API with retry logic.
    
    Uses Claude Sonnet 4.5 with extended thinking EXPLICITLY enabled for best
    quality evaluations, especially when generating structured JSON output.
    """
    
    url = "https://openrouter.ai/api/v1/chat/completions"
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
        "HTTP-Referer": "https://github.com/vericoding-benchmark",
        "X-Title": "Vericoding Benchmark Quality Check"
    }
    
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt}
        ],
        "temperature": 0.0,
        "max_tokens": 4000,  # Increased for thinking + response
        # EXPLICITLY enable extended thinking
        "thinking": {
            "type": "enabled",
            "budget_tokens": 10000
        }
    }
    
    for attempt in range(max_retries):
        try:
            response = requests.post(url, headers=headers, json=payload, timeout=timeout)
            response.raise_for_status()
            
            result = response.json()
            content = result["choices"][0]["message"]["content"]
            
            # Parse JSON from response
            # Handle potential markdown code blocks
            content = content.strip()
            if content.startswith("```"):
                lines = content.split("\n")
                content = "\n".join(lines[1:-1] if lines[-1].strip() == "```" else lines[1:])
            
            return json.loads(content)
            
        except requests.exceptions.RequestException as e:
            print(f"  API request failed (attempt {attempt + 1}/{max_retries}): {e}")
            if attempt < max_retries - 1:
                time.sleep(2 ** attempt)  # Exponential backoff
            else:
                return None
        except (json.JSONDecodeError, KeyError) as e:
            print(f"  Failed to parse response (attempt {attempt + 1}/{max_retries}): {e}")
            if attempt < max_retries - 1:
                time.sleep(1)
            else:
                return None
    
    return None


def process_task(task: Dict, api_key: str, language: str, model: str = "anthropic/claude-sonnet-4.5") -> Dict:
    """Process a single task and return quality assessment."""
    
    system_prompt = SYSTEM_PROMPTS.get(language, SYSTEM_PROMPTS["dafny"])
    user_prompt = create_user_prompt(task)
    
    result = call_openrouter_api(system_prompt, user_prompt, api_key, model=model)
    
    if result is None:
        return {
            "id": task["id"],
            "language": language,
            "source": task.get("source", "unknown"),
            "spec_faithfulness": -1,
            "spec_leakage": -1,
            "difficulty": -1,
            "explanation": "API call failed",
            "error": True
        }
    
    return {
        "id": task["id"],
        "language": language,
        "source": task.get("source", "unknown"),
        "spec_faithfulness": result.get("spec_faithfulness", -1),
        "spec_leakage": result.get("spec_leakage", -1),
        "difficulty": result.get("difficulty", -1),
        "explanation": result.get("explanation", ""),
        "error": False
    }


def load_completed_ids(output_file: Path) -> set:
    """Load IDs of already processed tasks from output file."""
    if not output_file.exists():
        return set()
    
    completed = set()
    with open(output_file, 'r') as f:
        for line in f:
            try:
                entry = json.loads(line)
                completed.add(entry["id"])
            except json.JSONDecodeError:
                continue
    
    return completed


def main():
    parser = argparse.ArgumentParser(description="Quality check vericoding benchmark")
    parser.add_argument(
        "--benchmark-dir",
        type=Path,
        default=DEFAULT_BENCHMARK_DIR,
        help="Path to vericoding-benchmark directory"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Directory to save quality check results"
    )
    parser.add_argument(
        "--api-key",
        type=str,
        default=None,
        help="OpenRouter API key (default: read from OPENROUTER_API_KEY env var)"
    )
    parser.add_argument(
        "--languages",
        nargs="+",
        choices=["dafny", "lean", "verus"],
        default=["dafny"],
        help="Languages to process (default: dafny only)"
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Limit number of tasks per language (for testing)"
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Resume from previous run (skip already processed tasks)"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=10,
        help="Number of parallel workers (default: 10)"
    )
    parser.add_argument(
        "--model",
        type=str,
        default="anthropic/claude-sonnet-4.5",
        help="Model to use via OpenRouter (default: claude-sonnet-4.5 with thinking ENABLED)"
    )
    
    args = parser.parse_args()
    
    # Get API key
    api_key = args.api_key or os.environ.get("OPENROUTER_API_KEY")
    if not api_key:
        print("Error: OpenRouter API key not provided. Set OPENROUTER_API_KEY env var or use --api-key")
        sys.exit(1)
    
    # Create output directory
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"\n{'='*60}")
    print(f"Model: {args.model}")
    print(f"Workers: {args.workers}")
    if "sonnet-4.5" in args.model or "claude-sonnet-4" in args.model:
        print("⚡ Extended thinking EXPLICITLY ENABLED")
        print("   (10,000 token thinking budget)")
    print(f"{'='*60}\n")
    
    # Process each language
    for language in args.languages:
        print(f"\n{'='*60}")
        print(f"Processing {language.upper()} tasks")
        print(f"{'='*60}")
        
        input_file = args.benchmark_dir / "jsonl" / f"{language}_tasks.jsonl"
        output_file = args.output_dir / f"{language}_quality_results.jsonl"
        
        if not input_file.exists():
            print(f"Warning: Input file not found: {input_file}")
            continue
        
        # Load completed tasks if resuming
        completed_ids = load_completed_ids(output_file) if args.resume else set()
        if completed_ids:
            print(f"Resuming: {len(completed_ids)} tasks already completed")
        
        # Load tasks
        tasks = []
        with open(input_file, 'r') as f:
            for line in f:
                task = json.loads(line)
                if not args.resume or task["id"] not in completed_ids:
                    tasks.append(task)
        
        if args.limit:
            tasks = tasks[:args.limit]
        
        print(f"Processing {len(tasks)} tasks with {args.workers} workers...")
        
        # Process tasks in parallel
        write_lock = Lock()
        completed_count = 0
        error_count = 0
        
        with open(output_file, 'a' if args.resume else 'w') as f:
            with ThreadPoolExecutor(max_workers=args.workers) as executor:
                # Submit all tasks
                future_to_task = {
                    executor.submit(process_task, task, api_key, language, args.model): task
                    for task in tasks
                }
                
                # Process completed tasks as they finish
                for future in as_completed(future_to_task):
                    task = future_to_task[future]
                    try:
                        result = future.result()
                        
                        # Write result with lock (thread-safe)
                        with write_lock:
                            f.write(json.dumps(result) + "\n")
                            f.flush()
                            
                            completed_count += 1
                            if result["error"]:
                                error_count += 1
                                print(f"[{completed_count}/{len(tasks)}] {result['id']}: ERROR")
                            else:
                                print(f"[{completed_count}/{len(tasks)}] {result['id']}: ✓ (faith: {result['spec_faithfulness']}, leak: {result['spec_leakage']}, diff: {result['difficulty']})")
                    
                    except Exception as e:
                        with write_lock:
                            print(f"[{completed_count}/{len(tasks)}] {task['id']}: EXCEPTION - {e}")
                            error_count += 1
        
        print(f"\nCompleted {language}! Successful: {completed_count - error_count}, Errors: {error_count}")
        print(f"Results saved to {output_file}")
    
    print(f"\n{'='*60}")
    print("All quality checks complete!")
    print(f"Results saved to: {args.output_dir}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()

