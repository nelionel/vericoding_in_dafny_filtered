#!/usr/bin/env python3
"""
Compare performance on hard subset vs non-hard subset.
"""

import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path


ANALYSIS_DIR = Path(__file__).resolve().parent
SCRIPTS_DIR = ANALYSIS_DIR.parent
FILTER_ENGINE_ROOT = SCRIPTS_DIR.parent
REPO_ROOT = FILTER_ENGINE_ROOT.parent.parent
RAW_DATA_ROOT = REPO_ROOT / "hard_subset" / "raw_data"
BENCHMARK_ROOT = RAW_DATA_ROOT / "vericoding-benchmark"
DEFAULT_TASKS_JSONL = BENCHMARK_ROOT / "jsonl" / "dafny_tasks.jsonl"
DEFAULT_HARD_SUBSET_IDS = (
    FILTER_ENGINE_ROOT / "outputs" / "hard_subsets_dafny" / "hard_subset_ids.json"
)
DEFAULT_AGGREGATE_CSV = BENCHMARK_ROOT / "vericoding_aggregate.csv"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare performance on APPS hard vs non-hard subsets."
    )
    parser.add_argument(
        "--aggregate-csv",
        type=Path,
        default=DEFAULT_AGGREGATE_CSV,
        help="Aggregated CSV exported from GitHub (vericoding_aggregate.csv).",
    )
    parser.add_argument(
        "--hard-subset-json",
        type=Path,
        default=DEFAULT_HARD_SUBSET_IDS,
        help="JSON file listing hard subset task IDs (output of create_hard_subsets.py).",
    )
    parser.add_argument(
        "--tasks-jsonl",
        type=Path,
        default=DEFAULT_TASKS_JSONL,
        help="dafny_tasks.jsonl mapping source IDs to task IDs.",
    )
    return parser.parse_args()


def create_source_id_mapping(tasks_jsonl: Path) -> dict[str, str]:
    """Create mapping from source-id to task ID."""
    mapping: dict[str, str] = {}
    with tasks_jsonl.open() as f:
        for line in f:
            task = json.loads(line)
            if task.get("source-id"):
                mapping[task["source-id"]] = task["id"]
    return mapping


def analyze_aggregate_csv(
    aggregate_csv: Path, hard_subset_json: Path, tasks_jsonl: Path
) -> dict[str, dict[str, int]]:
    """Analyze vericoding_aggregate.csv for hard vs non-hard subset."""

    if not hard_subset_json.exists():
        raise FileNotFoundError(
            f"Hard subset JSON not found: {hard_subset_json}. "
            "Run the filtering pipeline or pass --hard-subset-json."
        )

    if not aggregate_csv.exists():
        raise FileNotFoundError(
            f"Aggregate CSV not found: {aggregate_csv}. "
            "Download vericoding_aggregate.csv and place it relative to this repo "
            "or provide --aggregate-csv."
        )

    with hard_subset_json.open() as f:
        data = json.load(f)
        hard_subset_ids = set(data["task_ids"])
        apps_hard_ids = set(data["by_benchmark"].get("apps", []))

    print(f"Total hard subset: {len(hard_subset_ids)}")
    print(f"APPS hard subset: {len(apps_hard_ids)}")

    source_id_mapping = create_source_id_mapping(tasks_jsonl)

    model_map = {
        "claude-opus": "claude-opus-4.1",
        "claude-sonnet": "claude-sonnet-4",
        "gpt": "gpt-5",
        "gpt-mini": "gpt-5-mini",
        "gemini": "gemini-2.5-pro",
        "gemini-flash": "gemini-2.5-flash",
        "glm": "glm-4.5",
        "grok-code": "grok-code",
        "deepseek": "deepseek-chat-v3.1",
    }

    model_stats: dict[str, dict[str, int]] = defaultdict(
        lambda: {
            "all_total": 0,
            "all_passed": 0,
            "hard_total": 0,
            "hard_passed": 0,
            "nonhard_total": 0,
            "nonhard_passed": 0,
        }
    )

    with aggregate_csv.open() as f:
        reader = csv.DictReader(f)

        for row in reader:
            filename = row["filename"]
            task_id = source_id_mapping.get(filename)

            if task_id is None:
                continue

            successful = (
                row["successful_llms"].split(", ") if row["successful_llms"] else []
            )
            succeeded_models = {
                model_map.get(m.strip())
                for m in successful
                if m.strip() in model_map
            }

            in_hard = task_id in apps_hard_ids

            for model in model_map.values():
                stats = model_stats[model]
                stats["all_total"] += 1
                if model in succeeded_models:
                    stats["all_passed"] += 1

                if in_hard:
                    stats["hard_total"] += 1
                    if model in succeeded_models:
                        stats["hard_passed"] += 1
                else:
                    stats["nonhard_total"] += 1
                    if model in succeeded_models:
                        stats["nonhard_passed"] += 1

    return model_stats


def print_results(model_stats):
    """Print comprehensive results."""
    
    print("\n" + "="*140)
    print("MODEL PERFORMANCE: ALL APPS vs HARD SUBSET vs NON-HARD SUBSET")
    print("="*140)
    print(f"\n{'Model':<25} | {'All APPS':<18} | {'Hard Subset':<18} | {'Non-Hard':<18} | {'Hard-All':<10} | {'NonH-All':<10}")
    print("-"*140)
    
    # Sort by hard subset pass rate
    sorted_models = sorted(
        model_stats.items(),
        key=lambda x: (x[1]['hard_passed'] / x[1]['hard_total'] if x[1]['hard_total'] > 0 else 0),
        reverse=True
    )
    
    for model, stats in sorted_models:
        if stats['all_total'] == 0:
            continue
        
        # All APPS
        all_pct = (stats['all_passed'] / stats['all_total'] * 100) if stats['all_total'] > 0 else 0
        all_str = f"{stats['all_passed']}/{stats['all_total']} ({all_pct:.1f}%)"
        
        # Hard subset
        hard_pct = (stats['hard_passed'] / stats['hard_total'] * 100) if stats['hard_total'] > 0 else 0
        hard_str = f"{stats['hard_passed']}/{stats['hard_total']} ({hard_pct:.1f}%)"
        
        # Non-hard
        nonhard_pct = (stats['nonhard_passed'] / stats['nonhard_total'] * 100) if stats['nonhard_total'] > 0 else 0
        nonhard_str = f"{stats['nonhard_passed']}/{stats['nonhard_total']} ({nonhard_pct:.1f}%)"
        
        # Differences
        diff_hard = hard_pct - all_pct
        diff_nonhard = nonhard_pct - all_pct
        
        print(f"{model:<25} | {all_str:<18} | {hard_str:<18} | {nonhard_str:<18} | {diff_hard:>+8.1f}% | {diff_nonhard:>+8.1f}%")
    
    print("="*140)
    
    # Summary
    print("\nSummary:")
    avg_all = sum((s['all_passed'] / s['all_total'] * 100) for s in model_stats.values() if s['all_total'] > 0) / len([s for s in model_stats.values() if s['all_total'] > 0])
    avg_hard = sum((s['hard_passed'] / s['hard_total'] * 100) for s in model_stats.values() if s['hard_total'] > 0) / len([s for s in model_stats.values() if s['hard_total'] > 0])
    avg_nonhard = sum((s['nonhard_passed'] / s['nonhard_total'] * 100) for s in model_stats.values() if s['nonhard_total'] > 0) / len([s for s in model_stats.values() if s['nonhard_total'] > 0])
    
    print(f"  Average pass rate (all APPS):     {avg_all:.1f}%")
    print(f"  Average pass rate (hard subset):  {avg_hard:.1f}%")
    print(f"  Average pass rate (non-hard):     {avg_nonhard:.1f}%")
    print(f"  Hard - All:                        {avg_hard - avg_all:+.1f}%")
    print(f"  Non-Hard - All:                    {avg_nonhard - avg_all:+.1f}%")
    
    # Breakdown
    sample_model = list(model_stats.values())[0]
    print(f"\n  Total APPS tasks:      {sample_model['all_total']}")
    print(f"  Hard subset tasks:     {sample_model['hard_total']} ({sample_model['hard_total']/sample_model['all_total']*100:.1f}%)")
    print(f"  Non-hard tasks:        {sample_model['nonhard_total']} ({sample_model['nonhard_total']/sample_model['all_total']*100:.1f}%)")
    print()


def main() -> int:
    args = parse_args()
    print(f"Analyzing aggregate CSV at: {args.aggregate_csv}")
    model_stats = analyze_aggregate_csv(
        aggregate_csv=args.aggregate_csv,
        hard_subset_json=args.hard_subset_json,
        tasks_jsonl=args.tasks_jsonl,
    )
    print_results(model_stats)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())



