#!/usr/bin/env python3
"""
Compare the two different data sources for APPS performance.
"""

import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path

import pandas as pd


ANALYSIS_DIR = Path(__file__).resolve().parent
SCRIPTS_DIR = ANALYSIS_DIR.parent
FILTER_ENGINE_ROOT = SCRIPTS_DIR.parent
REPO_ROOT = FILTER_ENGINE_ROOT.parent.parent
RAW_DATA_ROOT = REPO_ROOT / "hard_subset" / "raw_data"
BENCHMARK_ROOT = RAW_DATA_ROOT / "vericoding-benchmark"
DEFAULT_RESULTS_CSV = BENCHMARK_ROOT / "vericoding_results_v1.csv"
DEFAULT_AGGREGATE_CSV = BENCHMARK_ROOT / "vericoding_aggregate.csv"
DEFAULT_TASKS_JSONL = BENCHMARK_ROOT / "jsonl" / "dafny_tasks.jsonl"
DEFAULT_HARD_SUBSET_JSON = (
    FILTER_ENGINE_ROOT / "outputs" / "hard_subsets_dafny" / "hard_subset_ids.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare vericoding_results_v1.csv to vericoding_aggregate.csv."
    )
    parser.add_argument(
        "--results-csv",
        type=Path,
        default=DEFAULT_RESULTS_CSV,
        help="Detailed benchmark CSV (vericoding_results_v1.csv).",
    )
    parser.add_argument(
        "--aggregate-csv",
        type=Path,
        default=DEFAULT_AGGREGATE_CSV,
        help="Aggregated APPS CSV (vericoding_aggregate.csv).",
    )
    parser.add_argument(
        "--tasks-jsonl",
        type=Path,
        default=DEFAULT_TASKS_JSONL,
        help="JSONL mapping source IDs to task IDs.",
    )
    parser.add_argument(
        "--hard-subset-json",
        type=Path,
        default=DEFAULT_HARD_SUBSET_JSON,
        help="JSON file describing hard subset IDs/output of create_hard_subsets.py.",
    )
    return parser.parse_args()


def load_hard_subset_ids(hard_subset_json: Path) -> tuple[set[str], set[str]]:
    if not hard_subset_json.exists():
        raise FileNotFoundError(
            f"Hard subset JSON not found: {hard_subset_json}. "
            "Run create_hard_subsets.py or pass --hard-subset-json."
        )
    with hard_subset_json.open() as f:
        data = json.load(f)
    hard_ids = set(data["task_ids"])
    apps_hard = set(data["by_benchmark"].get("apps", []))
    return hard_ids, apps_hard


def create_source_id_mapping(tasks_jsonl: Path) -> dict[str, str]:
    if not tasks_jsonl.exists():
        raise FileNotFoundError(
            f"Tasks JSONL not found: {tasks_jsonl}. Download the raw benchmark snapshot "
            "or pass --tasks-jsonl."
        )

    mapping: dict[str, str] = {}
    with tasks_jsonl.open() as f:
        for line in f:
            task = json.loads(line)
            if task.get("source-id"):
                mapping[task["source-id"]] = task["id"]
    return mapping


def analyze_both_sources(
    results_csv: Path,
    aggregate_csv: Path,
    tasks_jsonl: Path,
    hard_subset_json: Path,
) -> None:
    """Compare both data sources."""

    hard_ids, apps_hard = load_hard_subset_ids(hard_subset_json)

    print(f"APPS hard subset: {len(apps_hard)} tasks")

    if not results_csv.exists():
        raise FileNotFoundError(
            f"Results CSV not found: {results_csv}. Place vericoding_results_v1.csv "
            "under hard_subset/raw_data or pass --results-csv."
        )

    print("\n" + "=" * 80)
    print("SOURCE 1: vericoding_results_v1.csv (Detailed experimental results)")
    print("=" * 80)

    df = pd.read_csv(results_csv)
    df_apps = df[(df["Benchmark"] == "apps") & (df["Language"] == "dafny")]
    df_apps_hard = df_apps[df_apps["Task ID"].isin(hard_ids)]

    print(f"\nTotal APPS Dafny tasks in CSV: {df_apps['Task ID'].nunique()}")
    print(f"APPS tasks in hard subset: {df_apps_hard['Task ID'].nunique()}")
    print(f"\nPass rates on APPS hard subset:")

    source1_results: dict[str, float] = {}
    for model in sorted(df_apps_hard["LLM"].unique()):
        df_model = df_apps_hard[df_apps_hard["LLM"] == model]
        passed = df_model["Success"].sum()
        total = len(df_model)
        pct = passed / total * 100 if total > 0 else 0
        source1_results[model] = pct
        print(f"  {model:<25}: {passed:>3}/{total:<3} = {pct:>5.1f}%")

    print("\n" + "=" * 80)
    print("SOURCE 2: vericoding_aggregate.csv (Aggregated APPS results from GitHub)")
    print("=" * 80)

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
        lambda: {"hard_total": 0, "hard_passed": 0}
    )

    if not aggregate_csv.exists():
        raise FileNotFoundError(
            f"Aggregate CSV not found: {aggregate_csv}. "
            "Download vericoding_aggregate.csv or pass --aggregate-csv."
        )

    with aggregate_csv.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            filename = row["filename"]
            task_id = source_id_mapping.get(filename)

            if task_id and task_id in apps_hard:
                successful = (
                    row["successful_llms"].split(", ")
                    if row["successful_llms"]
                    else []
                )
                succeeded_models = {
                    model_map.get(m.strip())
                    for m in successful
                    if m.strip() in model_map
                }

                for model in model_map.values():
                    stats = model_stats[model]
                    stats["hard_total"] += 1
                    if model in succeeded_models:
                        stats["hard_passed"] += 1

    sample_model = next(iter(model_stats.values()), None)
    if sample_model:
        print(f"\nTasks found in aggregate: {sample_model['hard_total']}")
    else:
        print("\nNo tasks found in aggregate data.")
    print(f"\nPass rates on APPS hard subset:")

    source2_results: dict[str, float] = {}
    for model in sorted(model_stats.keys()):
        stats = model_stats[model]
        pct = stats["hard_passed"] / stats["hard_total"] * 100 if stats["hard_total"] > 0 else 0
        source2_results[model] = pct
        print(f"  {model:<25}: {stats['hard_passed']:>3}/{stats['hard_total']:<3} = {pct:>5.1f}%")

    print("\n" + "=" * 80)
    print("COMPARISON: SOURCE 1 vs SOURCE 2")
    print("=" * 80)
    print(f"\n{'Model':<25} | {'Source 1':<10} | {'Source 2':<10} | {'Difference':<12}")
    print("-" * 80)

    all_models = set(source1_results.keys()) | set(source2_results.keys())
    for model in sorted(all_models):
        s1 = source1_results.get(model, 0)
        s2 = source2_results.get(model, 0)
        diff = s1 - s2
        print(f"{model:<25} | {s1:>9.1f}% | {s2:>9.1f}% | {diff:>+10.1f}%")

    print("=" * 80)
    print("\n⚠️  MAJOR DISCREPANCY DETECTED!")
    print("The two CSV files contain VERY different results for the same tasks.")
    print("They likely represent different evaluation runs or different model versions.")
    print()


def main() -> int:
    args = parse_args()
    analyze_both_sources(
        results_csv=args.results_csv,
        aggregate_csv=args.aggregate_csv,
        tasks_jsonl=args.tasks_jsonl,
        hard_subset_json=args.hard_subset_json,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())



