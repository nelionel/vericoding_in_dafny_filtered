#!/usr/bin/env python3
"""
Create "hard subsets" - high-quality, challenging problems.
Filters for: faithfulness >= 2, leakage <= 1, difficulty >= 1
"""

import json
import argparse
from pathlib import Path
from collections import defaultdict


def load_results(results_file: Path):
    """Load quality check results."""
    results = []
    with open(results_file, 'r') as f:
        for line in f:
            try:
                result = json.loads(line)
                results.append(result)
            except json.JSONDecodeError:
                continue
    return results


def filter_hard_subset(results, min_faithfulness=2, max_leakage=1, min_difficulty=1):
    """Filter for high-quality, challenging problems."""
    
    filtered = []
    stats_by_benchmark = defaultdict(lambda: {
        'total': 0,
        'passed_faithfulness': 0,
        'passed_leakage': 0,
        'passed_difficulty': 0,
        'passed_all': 0
    })
    
    for result in results:
        source = result['source']
        stats = stats_by_benchmark[source]
        stats['total'] += 1
        
        faithfulness = result.get('spec_faithfulness', -999)
        leakage = result.get('spec_leakage', -999)
        difficulty = result.get('difficulty', -999)
        
        # Check each criterion
        passed_faith = faithfulness >= min_faithfulness
        passed_leak = leakage <= max_leakage
        passed_diff = difficulty >= min_difficulty
        
        if passed_faith:
            stats['passed_faithfulness'] += 1
        if passed_leak:
            stats['passed_leakage'] += 1
        if passed_diff:
            stats['passed_difficulty'] += 1
        
        # Check if all criteria passed
        if passed_faith and passed_leak and passed_diff:
            filtered.append(result)
            stats['passed_all'] += 1
    
    return filtered, stats_by_benchmark


def print_statistics(stats_by_benchmark, total_original, total_filtered):
    """Print filtering statistics."""
    
    print("\n" + "="*100)
    print("HARD SUBSET FILTERING STATISTICS")
    print("="*100)
    print(f"\nCriteria: faithfulness >= 2, leakage <= 1, difficulty >= 1\n")
    
    print(f"{'Benchmark':<20} | {'Total':<6} | {'Faith≥2':<8} | {'Leak≤1':<8} | {'Diff≥1':<8} | {'All 3':<8} | {'%':<6}")
    print("-"*100)
    
    # Sort by number passing all criteria
    sorted_benchmarks = sorted(
        stats_by_benchmark.items(),
        key=lambda x: x[1]['passed_all'],
        reverse=True
    )
    
    for benchmark, stats in sorted_benchmarks:
        total = stats['total']
        passed_all = stats['passed_all']
        percent = (passed_all / total * 100) if total > 0 else 0
        
        print(f"{benchmark:<20} | {total:<6} | {stats['passed_faithfulness']:<8} | "
              f"{stats['passed_leakage']:<8} | {stats['passed_difficulty']:<8} | "
              f"{passed_all:<8} | {percent:>5.1f}%")
    
    print("-"*100)
    print(f"{'TOTAL':<20} | {total_original:<6} | {'-':<8} | {'-':<8} | {'-':<8} | "
          f"{total_filtered:<8} | {total_filtered/total_original*100:>5.1f}%")
    print("="*100 + "\n")


def save_filtered_ids(filtered_results, output_file: Path):
    """Save filtered task IDs to a file."""
    
    with open(output_file, 'w') as f:
        json.dump({
            'criteria': {
                'min_faithfulness': 2,
                'max_leakage': 1,
                'min_difficulty': 1
            },
            'count': len(filtered_results),
            'task_ids': [r['id'] for r in filtered_results],
            'by_benchmark': {}
        }, f, indent=2)
    
    # Add by-benchmark breakdown
    with open(output_file, 'r') as f:
        data = json.load(f)
    
    by_benchmark = defaultdict(list)
    for result in filtered_results:
        by_benchmark[result['source']].append(result['id'])
    
    data['by_benchmark'] = {k: sorted(v) for k, v in sorted(by_benchmark.items())}
    
    with open(output_file, 'w') as f:
        json.dump(data, f, indent=2)
    
    print(f"✓ Saved filtered task IDs to: {output_file}")


def save_filtered_jsonl(filtered_results, output_file: Path):
    """Save filtered results as JSONL."""
    
    with open(output_file, 'w') as f:
        for result in filtered_results:
            f.write(json.dumps(result) + '\n')
    
    print(f"✓ Saved filtered results to: {output_file}")


def create_summary_markdown(stats_by_benchmark, total_original, total_filtered, output_file: Path):
    """Create a markdown summary of the hard subsets."""
    
    content = f"""# Hard Subsets - High-Quality Challenging Problems

## Filter Criteria

- **Spec Faithfulness**: ≥ 2 (faithful specs)
- **Spec Leakage**: ≤ 1 (low leakage - spec doesn't reveal implementation)
- **Difficulty**: ≥ 1 (non-trivial problems)

## Summary

**Total Original**: {total_original} tasks  
**Total Filtered**: {total_filtered} tasks ({total_filtered/total_original*100:.1f}%)

## By Benchmark

| Benchmark | Total Tasks | Passed All Criteria | Percentage |
|-----------|-------------|---------------------|------------|
"""
    
    sorted_benchmarks = sorted(
        stats_by_benchmark.items(),
        key=lambda x: x[1]['passed_all'],
        reverse=True
    )
    
    for benchmark, stats in sorted_benchmarks:
        total = stats['total']
        passed = stats['passed_all']
        percent = (passed / total * 100) if total > 0 else 0
        content += f"| {benchmark} | {total} | {passed} | {percent:.1f}% |\n"
    
    content += f"\n## Individual Criteria\n\n"
    content += "| Benchmark | Faith ≥ 2 | Leak ≤ 1 | Diff ≥ 1 |\n"
    content += "|-----------|-----------|----------|----------|\n"
    
    for benchmark, stats in sorted_benchmarks:
        content += (f"| {benchmark} | {stats['passed_faithfulness']} | "
                   f"{stats['passed_leakage']} | {stats['passed_difficulty']} |\n")
    
    content += f"""
## Interpretation

### What Makes These "Hard Subsets"?

1. **High Spec Faithfulness (≥2)**: The formal specifications faithfully capture the problem requirements. This ensures the verification task is meaningful.

2. **Low Spec Leakage (≤1)**: The specifications don't reveal the implementation details. Solving these requires actual algorithmic thinking, not just reading the spec.

3. **Non-Trivial Difficulty (≥1)**: The problems are at least "easy" difficulty, filtering out trivial tasks.

### Use Cases

- **Model Evaluation**: Use these subsets to evaluate models on challenging, well-specified verification tasks
- **Training Data**: High-quality problems for training verification models
- **Benchmark Refinement**: Focus on problems where formal verification adds real value

### Files Generated

- `hard_subset_ids.json`: Task IDs organized by benchmark
- `hard_subset_results.jsonl`: Full quality assessment data for filtered tasks
- `hard_subset_summary.md`: This file

### Example Usage

```bash
# Count tasks in hard subset by benchmark
jq '.by_benchmark | to_entries[] | "\\(.key): \\(.value | length)"' hard_subset_ids.json

# Get all hard subset task IDs
jq -r '.task_ids[]' hard_subset_ids.json

# Get hard subset for specific benchmark
jq -r '.by_benchmark.apps[]' hard_subset_ids.json
```
"""
    
    with open(output_file, 'w') as f:
        f.write(content)
    
    print(f"✓ Saved summary to: {output_file}")


def main():
    script_dir = Path(__file__).resolve().parent
    filter_engine_root = script_dir.parents[1]
    hard_subset_root = filter_engine_root.parent
    results_dir = filter_engine_root / "results"
    default_results = results_dir / "dafny_quality_results.jsonl"
    default_output = filter_engine_root / "outputs" / "hard_subsets_dafny"

    parser = argparse.ArgumentParser(description="Create hard subsets of benchmark")
    parser.add_argument(
        "--results-file",
        type=Path,
        default=default_results,
        help="Path to quality results JSONL file"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=default_output,
        help="Output directory for hard subsets"
    )
    parser.add_argument(
        "--min-faithfulness",
        type=int,
        default=2,
        help="Minimum spec faithfulness (default: 2)"
    )
    parser.add_argument(
        "--max-leakage",
        type=int,
        default=1,
        help="Maximum spec leakage (default: 1)"
    )
    parser.add_argument(
        "--min-difficulty",
        type=int,
        default=1,
        help="Minimum difficulty (default: 1)"
    )
    
    args = parser.parse_args()
    
    if not args.results_file.exists():
        print(f"Error: Results file not found: {args.results_file}")
        return 1
    
    # Load results
    print(f"Loading results from: {args.results_file}")
    results = load_results(args.results_file)
    print(f"  Loaded {len(results)} results")
    
    # Filter for hard subset
    print(f"\nFiltering for hard subset...")
    filtered, stats_by_benchmark = filter_hard_subset(
        results,
        min_faithfulness=args.min_faithfulness,
        max_leakage=args.max_leakage,
        min_difficulty=args.min_difficulty
    )
    print(f"  Filtered to {len(filtered)} tasks")
    
    # Print statistics
    print_statistics(stats_by_benchmark, len(results), len(filtered))
    
    # Create output directory
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    # Save filtered results
    save_filtered_ids(filtered, args.output_dir / "hard_subset_ids.json")
    save_filtered_jsonl(filtered, args.output_dir / "hard_subset_results.jsonl")
    create_summary_markdown(stats_by_benchmark, len(results), len(filtered),
                           args.output_dir / "hard_subset_summary.md")
    
    print(f"\n{'='*60}")
    print("Hard subset creation complete!")
    print(f"Output directory: {args.output_dir}")
    print(f"{'='*60}\n")
    
    return 0


if __name__ == "__main__":
    exit(main())




