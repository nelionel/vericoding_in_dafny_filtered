#!/usr/bin/env python3
"""
Analyze model performance on the hard subset vs overall benchmark.
"""

import json
import pandas as pd
import argparse
from pathlib import Path
from collections import defaultdict
import os

SCRIPT_DIR = Path(__file__).resolve().parent
os.chdir(SCRIPT_DIR.parent)


def load_hard_subset_ids(ids_file: Path):
    """Load hard subset task IDs."""
    with open(ids_file, 'r') as f:
        data = json.load(f)
    return set(data['task_ids'])


def analyze_performance(results_csv: Path, hard_subset_ids: set):
    """Analyze model performance on hard subset vs overall."""
    
    print(f"Loading results from: {results_csv}")
    df = pd.read_csv(results_csv)
    print(f"  Loaded {len(df)} experiment results")
    print(f"  Unique models: {df['LLM'].nunique()}")
    print(f"  Unique tasks (all languages): {df['Task ID'].nunique()}")
    
    # Filter for DAFNY only (for fair comparison)
    df_dafny = df[df['Language'] == 'dafny'].copy()
    print(f"\nDafny tasks only: {len(df_dafny)} experiment results")
    print(f"  Unique Dafny tasks: {df_dafny['Task ID'].nunique()}")
    
    # Filter for hard subset
    df_hard = df_dafny[df_dafny['Task ID'].isin(hard_subset_ids)].copy()
    print(f"\nHard subset (Dafny): {len(df_hard)} experiment results")
    print(f"  Unique tasks in hard subset: {df_hard['Task ID'].nunique()}")
    
    # Calculate pass rates by model
    print("\nCalculating pass rates...")
    
    # Overall pass rates (DAFNY ONLY for fair comparison)
    overall_stats = df_dafny.groupby('LLM').agg({
        'Success': ['sum', 'count', 'mean']
    }).reset_index()
    overall_stats.columns = ['LLM', 'Passes', 'Total', 'Pass Rate']
    overall_stats = overall_stats.sort_values('Pass Rate', ascending=False)
    
    # Hard subset pass rates
    hard_stats = df_hard.groupby('LLM').agg({
        'Success': ['sum', 'count', 'mean']
    }).reset_index()
    hard_stats.columns = ['LLM', 'Passes_Hard', 'Total_Hard', 'Pass Rate_Hard']
    hard_stats = hard_stats.sort_values('Pass Rate_Hard', ascending=False)
    
    # Merge stats
    combined = pd.merge(overall_stats, hard_stats, on='LLM', how='outer')
    combined = combined.fillna(0)
    
    # Calculate difference
    combined['Diff'] = combined['Pass Rate_Hard'] - combined['Pass Rate']
    combined = combined.sort_values('Pass Rate_Hard', ascending=False)
    
    return combined, df_dafny, df_hard


def print_statistics(combined_stats):
    """Print model performance statistics."""
    
    print("\n" + "="*120)
    print("MODEL PERFORMANCE: HARD SUBSET vs OVERALL DAFNY BENCHMARK")
    print("="*120)
    print(f"\n{'Model':<25} | {'All Dafny':<12} | {'All %':<10} | {'Hard Subset':<12} | {'Hard %':<10} | {'Diff':<8}")
    print("-"*120)
    
    for _, row in combined_stats.iterrows():
        model = row['LLM']
        overall_pass = f"{int(row['Passes'])}/{int(row['Total'])}"
        overall_pct = row['Pass Rate'] * 100
        hard_pass = f"{int(row['Passes_Hard'])}/{int(row['Total_Hard'])}"
        hard_pct = row['Pass Rate_Hard'] * 100
        diff = row['Diff'] * 100
        
        diff_str = f"{diff:+.1f}%" if row['Total_Hard'] > 0 else "N/A"
        
        print(f"{model:<25} | {overall_pass:<12} | {overall_pct:>9.1f}% | "
              f"{hard_pass:<12} | {hard_pct:>9.1f}% | {diff_str:<8}")
    
    print("="*120)
    
    # Summary statistics
    print("\nSummary (Dafny only):")
    print(f"  Average pass rate (all Dafny tasks): {combined_stats['Pass Rate'].mean()*100:.1f}%")
    print(f"  Average pass rate (hard subset): {combined_stats['Pass Rate_Hard'].mean()*100:.1f}%")
    print(f"  Average difference: {combined_stats['Diff'].mean()*100:+.1f}%")
    print()


def analyze_by_benchmark(df, df_hard, hard_subset_ids):
    """Analyze performance breakdown by benchmark."""
    
    print("\n" + "="*100)
    print("PERFORMANCE BY BENCHMARK (Hard Subset)")
    print("="*100)
    
    # Get top models
    top_models = df_hard.groupby('LLM')['Success'].mean().nlargest(5).index.tolist()
    
    print(f"\nTop 5 models: {', '.join(top_models)}\n")
    
    # For each benchmark
    benchmarks = df_hard['Benchmark'].unique()
    
    for benchmark in sorted(benchmarks):
        df_bench = df_hard[df_hard['Benchmark'] == benchmark]
        
        print(f"\n{benchmark.upper()}:")
        print(f"{'Model':<25} | {'Passes':<10} | {'Total':<6} | {'Pass %':<8}")
        print("-"*60)
        
        bench_stats = df_bench.groupby('LLM').agg({
            'Success': ['sum', 'count', 'mean']
        }).reset_index()
        bench_stats.columns = ['LLM', 'Passes', 'Total', 'PassRate']
        bench_stats = bench_stats.sort_values('PassRate', ascending=False)
        
        for _, row in bench_stats.head(10).iterrows():
            model = row['LLM']
            passes = int(row['Passes'])
            total = int(row['Total'])
            rate = row['PassRate'] * 100
            print(f"{model:<25} | {passes:<10} | {total:<6} | {rate:>7.1f}%")
    
    print("="*100 + "\n")


def save_results(combined_stats, output_file: Path):
    """Save results to CSV."""
    combined_stats.to_csv(output_file, index=False)
    print(f"✓ Saved detailed results to: {output_file}")


def create_summary_report(combined_stats, output_file: Path):
    """Create a markdown summary report."""
    
    content = """# Model Performance on Hard Subset

## Hard Subset Criteria
- **Spec Faithfulness**: ≥ 2
- **Spec Leakage**: ≤ 1  
- **Difficulty**: ≥ 1

## Performance Comparison

| Model | Overall Pass Rate | Hard Subset Pass Rate | Difference |
|-------|-------------------|----------------------|------------|
"""
    
    for _, row in combined_stats.iterrows():
        model = row['LLM']
        overall = f"{row['Pass Rate']*100:.1f}%"
        hard = f"{row['Pass Rate_Hard']*100:.1f}%" if row['Total_Hard'] > 0 else "N/A"
        diff = f"{row['Diff']*100:+.1f}%" if row['Total_Hard'] > 0 else "N/A"
        content += f"| {model} | {overall} | {hard} | {diff} |\n"
    
    content += f"""

## Key Insights

### Best Performing Models (Hard Subset)
"""
    
    top_models = combined_stats.nlargest(5, 'Pass Rate_Hard')
    for i, (_, row) in enumerate(top_models.iterrows(), 1):
        content += f"{i}. **{row['LLM']}**: {row['Pass Rate_Hard']*100:.1f}% ({int(row['Passes_Hard'])}/{int(row['Total_Hard'])})\n"
    
    content += """
### Observations

- Models typically perform **worse** on the hard subset (higher quality, more challenging tasks)
- The difference column shows how much harder the hard subset is for each model
- Negative differences indicate the model struggles more with high-quality, low-leakage tasks
"""
    
    with open(output_file, 'w') as f:
        f.write(content)
    
    print(f"✓ Saved summary report to: {output_file}")


def main():
    parser = argparse.ArgumentParser(description="Analyze model performance on hard subset")
    parser.add_argument(
        "--results-csv",
        type=Path,
        default=Path("../vericoding-benchmark/vericoding_results_v1.csv"),
        help="Path to vericoding results CSV"
    )
    parser.add_argument(
        "--hard-subset-ids",
        type=Path,
        default=Path("../hard_subsets/dafny/hard_subset_ids.json"),
        help="Path to hard subset IDs JSON"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("../hard_subsets/dafny"),
        help="Output directory"
    )
    
    args = parser.parse_args()
    
    if not args.results_csv.exists():
        print(f"Error: Results CSV not found: {args.results_csv}")
        return 1
    
    if not args.hard_subset_ids.exists():
        print(f"Error: Hard subset IDs not found: {args.hard_subset_ids}")
        return 1
    
    # Load hard subset IDs
    print(f"Loading hard subset IDs from: {args.hard_subset_ids}")
    hard_subset_ids = load_hard_subset_ids(args.hard_subset_ids)
    print(f"  Loaded {len(hard_subset_ids)} task IDs")
    
    # Analyze performance
    combined_stats, df_all, df_hard = analyze_performance(args.results_csv, hard_subset_ids)
    
    # Print statistics
    print_statistics(combined_stats)
    
    # Analyze by benchmark
    analyze_by_benchmark(df_all, df_hard, hard_subset_ids)
    
    # Save results
    args.output_dir.mkdir(parents=True, exist_ok=True)
    save_results(combined_stats, args.output_dir / "model_performance_hard_subset.csv")
    create_summary_report(combined_stats, args.output_dir / "model_performance_summary.md")
    
    print(f"\n{'='*60}")
    print("Analysis complete!")
    print(f"Output directory: {args.output_dir}")
    print(f"{'='*60}\n")
    
    return 0


if __name__ == "__main__":
    exit(main())

