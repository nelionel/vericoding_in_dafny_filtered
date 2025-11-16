#!/usr/bin/env python3
"""
Create flat folder structure for hard subset with metadata and analysis.
"""

import json
import shutil
import pandas as pd
from pathlib import Path
from collections import defaultdict
import numpy as np
import matplotlib.pyplot as plt
import argparse


def load_hard_subset_with_ratings(results_jsonl: Path):
    """Load hard subset with quality ratings."""
    task_ratings = {}
    
    with open(results_jsonl, 'r') as f:
        for line in f:
            result = json.loads(line)
            
            # Check if in hard subset (faithfulness >= 2, leakage <= 1, difficulty >= 1)
            if (result.get('spec_faithfulness', -999) >= 2 and
                result.get('spec_leakage', -999) <= 1 and
                result.get('difficulty', -999) >= 1):
                
                task_ratings[result['id']] = {
                    'spec_faithfulness': result.get('spec_faithfulness', -1),
                    'spec_leakage': result.get('spec_leakage', -1),
                    'difficulty': result.get('difficulty', -1),
                    'source': result.get('source', 'unknown'),
                    'language': result.get('language', 'unknown'),
                    'explanation': result.get('explanation', '')
                }
    
    return task_ratings


def count_models_passed(results_csv: Path, task_ratings: dict):
    """Count how many models passed each task."""
    
    print(f"Loading model results from: {results_csv}")
    df = pd.read_csv(results_csv)
    
    # Filter for Dafny tasks in hard subset
    df_hard = df[df['Task ID'].isin(task_ratings.keys())]
    
    print(f"  Total experiments: {len(df_hard)}")
    print(f"  Unique tasks in results: {df_hard['Task ID'].nunique()}")
    
    # Count models passed per task
    task_model_counts = {}
    
    for task_id in task_ratings.keys():
        df_task = df_hard[df_hard['Task ID'] == task_id]
        
        if len(df_task) > 0:
            # Count unique models that succeeded
            models_passed = df_task[df_task['Success'] == 1]['LLM'].nunique()
            total_models = df_task['LLM'].nunique()
            
            task_model_counts[task_id] = {
                'models_passed': models_passed,
                'models_total': total_models,
                'pass_rate': (models_passed / total_models * 100) if total_models > 0 else 0
            }
        else:
            # Task not in results CSV
            task_model_counts[task_id] = {
                'models_passed': 0,
                'models_total': 0,
                'pass_rate': 0
            }
    
    return task_model_counts


def copy_hard_subset_files(task_ratings: dict, benchmark_dir: Path, output_dir: Path):
    """Copy hard subset spec files to flat folder."""
    
    specs_dir = benchmark_dir / "specs"
    files_dir = output_dir / "files"
    files_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"\nCopying {len(task_ratings)} hard subset files...")
    
    # Detect language from first task
    first_language = list(task_ratings.values())[0].get('language', 'dafny')
    ext_map = {'dafny': 'dfy', 'lean': 'lean', 'verus': 'rs'}
    ext = ext_map.get(first_language, 'dfy')
    
    copied = 0
    missing = []
    
    for task_id in task_ratings.keys():
        # Find spec file with correct extension
        spec_file = specs_dir / f"{task_id}_specs.{ext}"
        
        if spec_file.exists():
            # Copy to flat folder
            dest = files_dir / spec_file.name
            shutil.copy2(spec_file, dest)
            copied += 1
        else:
            missing.append(task_id)
    
    print(f"  Copied: {copied}")
    print(f"  Missing: {len(missing)}")
    
    if missing:
        print(f"  First missing: {missing[:5]}")
    
    return copied, missing


def create_metadata_json(task_ratings: dict, task_model_counts: dict, output_file: Path):
    """Create JSON with metadata for each task."""
    
    metadata = {}
    
    for task_id, ratings in task_ratings.items():
        model_info = task_model_counts.get(task_id, {'models_passed': 0, 'models_total': 0, 'pass_rate': 0})
        
        metadata[f"{task_id}_specs.dfy"] = {
            'task_id': task_id,
            'source': ratings['source'],
            'difficulty': ratings['difficulty'],
            'spec_faithfulness': ratings['spec_faithfulness'],
            'spec_leakage': ratings['spec_leakage'],
            'models_passed': model_info['models_passed'],
            'models_total': model_info['models_total'],
            'model_pass_rate': model_info['pass_rate'],
            'explanation': ratings['explanation']
        }
    
    with open(output_file, 'w') as f:
        json.dump(metadata, f, indent=2)
    
    print(f"\n✓ Created metadata JSON: {output_file}")
    return metadata


def create_correlation_plot(metadata: dict, output_file: Path):
    """Create plot showing relationship between difficulty and model success."""
    
    # Extract data
    data_points = []
    for filename, meta in metadata.items():
        if meta['models_total'] > 0:  # Only include tasks with model results
            data_points.append({
                'difficulty': meta['difficulty'],
                'models_passed': meta['models_passed'],
                'models_total': meta['models_total'],
                'source': meta['source']
            })
    
    # Group by difficulty rating
    by_difficulty = defaultdict(list)
    for point in data_points:
        by_difficulty[point['difficulty']].append(point['models_passed'])
    
    # Calculate statistics
    difficulties = sorted(by_difficulty.keys())
    means = []
    stds = []
    counts = []
    
    for diff in difficulties:
        values = by_difficulty[diff]
        means.append(np.mean(values))
        stds.append(np.std(values))
        counts.append(len(values))
    
    # Create plot
    fig, ax = plt.subplots(figsize=(10, 6))
    
    # Bar plot with error bars
    x_pos = np.arange(len(difficulties))
    colors = ['#d73027', '#fc8d59', '#fee08b', '#1a9850']
    
    bars = ax.bar(x_pos, means, yerr=stds, capsize=5,
                  color=[colors[d] if d < len(colors) else colors[-1] for d in difficulties],
                  edgecolor='black', linewidth=1, alpha=0.85,
                  error_kw={'linewidth': 2, 'ecolor': 'black', 'alpha': 0.7})
    
    # Customize
    ax.set_xlabel('LLM-Rated Difficulty', fontweight='bold', fontsize=12)
    ax.set_ylabel('Average Number of Models Passed', fontweight='bold', fontsize=12)
    ax.set_title('Model Success vs Task Difficulty (Hard Subset)', fontweight='bold', fontsize=14)
    ax.set_xticks(x_pos)
    ax.set_xticklabels([f'Difficulty {d}' for d in difficulties])
    ax.grid(axis='y', alpha=0.3, linestyle='--')
    
    # Add value labels and counts
    for i, (bar, mean, std, count) in enumerate(zip(bars, means, stds, counts)):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height + std + 0.2,
               f'{mean:.1f}',
               ha='center', va='bottom', fontsize=10, fontweight='bold')
        ax.text(bar.get_x() + bar.get_width()/2., -0.3,
               f'n={count}',
               ha='center', va='top', fontsize=9, style='italic', color='gray')
    
    # Add explanation
    ax.text(0.02, 0.98, 
           'Lower bars = harder tasks (fewer models succeed)\nError bars show standard deviation',
           transform=ax.transAxes, fontsize=9, verticalalignment='top',
           bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.5))
    
    plt.tight_layout()
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    print(f"\n✓ Created correlation plot: {output_file}")
    
    # Print statistics
    print(f"\nCorrelation Statistics:")
    print(f"{'Difficulty':<12} | {'Avg Models':<12} | {'Std Dev':<10} | {'Count':<8}")
    print("-"*50)
    for diff, mean, std, count in zip(difficulties, means, stds, counts):
        print(f"{diff:<12} | {mean:>11.2f} | {std:>9.2f} | {count:<8}")
    
    # Calculate correlation coefficient
    diff_values = [p['difficulty'] for p in data_points]
    model_values = [p['models_passed'] for p in data_points]
    correlation = np.corrcoef(diff_values, model_values)[0, 1]
    print(f"\nPearson correlation (difficulty vs models passed): {correlation:.3f}")
    
    return data_points


def create_readme(output_dir: Path, num_tasks: int, num_copied: int):
    """Create README for the hard subset folder."""
    
    content = f"""# Hard Subset - Flat Structure

This folder contains {num_tasks} high-quality, challenging Dafny verification tasks.

## Filter Criteria

- **Spec Faithfulness**: ≥ 2 (faithful specs)
- **Spec Leakage**: ≤ 1 (low leakage)
- **Difficulty**: ≥ 1 (non-trivial)

## Folder Structure

```
hard_subset_flat/
├── files/                      # {num_copied} specification files
│   ├── DA0000_specs.dfy
│   ├── DA0004_specs.dfy
│   └── ...
├── metadata.json               # Task metadata and model performance
├── difficulty_vs_models.png    # Correlation plot
└── README.md                   # This file
```

## metadata.json

Maps each filename to:
- `difficulty`: LLM-rated difficulty (0-3)
- `spec_faithfulness`: How well spec captures description (0-3)
- `spec_leakage`: How much spec reveals implementation (0-3)
- `models_passed`: Number of models that successfully verified this task
- `models_total`: Number of models that attempted this task
- `model_pass_rate`: Percentage of models that passed
- `source`: Which benchmark this task came from
- `explanation`: LLM explanation of the ratings

## Usage Examples

### Find hardest tasks (difficulty = 3)
```bash
jq 'to_entries[] | select(.value.difficulty == 3) | .key' metadata.json
```

### Find tasks no model solved
```bash
jq 'to_entries[] | select(.value.models_passed == 0) | .key' metadata.json
```

### Find easy hard-subset tasks (many models passed)
```bash
jq 'to_entries[] | select(.value.models_passed >= 7) | .key' metadata.json
```

### Get stats by source
```bash
jq 'group_by(.value.source) | map({{source: .[0].value.source, count: length}})' metadata.json
```

## Correlation Analysis

The `difficulty_vs_models.png` plot shows the relationship between:
- **X-axis**: LLM-rated difficulty
- **Y-axis**: Average number of models that passed

Expected: Higher difficulty → Fewer models pass (negative correlation)
"""
    
    with open(output_dir / "README.md", 'w') as f:
        f.write(content)
    
    print(f"\n✓ Created README: {output_dir / 'README.md'}")


def main():
    script_dir = Path(__file__).resolve().parent
    filter_engine_root = script_dir.parents[1]
    hard_subset_root = filter_engine_root.parent
    raw_data_dir = hard_subset_root / "raw_data"
    default_ratings = filter_engine_root / "outputs" / "hard_subsets_dafny" / "hard_subset_results.jsonl"
    default_results_csv = raw_data_dir / "vericoding_results_v1.csv"
    default_benchmark_dir = raw_data_dir / "vericoding-benchmark"
    default_output_dir = hard_subset_root / "dafny_flat"

    parser = argparse.ArgumentParser(description="Create flat folder for Dafny hard subset")
    parser.add_argument(
        "--ratings-jsonl",
        type=Path,
        default=default_ratings,
        help="Path to hard_subset_results.jsonl",
    )
    parser.add_argument(
        "--results-csv",
        type=Path,
        default=default_results_csv,
        help="CSV of aggregate model results (vericoding_results_v1.csv)",
    )
    parser.add_argument(
        "--benchmark-dir",
        type=Path,
        default=default_benchmark_dir,
        help="Directory that holds specs/ for each task",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=default_output_dir,
        help="Destination for the flat hard subset folder",
    )
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    print("="*60)
    print("Creating Hard Subset Flat Structure")
    print("="*60)
    
    # Load hard subset with ratings
    print("\nLoading quality ratings...")
    task_ratings = load_hard_subset_with_ratings(args.ratings_jsonl)
    print(f"  Found {len(task_ratings)} tasks in hard subset")
    
    # Count models that passed each task
    task_model_counts = count_models_passed(
        args.results_csv,
        task_ratings
    )
    
    # Copy files
    num_copied, missing = copy_hard_subset_files(
        task_ratings,
        args.benchmark_dir,
        args.output_dir
    )
    
    # Create metadata JSON
    metadata = create_metadata_json(
        task_ratings,
        task_model_counts,
        args.output_dir / "metadata.json"
    )
    
    # Create correlation plot
    data_points = create_correlation_plot(
        metadata,
        args.output_dir / "difficulty_vs_models.png"
    )
    
    # Create README
    create_readme(args.output_dir, len(task_ratings), num_copied)
    
    print("\n" + "="*60)
    print("Hard subset flat structure complete!")
    print(f"Output directory: {args.output_dir}")
    print(f"  Files: {num_copied}")
    print(f"  Metadata: metadata.json")
    print(f"  Plot: difficulty_vs_models.png")
    print("="*60 + "\n")
    
    return 0


if __name__ == "__main__":
    exit(main())



