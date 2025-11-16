#!/usr/bin/env python3
"""
Visualize quality check results with bar plots showing average ratings
and standard deviations for each benchmark.
"""

import argparse
import json
from collections import defaultdict
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np


ANALYSIS_DIR = Path(__file__).resolve().parent
SCRIPTS_DIR = ANALYSIS_DIR.parent
FILTER_ENGINE_ROOT = SCRIPTS_DIR.parent
DEFAULT_RESULTS_FILE = FILTER_ENGINE_ROOT / "results" / "dafny_quality_results.jsonl"
DEFAULT_OUTPUT_FILE = (
    FILTER_ENGINE_ROOT / "outputs" / "quality_metrics_by_benchmark.png"
)

# Set nice plotting defaults
mpl.rcParams["font.size"] = 10
mpl.rcParams["axes.labelsize"] = 11
mpl.rcParams["axes.titlesize"] = 12
mpl.rcParams["xtick.labelsize"] = 9
mpl.rcParams["ytick.labelsize"] = 10


def load_results(results_file: Path):
    """Load results from JSONL file."""
    results = []
    with open(results_file, 'r') as f:
        for line in f:
            try:
                result = json.loads(line)
                if not result.get('error', False):
                    results.append(result)
            except json.JSONDecodeError:
                continue
    return results


def aggregate_by_benchmark(results):
    """Aggregate results by benchmark source."""
    by_source = defaultdict(lambda: {
        'spec_faithfulness': [],
        'spec_leakage': [],
        'difficulty': []
    })
    
    for result in results:
        source = result.get('source', 'unknown')
        by_source[source]['spec_faithfulness'].append(result.get('spec_faithfulness', -1))
        by_source[source]['spec_leakage'].append(result.get('spec_leakage', -1))
        by_source[source]['difficulty'].append(result.get('difficulty', -1))
    
    return by_source


def calculate_stats(by_source):
    """Calculate distribution (percentages) for each rating level and overall std."""
    stats = {}
    
    # First pass: discover all unique rating values across all data
    all_ratings = set()
    for source, metrics in by_source.items():
        for metric_name, values in metrics.items():
            # Include -1 values this time (they're valid ratings, just special)
            all_ratings.update(values)
    
    # Get sorted list of all rating values found
    rating_values = sorted(list(all_ratings))
    
    for source, metrics in by_source.items():
        stats[source] = {}
        for metric_name, values in metrics.items():
            if values:
                total = len(values)
                # Count occurrences of each rating value found in the data
                distribution = {}
                for rating in rating_values:
                    count = sum(1 for v in values if v == rating)
                    distribution[rating] = (count / total * 100) if total > 0 else 0
                
                stats[source][metric_name] = {
                    'distribution': distribution,
                    'rating_values': rating_values,
                    'mean': np.mean(values),
                    'std': np.std(values),
                    'count': total
                }
            else:
                stats[source][metric_name] = {
                    'distribution': {r: 0 for r in rating_values},
                    'rating_values': rating_values,
                    'mean': 0,
                    'std': 0,
                    'count': 0
                }
    
    return stats, rating_values


def create_visualization(stats, rating_values, output_file: Path):
    """Create grouped bar plots showing percentage distribution for each rating."""
    
    # Prepare data for each metric
    metrics = ['spec_faithfulness', 'spec_leakage', 'difficulty']
    metric_labels = [
        'Spec Faithfulness',
        'Spec Leakage',
        'Difficulty'
    ]
    
    # Create figure with 3 subplots stacked vertically
    fig, axes = plt.subplots(3, 1, figsize=(14, 12))
    fig.suptitle('Quality Metrics Distribution by Benchmark (Dafny)', fontsize=14, fontweight='bold')
    
    # Generate dynamic colors based on number of rating values
    # Interpolate from red (bad) to green (good)
    n_ratings = len(rating_values)
    
    def generate_colors(n, inverted=False):
        """Generate n colors interpolating from red to green (or inverted)."""
        from matplotlib.colors import LinearSegmentedColormap
        if inverted:
            # Green (good) to Red (bad)
            cmap = LinearSegmentedColormap.from_list('custom', ['#1a9850', '#fee08b', '#d73027'])
        else:
            # Red (bad) to Green (good)
            cmap = LinearSegmentedColormap.from_list('custom', ['#d73027', '#fee08b', '#1a9850'])
        
        return [cmap(i / max(1, n - 1)) for i in range(n)]
    
    rating_colors_normal = generate_colors(n_ratings, inverted=False)
    rating_colors_inverted = generate_colors(n_ratings, inverted=True)
    rating_labels = [f'Rating {r}' for r in rating_values]
    
    for idx, (metric, label) in enumerate(zip(metrics, metric_labels)):
        ax = axes[idx]
        
        # Choose color scheme: inverted for leakage (0 is best), normal for others (3 is best)
        if metric == 'spec_leakage':
            rating_colors = rating_colors_inverted
        else:
            rating_colors = rating_colors_normal
        
        # Extract data for this metric and sort by mean value
        benchmark_data = []
        for source, metrics_dict in stats.items():
            if metrics_dict[metric]['count'] > 0:
                benchmark_data.append({
                    'name': source,
                    'distribution': metrics_dict[metric]['distribution'],
                    'mean': metrics_dict[metric]['mean'],
                    'std': metrics_dict[metric]['std'],
                    'count': metrics_dict[metric]['count']
                })
        
        # Sort by mean value (descending)
        benchmark_data.sort(key=lambda x: x['mean'], reverse=True)
        
        # Extract sorted data
        names = [item['name'] for item in benchmark_data]
        n_benchmarks = len(names)
        
        # Set up bar positions
        x_pos = np.arange(n_benchmarks)
        width = 0.8 / n_ratings  # Dynamic width based on number of ratings
        
        # Plot bars for each rating level with individual error bars
        for rating_idx, rating in enumerate(rating_values):
            percentages = [item['distribution'][rating] for item in benchmark_data]
            counts = [item['count'] for item in benchmark_data]
            
            # Calculate error bars (standard error of proportion)
            errors = []
            for pct, n in zip(percentages, counts):
                p = pct / 100.0  # Convert percentage to proportion
                # Standard error of proportion: sqrt(p*(1-p)/n)
                se = np.sqrt(p * (1 - p) / n) * 100 if n > 0 else 0  # Convert back to percentage
                errors.append(se)
            
            # Center the group of bars
            offset = (rating_idx - (n_ratings - 1) / 2) * width
            bars = ax.bar(x_pos + offset, percentages, width, 
                         yerr=errors,
                         capsize=3,
                         label=rating_labels[rating_idx], 
                         color=rating_colors[rating_idx], 
                         edgecolor='black', linewidth=0.5, alpha=0.85,
                         error_kw={'linewidth': 1, 'ecolor': 'black', 'alpha': 0.6})
        
        # Customize plot
        ax.set_ylabel(f'{label}\n(Percentage %)', fontweight='bold')
        ax.set_xticks(x_pos)
        ax.set_xticklabels(names, rotation=45, ha='right')
        ax.set_ylim(0, 115)
        ax.grid(axis='y', alpha=0.3, linestyle='--')
        
        # Create legend with color-coded explanation
        legend = ax.legend(loc='upper right', fontsize=8, ncol=4, framealpha=0.9)
        
        # Add sample counts below bars
        for i, item in enumerate(benchmark_data):
            ax.text(i, -6, f'n={item["count"]}',
                   ha='center', va='top', fontsize=7, style='italic', color='gray')
        
        # Add metric description with color coding explanation
        if metric == 'spec_leakage':
            desc_text = 'GREEN (R0) = Best (no leakage) → RED (R3) = Worst (high leakage)'
        else:
            desc_text = 'RED (R0) = Worst → GREEN (R3) = Best'
        
        descriptions = {
            'spec_faithfulness': 'Higher ratings = spec better captures description requirements',
            'spec_leakage': 'Lower ratings = spec reveals less implementation (better)',
            'difficulty': 'Higher ratings = more challenging problem'
        }
        
        ax.text(0.02, 0.98, descriptions[metric] + '\n' + desc_text, 
               transform=ax.transAxes, fontsize=7.5, verticalalignment='top',
               bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.5))
    
    plt.tight_layout()
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=300, bbox_inches="tight")
    print(f"\n✓ Visualization saved to: {output_file}")
    
    return benchmark_data, stats


def print_summary_table(stats, rating_values):
    """Print a summary table with distribution percentages."""
    print("\n" + "="*140)
    print("RATING DISTRIBUTION BY BENCHMARK (Percentages)")
    print("="*140)
    
    # Sort by average across all metrics
    sorted_sources = sorted(stats.items(), 
                          key=lambda x: (x[1]['spec_faithfulness']['mean'] + 
                                       x[1]['spec_leakage']['mean'] + 
                                       x[1]['difficulty']['mean']) / 3,
                          reverse=True)
    
    for source, metrics_dict in sorted_sources:
        print(f"\n{source.upper()} (n={metrics_dict['spec_faithfulness']['count']})")
        print("-" * 140)
        
        for metric_name in ['spec_faithfulness', 'spec_leakage', 'difficulty']:
            dist = metrics_dict[metric_name]['distribution']
            mean = metrics_dict[metric_name]['mean']
            std = metrics_dict[metric_name]['std']
            
            metric_label = metric_name.replace('_', ' ').title()
            # Build distribution string dynamically based on rating values
            dist_str = "  ".join([f"R{r}: {dist[r]:>5.1f}%" for r in rating_values])
            print(f"  {metric_label:<20} | {dist_str}  | Mean: {mean:.2f} ± {std:.2f}")
    
    print("\n" + "="*140 + "\n")


def main():
    parser = argparse.ArgumentParser(description="Visualize quality check results")
    parser.add_argument(
        "--results-file",
        type=Path,
        default=DEFAULT_RESULTS_FILE,
        help="Path to results JSONL file",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT_FILE,
        help="Output file for visualization",
    )

    args = parser.parse_args()

    if not args.results_file.exists():
        print(f"Error: Results file not found: {args.results_file}")
        return 1

    print(f"Loading results from: {args.results_file}")
    results = load_results(args.results_file)
    print(f"  Loaded {len(results)} valid results")

    print("\nAggregating by benchmark...")
    by_source = aggregate_by_benchmark(results)
    print(f"  Found {len(by_source)} benchmarks")

    print("\nCalculating statistics...")
    stats, rating_values = calculate_stats(by_source)
    print(f"  Detected rating values: {rating_values}")

    print("\nCreating visualization...")
    create_visualization(stats, rating_values, args.output)

    print_summary_table(stats, rating_values)

    print(f"\n{'='*60}")
    print("Visualization complete!")
    print(f"Output saved to: {args.output}")
    print(f"{'='*60}\n")

    return 0


if __name__ == "__main__":
    exit(main())

