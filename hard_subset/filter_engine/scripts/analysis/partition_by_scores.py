#!/usr/bin/env python3
"""
Partition benchmark problems by their quality scores.
Creates folder structure: benchmark/language/criteria/score/task_file.dfy
"""

import argparse
import json
import os
import shutil
from collections import defaultdict
from pathlib import Path


ANALYSIS_DIR = Path(__file__).resolve().parent
SCRIPTS_DIR = ANALYSIS_DIR.parent
FILTER_ENGINE_ROOT = SCRIPTS_DIR.parent
REPO_ROOT = FILTER_ENGINE_ROOT.parent.parent
RAW_DATA_ROOT = REPO_ROOT / "hard_subset" / "raw_data"
DEFAULT_RESULTS_FILE = FILTER_ENGINE_ROOT / "results" / "dafny_quality_results.jsonl"
DEFAULT_BENCHMARK_DIR = RAW_DATA_ROOT / "vericoding-benchmark"
DEFAULT_OUTPUT_DIR = FILTER_ENGINE_ROOT / "outputs" / "partitioned_benchmark"


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


def find_spec_file(task_id: str, language: str, benchmark_dir: Path):
    """Find the specification file for a given task."""
    specs_dir = benchmark_dir / "specs"
    
    # Construct expected filename
    spec_file = specs_dir / f"{task_id}_specs.{get_extension(language)}"
    
    if spec_file.exists():
        return spec_file
    
    # Fallback: search for the file
    for ext in ['dfy', 'lean', 'rs']:
        spec_file = specs_dir / f"{task_id}_specs.{ext}"
        if spec_file.exists():
            return spec_file
    
    return None


def get_extension(language: str) -> str:
    """Get file extension for language."""
    extensions = {
        'dafny': 'dfy',
        'lean': 'lean',
        'verus': 'rs'
    }
    return extensions.get(language, 'txt')


def partition_results(results, benchmark_dir: Path, output_dir: Path, copy_files: bool = False):
    """Partition results into folder structure."""
    
    print(f"\nPartitioning {len(results)} results...")
    print(f"Output directory: {output_dir}")
    
    stats = defaultdict(int)
    missing_files = []
    
    for result in results:
        task_id = result['id']
        language = result['language']
        source = result['source']
        
        # Get scores for each criteria
        criteria_scores = {
            'spec_faithfulness': result.get('spec_faithfulness', -999),
            'spec_leakage': result.get('spec_leakage', -999),
            'difficulty': result.get('difficulty', -999)
        }
        
        # Find the spec file
        spec_file = find_spec_file(task_id, language, benchmark_dir)
        
        if spec_file is None:
            missing_files.append(task_id)
            stats['missing_files'] += 1
            continue
        
        # Create folder structure for each criteria
        for criteria, score in criteria_scores.items():
            # Create path: benchmark/language/criteria/score/
            target_dir = output_dir / source / language / criteria / str(score)
            target_dir.mkdir(parents=True, exist_ok=True)
            
            # Target file path
            target_file = target_dir / spec_file.name
            
            # Copy or symlink the file
            if copy_files:
                if not target_file.exists():
                    shutil.copy2(spec_file, target_file)
                    stats['files_copied'] += 1
            else:
                # Create symlink
                if not target_file.exists():
                    relative_path = os.path.relpath(spec_file, target_dir)
                    target_file.symlink_to(relative_path)
                    stats['symlinks_created'] += 1
        
        stats['tasks_processed'] += 1
        
        if stats['tasks_processed'] % 100 == 0:
            print(f"  Processed {stats['tasks_processed']} tasks...")
    
    return stats, missing_files


def print_statistics(stats, missing_files):
    """Print partitioning statistics."""
    print("\n" + "="*60)
    print("PARTITIONING STATISTICS")
    print("="*60)
    print(f"Tasks processed:     {stats['tasks_processed']}")
    print(f"Files copied:        {stats.get('files_copied', 0)}")
    print(f"Symlinks created:    {stats.get('symlinks_created', 0)}")
    print(f"Missing spec files:  {stats['missing_files']}")
    
    if missing_files and len(missing_files) <= 10:
        print(f"\nMissing files:")
        for task_id in missing_files:
            print(f"  - {task_id}")
    elif missing_files:
        print(f"\nFirst 10 missing files:")
        for task_id in missing_files[:10]:
            print(f"  - {task_id}")
        print(f"  ... and {len(missing_files) - 10} more")
    
    print("="*60 + "\n")


def create_readme(output_dir: Path, results_file: Path):
    """Create README explaining the folder structure."""
    readme_content = f"""# Partitioned Benchmark Results

This directory contains benchmark problems partitioned by their quality scores.

## Folder Structure

```
benchmark_name/
  language/
    spec_faithfulness/
      -1/  (error cases)
      0/   (worst)
      1/
      2/
      3/   (best)
    spec_leakage/
      -1/  (error cases)
      0/   (best - no leakage)
      1/
      2/
      3/   (worst - high leakage)
    difficulty/
      -1/  (error cases)
      0/   (trivial)
      1/   (easy)
      2/   (moderate)
      3/   (hard)
```

## Criteria Meanings

### Spec Faithfulness (0-3)
How well the formal specification captures the problem description:
- **0**: Spec misses description intent
- **1**: Spec captures some but misses key requirements
- **2**: Spec captures most requirements, minor gaps
- **3**: Spec faithfully captures all requirements ✓

### Spec Leakage (0-3)
How much the spec reveals implementation steps:
- **0**: No leakage - spec only states WHAT, not HOW ✓
- **1**: Minor leakage
- **2**: Significant leakage
- **3**: Complete leakage - spec dictates implementation

### Difficulty (0-3)
Inherent problem difficulty:
- **0**: Trivial
- **1**: Easy
- **2**: Moderate
- **3**: Hard

## Source Data

Quality results from: `{results_file}`

## Usage Examples

Find all high-quality tasks (faithful specs, no leakage, hard difficulty):
```bash
# Apps benchmark, Dafny, faithfulness=3, leakage=0, difficulty=3
ls apps/dafny/spec_faithfulness/3/
ls apps/dafny/spec_leakage/0/
ls apps/dafny/difficulty/3/
```

Find all tasks with spec leakage problems:
```bash
find . -path "*/spec_leakage/3/*.dfy"
```

Count tasks by difficulty:
```bash
for i in -1 0 1 2 3; do
  echo "Difficulty $i: $(find . -path "*/difficulty/$i/*.dfy" | wc -l)"
done
```
"""
    
    readme_file = output_dir / "README.md"
    readme_file.write_text(readme_content)
    print(f"✓ Created README: {readme_file}")


def main():
    parser = argparse.ArgumentParser(description="Partition benchmark by quality scores")
    parser.add_argument(
        "--results-file",
        type=Path,
        default=DEFAULT_RESULTS_FILE,
        help="Path to quality results JSONL file",
    )
    parser.add_argument(
        "--benchmark-dir",
        type=Path,
        default=DEFAULT_BENCHMARK_DIR,
        help="Path to benchmark directory",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Output directory for partitioned files",
    )
    parser.add_argument(
        "--copy",
        action="store_true",
        help="Copy files instead of creating symlinks (default: symlinks)",
    )

    args = parser.parse_args()

    if not args.results_file.exists():
        print(f"Error: Results file not found: {args.results_file}")
        return 1

    if not args.benchmark_dir.exists():
        print(f"Error: Benchmark directory not found: {args.benchmark_dir}")
        return 1

    print(f"Loading results from: {args.results_file}")
    results = load_results(args.results_file)
    print(f"  Loaded {len(results)} results")

    args.output_dir.mkdir(parents=True, exist_ok=True)

    stats, missing_files = partition_results(
        results,
        args.benchmark_dir,
        args.output_dir,
        copy_files=args.copy,
    )

    print_statistics(stats, missing_files)
    create_readme(args.output_dir, args.results_file)

    print(f"\n{'='*60}")
    print("Partitioning complete!")
    print(f"Output directory: {args.output_dir}")
    print(f"{'='*60}\n")

    return 0


if __name__ == "__main__":
    exit(main())




