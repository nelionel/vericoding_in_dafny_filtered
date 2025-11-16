# Hard Subset Filter Engine

This folder preserves the original tooling that produced the Dafny hard subset
distributed in `hard_subset/dafny_flat`.

## Layout

| Path | Description |
| --- | --- |
| `scripts/pipeline/` | Core generation scripts: `quality_check_benchmark.py`, `create_hard_subsets.py`, `create_hard_subset_flat.py`. Defaults now point at `../raw_data` and `../outputs`. |
| `scripts/analysis/` | Optional diagnostics/visualizations (model comparisons, source breakdowns, etc.). |
| `hard_subset_summary.md` | Narrative description of the filtering criteria and benchmark breakdown. |
| `model_performance_summary.md` | Aggregate success rates for common models on the filtered set. |
| `performance_by_benchmark.md` | Pass-rate breakdown per source benchmark. |

## Usage

1. **Input data** lives under `hard_subset/raw_data/`:
   - `dafny_specs/` – all upstream `.dfy` specs copied from the original benchmark
   - `dafny_tasks.jsonl` – task metadata (IDs, sources, descriptions)
   - optional CSVs for the full benchmark (`vericoding_benchmark_v1.csv`, `vericoding_results_v1.csv`)
2. Run the filtering scripts from within this project’s virtual environment; they
   expect paths relative to `hard_subset/raw_data`. For example:

```bash
cd /path/to/vericoding_clean_dafny_evals/hard_subset/filter_engine/scripts/pipeline
python create_hard_subsets.py \
  --results-file ../../results/dafny_quality_results.jsonl \
  --output-dir ../../outputs/hard_subsets_dafny
```

3. Regenerate the flat folder + metadata (mirrors what already exists in
   `hard_subset/dafny_flat/`) using:

```bash
python create_hard_subset_flat.py \
  --ratings-jsonl ../../outputs/hard_subsets_dafny/hard_subset_results.jsonl \
  --results-csv ../../raw_data/vericoding_results_v1.csv \
  --benchmark-dir ../../raw_data/vericoding-benchmark \
  --output-dir ../../dafny_flat
```

Feel free to edit the scripts or add new ones; the copies here are purely local
so the repository stays self-contained.

