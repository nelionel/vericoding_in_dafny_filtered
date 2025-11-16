# Hard Subset Assets

Everything under `hard_subset/` is self-contained so you can regenerate the
filtered Dafny tasks or inspect the original benchmark without pulling the
upstream repos again.

| Path | Description |
| --- | --- |
| `dafny_flat/` | Ready-to-run hard subset (1,149 specs, metadata, difficulty plot). This is what the evaluator consumes by default. |
| `raw_data/` | Snapshot of the upstream VeriCoding benchmark: full `.dfy` specs, `jsonl/dafny_tasks.jsonl`, aggregate CSVs, and the original `vericoding-benchmark/` tree. |
| `filter_engine/` | The quality-check + filtering scripts, analysis notebooks, and summary markdown copied from the upstream `Vericoding_Dafny_filtered` repo. |

## Regenerating the hard subset

1. **Quality check (optional)**  
   Produces `results/dafny_quality_results.jsonl` with faithfulness/leakage/difficulty
   scores using Claude Sonnet 4.5:

   ```bash
   cd hard_subset/filter_engine/scripts/pipeline
   python quality_check_benchmark.py \
     --benchmark-dir ../../raw_data/vericoding-benchmark \
     --output-dir ../../filter_engine/results
   ```

   (You can skip this if you trust the bundled `results/dafny_quality_results.jsonl`.)

2. **Create the filtered ID / metadata set**  
   Filters the quality results and writes JSON/markdown under
   `filter_engine/outputs/hard_subsets_dafny/`:

   ```bash
   python create_hard_subsets.py \
     --results-file ../../filter_engine/results/dafny_quality_results.jsonl \
     --output-dir ../../filter_engine/outputs/hard_subsets_dafny
   ```

3. **Build the flat folder**  
   Copies the relevant `.dfy` specs, attaches metadata, and emits the difficulty
   plot + README in `dafny_flat/`:

   ```bash
   python create_hard_subset_flat.py \
     --ratings-jsonl ../../filter_engine/outputs/hard_subsets_dafny/hard_subset_results.jsonl \
     --results-csv ../../raw_data/vericoding_results_v1.csv \
     --benchmark-dir ../../raw_data/vericoding-benchmark \
     --output-dir ../../dafny_flat
   ```

## Analysis scripts

Exploratory utilities live in `filter_engine/scripts/analysis/` (pass rate
breakdowns, APPS-only comparisons, etc.). They expect the same `raw_data/` and
`filter_engine/outputs/` paths, so you can reuse them without editing hardcoded
paths.

Feel free to drop additional notebooks or regenerated artifacts in this folder—
the rest of the repository only depends on `dafny_flat/`.

