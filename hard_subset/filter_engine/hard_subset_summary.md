# Hard Subsets - High-Quality Challenging Problems

## Filter Criteria

- **Spec Faithfulness**: ≥ 2 (faithful specs)
- **Spec Leakage**: ≤ 1 (low leakage - spec doesn't reveal implementation)
- **Difficulty**: ≥ 1 (non-trivial problems)

## Summary

**Total Original**: 2334 tasks  
**Total Filtered**: 1149 tasks (49.2%)

## By Benchmark

| Benchmark | Total Tasks | Passed All Criteria | Percentage |
|-----------|-------------|---------------------|------------|
| numpy_triple | 603 | 309 | 51.2% |
| dafnybench | 443 | 294 | 66.4% |
| apps | 677 | 196 | 29.0% |
| humaneval | 162 | 102 | 63.0% |
| verina | 157 | 96 | 61.1% |
| verified_cogen | 172 | 76 | 44.2% |
| bignum | 62 | 50 | 80.6% |
| numpy_simple | 58 | 26 | 44.8% |

## Individual Criteria

| Benchmark | Faith ≥ 2 | Leak ≤ 1 | Diff ≥ 1 |
|-----------|-----------|----------|----------|
| numpy_triple | 566 | 406 | 433 |
| dafnybench | 371 | 376 | 373 |
| apps | 550 | 278 | 543 |
| humaneval | 138 | 125 | 146 |
| verina | 125 | 146 | 128 |
| verified_cogen | 103 | 141 | 104 |
| bignum | 62 | 50 | 61 |
| numpy_simple | 43 | 46 | 44 |

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
jq '.by_benchmark | to_entries[] | "\(.key): \(.value | length)"' hard_subset_ids.json

# Get all hard subset task IDs
jq -r '.task_ids[]' hard_subset_ids.json

# Get hard subset for specific benchmark
jq -r '.by_benchmark.apps[]' hard_subset_ids.json
```
