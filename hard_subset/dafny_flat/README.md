# Hard Subset - Flat Structure

This folder contains 1149 high-quality, challenging Dafny verification tasks.

## Filter Criteria

- **Spec Faithfulness**: ≥ 2 (faithful specs)
- **Spec Leakage**: ≤ 1 (low leakage)
- **Difficulty**: ≥ 1 (non-trivial)

## Folder Structure

```
hard_subset_flat/
├── files/                      # 1149 specification files
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
jq 'group_by(.value.source) | map({source: .[0].value.source, count: length})' metadata.json
```

## Correlation Analysis

The `difficulty_vs_models.png` plot shows the relationship between:
- **X-axis**: LLM-rated difficulty
- **Y-axis**: Average number of models that passed

Expected: Higher difficulty → Fewer models pass (negative correlation)
