# Model Performance on Hard Subset

## Hard Subset Criteria
- **Spec Faithfulness**: ≥ 2
- **Spec Leakage**: ≤ 1  
- **Difficulty**: ≥ 1

## Performance Comparison

| Model | Overall Pass Rate | Hard Subset Pass Rate | Difference |
|-------|-------------------|----------------------|------------|
| claude-sonnet-4 | 83.1% | 75.3% | -7.9% |
| claude-opus-4.1 | 82.7% | 74.8% | -7.9% |
| gpt-5-mini | 80.4% | 72.0% | -8.4% |
| gpt-5 | 76.6% | 66.8% | -9.9% |
| grok-code | 75.6% | 66.4% | -9.2% |
| deepseek-chat-v3.1 | 72.4% | 61.9% | -10.5% |
| gemini-2.5-pro | 68.7% | 58.5% | -10.2% |
| gemini-2.5-flash | 49.1% | 44.6% | -4.5% |
| glm-4.5 | 29.6% | 29.1% | -0.6% |


## Key Insights

### Best Performing Models (Hard Subset)
1. **claude-sonnet-4**: 75.3% (727/966)
2. **claude-opus-4.1**: 74.8% (651/870)
3. **gpt-5-mini**: 72.0% (696/966)
4. **gpt-5**: 66.8% (645/966)
5. **grok-code**: 66.4% (641/966)

### Observations

- Models typically perform **worse** on the hard subset (higher quality, more challenging tasks)
- The difference column shows how much harder the hard subset is for each model
- Negative differences indicate the model struggles more with high-quality, low-leakage tasks
