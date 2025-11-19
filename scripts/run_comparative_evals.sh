#!/bin/bash
set -e

# Configuration
DATASET_DIR="/workspace/vericoding_in_dafny_filtered/hard_subset/random_50_eval"
MODEL_NAME="qwen3-30b-a3b-thinking-2507" # For OpenRouter
LOCAL_MODEL_NAME="qwen3-30b-thinking" # Alias for vLLM
VLLM_URL="http://localhost:8000/v1"
LOG_DIR="logs/comparative_evals"

mkdir -p "$LOG_DIR"

echo "=== Starting Comparative Evals ==="
date

# 1. OpenRouter + clean_eval
echo "--- Run 1: OpenRouter + clean_eval ---"
# Requires OPENROUTER_API_KEY
# python -m clean_eval.cli \
#   --tasks-dir "$DATASET_DIR" \
#   --models "$MODEL_NAME" \
#   --backend openrouter \
#   --limit 50 \
#   --output-dir eval_results/run1_openrouter_clean \
#   --verbose > "$LOG_DIR/run1.log" 2>&1

# 2. Local vLLM + clean_eval
echo "--- Run 2: Local vLLM + clean_eval ---"
# Requires vLLM server running
# python -m clean_eval.cli \
#   --tasks-dir "$DATASET_DIR" \
#   --models "$LOCAL_MODEL_NAME" \
#   --backend vllm \
#   --vllm-base-url "$VLLM_URL" \
#   --limit 50 \
#   --output-dir eval_results/run2_local_clean \
#   --verbose > "$LOG_DIR/run2.log" 2>&1

# 3. OpenRouter + vericoder.py
echo "--- Run 3: OpenRouter + vericoder.py ---"
# python /workspace/vericoding/src/vericoder.py dafny "$DATASET_DIR" \
#   --llm "$MODEL_NAME" \
#   --limit 50 \
#   --iterations 1 \
#   --output-root eval_results/run3_openrouter_vericoder \
#   > "$LOG_DIR/run3.log" 2>&1

# 4. Local vLLM + vericoder.py
echo "--- Run 4: Local vLLM + vericoder.py ---"
# python /workspace/vericoding/src/vericoder.py dafny "$DATASET_DIR" \
#   --llm "$LOCAL_MODEL_NAME" \
#   --base-url "$VLLM_URL" \
#   --limit 50 \
#   --iterations 1 \
#   --output-root eval_results/run4_local_vericoder \
#   > "$LOG_DIR/run4.log" 2>&1

echo "=== All runs completed ==="
date



