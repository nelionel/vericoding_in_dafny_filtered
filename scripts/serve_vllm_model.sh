#!/usr/bin/env bash
set -euo pipefail

# Simple helper to launch a local vLLM OpenAI-compatible server for any HF model.
# Usage:
#   ./scripts/serve_vllm_model.sh openai/gpt-oss-20b --max-model-len 4096
# Set VERICODING_MODELS_DIR (or MODELS_DIR) to your local cache directory if you
# want the script to auto-resolve repo IDs to on-disk paths.

REQUESTED_MODEL="${1:-openai/gpt-oss-20b}"
shift || true

HOST="${VLLM_HOST:-0.0.0.0}"
PORT="${VLLM_PORT:-8000}"

# Hugging Face's fast downloader requires the hf_transfer package.
# Disable it by default so collaborators don't need extra installs.
export HF_HUB_ENABLE_HF_TRANSFER="${HF_HUB_ENABLE_HF_TRANSFER:-0}"

LOCAL_MODELS_DIR="${VERICODING_MODELS_DIR:-${MODELS_DIR:-}}"
MODEL="$REQUESTED_MODEL"
if [ -n "$LOCAL_MODELS_DIR" ]; then
  candidate="$LOCAL_MODELS_DIR/${REQUESTED_MODEL//\//__}"
  if [ -d "$candidate" ]; then
    MODEL="$candidate"
  fi
fi

echo "[serve_vllm_model] Starting vLLM server for ${MODEL} on ${HOST}:${PORT}"
echo "[serve_vllm_model] Additional vLLM args: $*"

exec vllm serve "${MODEL}" \
  --host "${HOST}" \
  --port "${PORT}" \
  "$@"

