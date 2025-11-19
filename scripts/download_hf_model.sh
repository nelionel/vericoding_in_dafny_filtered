#!/usr/bin/env bash
set -euo pipefail

# Download a full Hugging Face model repo into a configurable models directory.
# Usage:
#   ./scripts/download_hf_model.sh openai/gpt-oss-20b
#   MODELS_DIR=/data/models ./scripts/download_hf_model.sh openai/gpt-oss-20b

DEFAULT_MODELS_DIR="${VERICODING_MODELS_DIR:-${XDG_DATA_HOME:-$HOME/.local/share}/vericoding_models}"
MODELS_DIR="${MODELS_DIR:-$DEFAULT_MODELS_DIR}"
MODEL_ID="${1:-openai/gpt-oss-20b}"

mkdir -p "$MODELS_DIR"

echo "[download_hf_model] Downloading ${MODEL_ID} into ${MODELS_DIR}"

export MODEL_ID
export MODELS_DIR
export HF_HUB_ENABLE_HF_TRANSFER=1 

# Install hf_transfer if possible for speed
pip install hf_transfer > /dev/null 2>&1 || true

python - <<'PY'
import os
import logging
import sys
from pathlib import Path
from huggingface_hub import snapshot_download

# Configure verbose logging
logging.basicConfig(level=logging.INFO)

model_id = os.environ["MODEL_ID"]
target_dir = Path(os.environ["MODELS_DIR"])
cache_dir = target_dir / ".hf_cache"

print(f"Starting download of {model_id}...")
print(f"Target directory: {target_dir}")
print(f"Cache directory: {cache_dir}")

try:
    snapshot_download(
        repo_id=model_id,
        local_dir=target_dir / model_id.replace("/", "__"),
        local_dir_use_symlinks=False,
        cache_dir=cache_dir,
        resume_download=True,
    )
    print("Download completed successfully.")
except Exception as e:
    print(f"Error during download: {e}")
    sys.exit(1)
PY
