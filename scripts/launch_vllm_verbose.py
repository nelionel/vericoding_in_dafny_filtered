import subprocess
import sys
import os
import time
import select
import torch

def estimate_memory(model_config_path, quantization="bitsandbytes", max_seq_len=32768, gpu_mem_gb=32):
    # Rough estimation of memory usage
    # 30B params * 0.5 bytes (4-bit) = 15GB for weights
    # KV cache: 2 * n_layers * n_heads * head_dim * max_seq_len * batch_size * 2 (bytes/fp16)
    # Qwen3-30B: 64 layers (est), 32 heads (est), 128 dim (est)
    # Let's assume 15GB model + 2GB buffer + KV cache
    
    # We need to leave space for KV cache to support concurrency.
    # 80GB A100/H100 is huge, but 32GB is tight.
    
    # Actually we will just let vLLM handle it, but we need to set max-model-len high enough.
    pass

def main():
    # Configuration
    model_path = "Qwen/Qwen3-30B-A3B-Thinking-2507"
    
    # Qwen supports 262144 (256k).
    # However, on a single 32GB GPU with 30B params (4-bit), we are limited by VRAM.
    # Model takes ~17GB. Available for KV: ~14GB.
    # KV Cache (approx): ~0.25MB per token.
    # Max total tokens capacity ~= 14000MB / 0.25MB = 56,000 tokens.
    # If we set max-model-len to 32768, we can fit roughly 1 full context + some small ones.
    # If we set it to 100k, we might OOM instantly if it pre-allocates, or support <1 req.
    # vLLM manages blocks dynamically, but max-model-len restricts the max allowed.
    # Let's try 32768 (32k) as a reasonable "long" context that fits.
    
    cmd = [
        "vllm", "serve", model_path,
        "--host", "0.0.0.0",
        "--port", "8000",
        "--max-model-len", "32768",
        "--gpu-memory-utilization", "0.98", # Push usage to max
        "--quantization", "bitsandbytes",
        "--enforce-eager",
        "--max-num-seqs", "10", # Allow some concurrency if seqs are short
        "--max-num-batched-tokens", "32768" # Limit batch size to one full context equivalent
    ]
    
    env = os.environ.copy()
    env["VLLM_USE_V1"] = "0" # Force V0 engine
    
    models_dir = env.get("MODELS_DIR", "/workspace/models")
    resolved_path = os.path.join(models_dir, model_path.replace("/", "__"))
    if os.path.exists(resolved_path):
        cmd[2] = resolved_path
        print(f"Resolved model path: {resolved_path}")
    else:
        print(f"Warning: Could not find model at {resolved_path}, letting vLLM try to find it...")

    print(f"Starting vLLM: {' '.join(cmd)}")
    
    process = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        env=env,
        universal_newlines=True,
        bufsize=1
    )

    print("--- vLLM Output ---")
    try:
        while True:
            line = process.stdout.readline()
            if not line and process.poll() is not None:
                break
            if line:
                print(line.strip())
                # Check for success message
                if "Application startup complete" in line:
                    print("\n>>> Server is ready! <<<")
    except KeyboardInterrupt:
        print("\nStopping server...")
        process.terminate()
        process.wait()
        print("Server stopped.")

if __name__ == "__main__":
    main()
