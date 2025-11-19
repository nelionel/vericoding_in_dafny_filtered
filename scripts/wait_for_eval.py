#!/usr/bin/env python3
"""
Wait for evaluation to complete and show summary.
"""
import time
import json
from pathlib import Path
import sys

def wait_for_completion(output_dir, check_interval=10):
    """Wait for evaluation to complete by monitoring the results file."""
    output_path = Path(output_dir)
    results_file = None
    
    # Find the results directory (qwen3-30b-thinking_N)
    while True:
        candidates = list(output_path.glob("qwen3-30b-thinking_*/summary.txt"))
        if candidates:
            results_file = candidates[-1]  # Get latest
            break
        print(f"Waiting for results directory to appear in {output_dir}...")
        time.sleep(check_interval)
    
    results_dir = results_file.parent
    print(f"Monitoring: {results_dir}")
    
    # Wait for summary.txt to stop changing (evaluation complete)
    last_mtime = 0
    stable_count = 0
    
    while stable_count < 3:  # Wait for 3 consecutive checks with no change
        if results_file.exists():
            current_mtime = results_file.stat().st_mtime
            if current_mtime == last_mtime:
                stable_count += 1
            else:
                stable_count = 0
                last_mtime = current_mtime
                
                # Print current status
                with open(results_file) as f:
                    lines = f.readlines()
                    for line in lines:
                        if "Success rate:" in line or "Total successful:" in line or "Total failed:" in line:
                            print(line.strip())
        
        time.sleep(check_interval)
    
    print("\n" + "=" * 80)
    print("EVALUATION COMPLETE!")
    print("=" * 80)
    
    # Print final summary
    with open(results_file) as f:
        print(f.read())
    
    # Check for CSV
    csv_file = results_dir / "results.csv"
    if csv_file.exists():
        print(f"\nResults CSV: {csv_file}")

if __name__ == "__main__":
    output_dir = sys.argv[1] if len(sys.argv) > 1 else "eval_results/run1_openrouter_qwen_clean"
    wait_for_completion(output_dir)


