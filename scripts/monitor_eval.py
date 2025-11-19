#!/usr/bin/env python3
"""Monitor evaluation progress and display status."""
import sys
import time
from pathlib import Path

def monitor_log(log_path, interval=10):
    """Monitor log file and print status updates."""
    print(f"Monitoring: {log_path}")
    print("=" * 80)
    
    if not Path(log_path).exists():
        print(f"Waiting for log file to appear...")
        while not Path(log_path).exists():
            time.sleep(1)
    
    with open(log_path, 'r') as f:
        # Seek to end
        f.seek(0, 2)
        
        while True:
            line = f.readline()
            if not line:
                time.sleep(0.5)
                continue
            
            line = line.strip()
            # Print progress lines and key events
            if any(keyword in line for keyword in [
                'Progress:', '✓', '✗', 'Complete:', 'Rate limiter:', 
                'Success rate:', 'Evaluating', 'tasks with'
            ]):
                print(line)
                sys.stdout.flush()

if __name__ == "__main__":
    log_path = sys.argv[1] if len(sys.argv) > 1 else "logs/eval1_openrouter_qwen_full.log"
    try:
        monitor_log(log_path)
    except KeyboardInterrupt:
        print("\nMonitoring stopped.")



