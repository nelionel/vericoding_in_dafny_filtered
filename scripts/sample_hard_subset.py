import os
import random
import shutil
import argparse
from pathlib import Path

def sample_problems(source_dir, target_dir, n=50):
    source_path = Path(source_dir)
    target_path = Path(target_dir)
    
    files_dir = source_path / "files"
    if not files_dir.exists():
        print(f"Error: {files_dir} does not exist")
        return

    # Filter for specs files
    all_problems = [f for f in files_dir.iterdir() if f.is_file() and f.name.endswith("_specs.dfy")]
    
    if len(all_problems) < n:
        print(f"Warning: Only {len(all_problems)} problems found, taking all.")
        selected = all_problems
    else:
        selected = random.sample(all_problems, n)
        
    print(f"Selected {len(selected)} problems.")
    
    # Create target structure
    target_files_dir = target_path / "files"
    target_files_dir.mkdir(parents=True, exist_ok=True)
    
    # Copy files
    for prob in selected:
        shutil.copy(prob, target_files_dir / prob.name)
        
    # Copy metadata.json if it exists in source root
    meta_src = source_path / "metadata.json"
    if meta_src.exists():
        shutil.copy(meta_src, target_path / "metadata.json")
        
    print(f"Created subset in {target_path}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--seed", type=int, default=42)
    args = parser.parse_args()
    
    random.seed(args.seed)
    sample_problems(args.source, args.target)
