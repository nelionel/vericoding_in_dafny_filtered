# Harness Comparison Notes

## Dataset & Task Selection
- `clean_eval` filters to the “hard subset” (difficulty ≥3 or unsolved) before applying `--limit`, so even the first few files are the `DB****`/`DT****` benchmarks.  
```46:117:vericoding_in_dafny_filtered/src/clean_eval/cli.py
def select_tasks(...):
    if args.eval_hardest:
        hardest = [
            (fname, data)
            for fname, data in items
            if data.get("difficulty", 0) >= 3 or data.get("models_passed", 99) <= 1
        ]
        ...
        selected = [fname for fname, _ in hardest][: args.hardest_count]
```
- The upstream `vericoder.py` simply walks the folder that the user passes (`--folder /workspace/vericoding-benchmark/specs`) with no difficulty filter, so my Claude control run sampled the easier `DA00xx` specs.  
```201:293:vericoding/src/vericoder.py
def setup_configuration(args):
    files_dir = str(args.folder)
    ...
    config = ProcessingConfig(
        ...
        files_dir=files_dir,
        max_iterations=args.iterations,
        ...
    )
```

## Placeholder Layout Presented to the Model
- Hard-subset files include explicit `<vc-code>`/`<vc-helpers>` stubs, which forces the LLM to emit **two JSON entries per spec**; this is where the count mismatch is tripping the clean harness.  
```1:54:vericoding_in_dafny_filtered/hard_subset/dafny_flat/files/DB0016_specs.dfy
// <vc-helpers>
// </vc-helpers>
...
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
```
- The benchmark specs fed to `vericoder.py` share the same tags, but the harness isn’t filtering to only the hardest ones, so the model rarely exhausts its JSON entries (and the easier specs finish in fewer iterations).  
```1:50:vericoding-benchmark/specs/DA0000_specs.dfy
// <vc-helpers>
// </vc-helpers>
...
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
```

## JSON Extraction & Failure Mode
- Both harnesses call `apply_json_replacements`, but the clean evaluator’s metadata guarantees there are always 2 placeholders. As soon as Claude emits a single string (e.g., slips extra prose), the strict count check trips and the run retries the whole prompt, burning time.  
```73:193:vericoding_in_dafny_filtered/src/vericoding/processing/code_fixer.py
expected_count = len(vc_code_matches) + len(vc_helpers_matches)
...
if len(replacements) != expected_count:
    error = f"JSON replacement count mismatch: Expected {expected_count} replacements ... got {len(replacements)}"
    return original_code, error
```
- The log from the verbose mini-run shows this happening immediately on DB0022: “JSON replacement count mismatch: Expected 2 replacements… got 1”, which cascades into retries and extra API calls.

## Iteration Count & Verification Cost
- Clean harness default is `--max-iterations 5` plus a 60 s verification timeout. With the hard subset, Dafny frequently hits the 30 s timeout inside lemmas (example below), so each spec can easily burn ~3–4 minutes even with rate limiter utilization at only 1 %.  
```220:239:vericoding_in_dafny_filtered/src/clean_eval/cli.py
parser.add_argument(
    "--max-iterations",
    type=int,
    default=int(os.getenv("MAX_ITERATIONS", "5")),
    help="Maximum retry iterations per task",
)
parser.add_argument(
    "--timeout",
    type=int,
    default=int(os.getenv("VERIFICATION_TIMEOUT", "60")),
    help="Verification timeout in seconds",
)
```
- Example timeout captured in `/eval_results/claude-4.5-sonnet_1/debug/DB0027_specs_iter4_error.log`:  
```7:28:vericoding_in_dafny_filtered/eval_results/claude-4.5-sonnet_1/debug/DB0027_specs_iter4_error.log
Compilation failed: ... ModMulProperty' timed out after 30 seconds ...
eval_results/.../DB0027_specs_impl.dfy(111,0): Error: a postcondition could not be proved ...
```
- `vericoder.py` run used `--iterations 3` and the easier `DA` tasks, so each spec rarely hit the timeout cliff; overall elapsed time for 50 tasks was ~9.7 minutes versus ~25+ minutes projected for the hard subset.

## Clean evaluator vs. classic harness (Claude 4.5)

- **`clean_eval`, flat slice (no hardest filter):**  
  `python -m clean_eval.cli --tasks-dir /workspace/vericoding_in_dafny_filtered/hard_subset/dafny_flat --limit 50 --models claude-4.5-sonnet --backend openrouter --max-iterations 3`  
  achieved 29/50 passes (58 %).  
```13:16:vericoding_in_dafny_filtered/eval_results/claude-4.5-sonnet_3/summary.txt
Total successful: 29
Total failed: 21
Success rate: 58.0%
```

- **`clean_eval`, `--eval-hardest` (difficulty ≥ 3):**  
  `python -m clean_eval.cli --tasks-dir /workspace/vericoding_in_dafny_filtered/hard_subset/dafny_flat --eval-hardest --limit 50 --models claude-4.5-sonnet --backend openrouter --max-iterations 3`  
  fell back to 0/50.  
```13:16:vericoding_in_dafny_filtered/eval_results/claude-4.5-sonnet_4/summary.txt
Total successful: 0
Total failed: 50
Success rate: 0.0%
```

- **`vericoder.py` on the same hard slice:**  
  `python vericoding/src/vericoder.py dafny /workspace/vericoding_in_dafny_filtered/hard_subset/dafny_flat/files --llm claude-4.5-sonnet --limit 50 --iterations 3 --workers 4 --api-rate-limit-delay 0 --no-wandb`  
  recovered 22/50 passes (44 %).  
```13:16:vericoding_in_dafny_filtered/hard_subset/dafny_flat/vericoder_claude-4.5-sonnet_17-11_19h01/summary.txt
Total successful: 22
Total failed: 28
Success rate: 44.0%
```

- **`clean_eval` on the original “easy 50” control set:** recreating `/workspace/tmp_vericoder50` and reusing the same command/flags gives 35/50 (70 %), matching the upstream baseline.  
```1:20:vericoding_in_dafny_filtered/eval_results/claude-4.5-sonnet_2/summary.txt
Total successful: 35
Total failed: 15
Success rate: 70.0%
```

## Historical benchmark context

- Parsing `vericoding-benchmark/vericoding_results_v1.csv` for Dafny tasks with `difficulty ≥ 3` (81 total) yields pass rates in the 30–35 % range for the strongest hosted models (Claude Sonnet/Opus, GPT-5-mini), which aligns with the `vericoder.py` run but is far above the 0 % we currently see from `clean_eval` on the same slice.

