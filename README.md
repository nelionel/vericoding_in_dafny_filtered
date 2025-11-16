# VeriCoding Clean Dafny Evals

Self-contained harness for benchmarking LLMs on the VeriCoding Dafny hard subset.
It vendors the minimal pieces of the upstream evaluation pipeline, the curated
tasks (`hard_subset/dafny_flat`), and a slim CLI designed for reproducible runs
on OpenRouter or a local vLLM server.

## Repository layout

| Path | Purpose |
| --- | --- |
| `src/vericoding` | Vendored core/processing/utils modules from the upstream project |
| `src/clean_eval` | New CLI + backend glue (`clean_eval.cli`) |
| `hard_subset/dafny_flat` | 1,149 filtered Dafny specs plus metadata/README |
| `hard_subset/raw_data` | Snapshot of the full Dafny benchmark (all `.dfy` specs, `dafny_tasks.jsonl`, CSV aggregates) |
| `hard_subset/filter_engine` | Original filtering scripts/docs so you can regenerate the subset locally |
| `eval_results/` | Created automatically for run artifacts |
| `requirements.txt` | Minimal dependency set |
| `env.template` | Copy to `.env` and fill in API keys |

## Setup

```bash
cd /path/to/vericoding_clean_dafny_evals
python -m venv .venv            # once
source .venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
cp env.template .env            # fill in OPENROUTER_API_KEY, etc.
set -a && source .env && set +a # or use direnv/asdf to load env vars
export PYTHONPATH="$PWD/src"    # add to your shell profile for convenience
```

Fill in the `.env` file with your API keys **and** Dafny locations:

- `DAFNY_HOME` should point to the directory that contains the bundled `dafny/`
  folder (the binary will be at `$DAFNY_HOME/dafny/dafny`).
- Alternatively set `DAFNY_PATH` to the exact Dafny executable.

### Dafny toolchain

The verifier reads whichever of `DAFNY_PATH` or `DAFNY_HOME` you define—there are
no baked-in workspace paths. Typical workflows:

1. **Already installed Dafny** (e.g. `/opt/dafny` or `~/tools/dafny`): set
   `DAFNY_HOME=/path/to/your/dafny` in `.env`, reload the file, and confirm with
   `dafny --version`.
2. **Fresh install**: run the helper and choose your own install directory/env
   file.

```bash
source .venv/bin/activate
bash scripts/install_dafny.sh \
  --install-root /path/you/control \
  --env-file /path/to/.dafny_env
source /path/to/.dafny_env              # exports DAFNY_HOME/DAFNY_PATH and updates PATH
dafny --version
```

### Local model cache (optional)

If you need to download Hugging Face checkpoints for offline use, define a
directory outside the repo and export `VERICODING_MODELS_DIR` (or pass
`MODELS_DIR=...` per command invocation).  For example:

```bash
export VERICODING_MODELS_DIR="$HOME/.cache/vericoding_models"
./scripts/download_hf_model.sh openai/gpt-oss-20b
./scripts/serve_vllm_model.sh "$VERICODING_MODELS_DIR/openai__gpt-oss-20b"
```

When `VERICODING_MODELS_DIR` is set, `serve_vllm_model.sh` automatically rewrites
repo IDs (e.g., `openai/gpt-oss-20b`) to the corresponding local path if it
exists.

## Running evaluations

Basic smoke test (20 tasks, default models `claude-haiku` and `qwen3-30b-thinking`):

```bash
python -m clean_eval.cli \
  --limit 20 \
  --wandb-mode disabled
```

Full hard subset:

```bash
python -m clean_eval.cli --eval-all --models claude-4.5-sonnet
```

Hard-only preset (difficulty ≥3 or unsolved historically):

```bash
python -m clean_eval.cli --eval-hardest --hardest-count 150
```

Switch to a local vLLM server (OpenAI-compatible endpoint):

```bash
python -m clean_eval.cli \
  --backend vllm \
  --vllm-base-url http://localhost:8000/v1 \
  --models qwen2.5-coder
```

Key flags:

- `--eval-all`: ignore `--limit`, run every task in metadata.
- `--eval-hardest`: filter to difficult/unsolved tasks (tunable via `--hardest-count`).
- `--sources`: restrict to one or more benchmark sources (e.g. `apps`, `bignum`).
- `--min-difficulty/--max-difficulty`, `--min-models-passed/--max-models-passed`:
  additional metadata filters.
- `--backend {openrouter,vllm}` and the `--vllm-*` options select providers.
- `--dry-run`: inspect which tasks would run without consuming credits.

Each model run gets its own timestamped folder under `eval_results/` with:

- `summary.txt` – textual aggregate report
- `results.csv` – per-task success table plus optional GitHub links
- `_impl.dfy` files – LLM completions that verified successfully
- optional `debug/` artifacts when `--verbose` is set

## Extending / testing

- The vendored modules remain untouched except for two small hooks:
  - `vericoding/utils/git_utils.py` now suppresses warnings unless
    `VERICODING_SHOW_GIT_WARN=1`.
  - `vericoding/processing/file_processor.py` accepts an optional
    `llm_provider_factory`, enabling backend injection.
- The raw benchmark inputs are available for reproducibility:
  - `hard_subset/raw_data/dafny_specs/` – every upstream `.dfy` spec.
  - `hard_subset/raw_data/dafny_tasks.jsonl` – metadata used to filter tasks.
  - `hard_subset/raw_data/vericoding_benchmark_v1.csv` / `vericoding_results_v1.csv` – aggregate CSVs from the original release.
  - `hard_subset/filter_engine/scripts/` – copies of the hard subset creator, flat-folder builder, and analysis helpers. `hard_subset/filter_engine/README.md` walks through regenerating outputs.
- Unit tests are not included yet, but you can exercise the harness by running
  short limits (`--limit 2 --verbose`) and verifying that Dafny validations pass.
- Future work: add pytest smoke tests that mock the LLM provider and Dafny CLI
  to keep regressions from creeping in.

## Licensing / attribution

The upstream VeriCoding repository is MIT-licensed.  This repo preserves the
license headers in the vendored files and is intended solely for evaluation
research on the existing benchmark.  Please keep attribution intact when
publishing results.

