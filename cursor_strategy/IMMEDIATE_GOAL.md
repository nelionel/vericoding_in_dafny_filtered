CURRENT IMMEDIATE GOAL:
Make the canonical `vericoder.py` write its artifacts under `eval_results/` by default (with a flexible path) and expose a CLI/config option so users can override the destination.

Acceptance criteria:
- Introduce a configuration/CLI flag (e.g., `--output-dir` or `--output-root`) that controls where per-run folders are created.
- Default the new option to `eval_results` relative to the repo (no hard-coded `/workspace`), while keeping backward-compatible layout otherwise.
- Update docs/state to describe the new behavior and remind users how to override it.
