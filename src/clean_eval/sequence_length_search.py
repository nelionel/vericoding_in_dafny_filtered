"""Binary search helper to find minimal vLLM max_tokens that yields JSON output."""

from __future__ import annotations

import argparse
import json
import os
import sys
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timezone
from pathlib import Path
from time import time
from types import SimpleNamespace
from typing import Any

from clean_eval.cli import (
    DEFAULT_OUTPUT_DIR,
    DEFAULT_TASKS_DIR,
    configure_logging,
    ensure_env_loaded,
    load_hard_subset_metadata,
    run_for_model,
    select_tasks,
)


class Tee:
    """Fan-out writes to multiple streams (e.g., console + log file)."""

    def __init__(self, *streams):
        self.streams = streams

    def write(self, data: str) -> None:
        for stream in self.streams:
            stream.write(data)

    def flush(self) -> None:
        for stream in self.streams:
            stream.flush()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Binary-search the minimal --vllm-max-tokens that still yields JSON output.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    parser.add_argument(
        "--model-alias",
        default="qwen3-30b-a3b-thinking-100k",
        help="Logical model alias defined in providers.py",
    )
    parser.add_argument(
        "--backend",
        choices=["vllm"],
        default="vllm",
        help="Backend to probe (currently only vLLM supported)",
    )
    parser.add_argument(
        "--vllm-base-url",
        default=os.getenv("VLLM_BASE_URL", "http://localhost:8000/v1"),
        help="Base URL for the local vLLM server",
    )
    parser.add_argument(
        "--vllm-api-key",
        default=os.getenv("VLLM_API_KEY", "dummy"),
        help="API key forwarded to vLLM (if required)",
    )
    parser.add_argument(
        "--vllm-request-timeout",
        type=float,
        default=float(os.getenv("VLLM_REQUEST_TIMEOUT", "600")),
        help="Per-request timeout window (seconds)",
    )
    parser.add_argument(
        "--tasks-dir",
        type=Path,
        default=DEFAULT_TASKS_DIR,
        help="Directory containing metadata.json and files/",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=3,
        help="Number of tasks to probe (ignored if --eval-all)",
    )
    parser.add_argument(
        "--eval-all",
        action="store_true",
        help="Ignore --limit and run every task in metadata",
    )
    parser.add_argument(
        "--eval-hardest",
        action="store_true",
        help="Filter to the hardest tasks (difficulty>=3 or unsolved)",
    )
    parser.add_argument(
        "--hardest-count",
        type=int,
        default=200,
        help="Number of hardest tasks to consider before applying --limit",
    )
    parser.add_argument("--sources", nargs="+", help="Restrict to specific source tags")
    parser.add_argument(
        "--min-difficulty",
        type=int,
        choices=[0, 1, 2, 3],
        help="Minimum difficulty filter",
    )
    parser.add_argument(
        "--max-difficulty",
        type=int,
        choices=[0, 1, 2, 3],
        help="Maximum difficulty filter",
    )
    parser.add_argument(
        "--min-models-passed",
        type=int,
        help="Minimum historical pass count filter",
    )
    parser.add_argument(
        "--max-models-passed",
        type=int,
        help="Maximum historical pass count filter",
    )

    parser.add_argument(
        "--min-tokens",
        type=int,
        required=True,
        help="Lower bound for --vllm-max-tokens during search",
    )
    parser.add_argument(
        "--max-tokens",
        type=int,
        required=True,
        help="Upper bound for --vllm-max-tokens during search",
    )
    parser.add_argument(
        "--granularity",
        type=int,
        default=250,
        help="Token bucket granularity (search happens on multiples of this value)",
    )
    parser.add_argument(
        "--max-rounds",
        type=int,
        default=8,
        help="Maximum binary-search rounds (caps total evaluation runs)",
    )
    parser.add_argument(
        "--study-root",
        type=Path,
        help="Optional folder to store study artifacts; defaults to eval_results/sequence_length_study/<timestamp>",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable verbose logging for inner evaluations",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=int(os.getenv("MAX_ITERATIONS", "1")),
        help="Maximum iterations per task during probing",
    )
    parser.add_argument(
        "--max-concurrent-tasks",
        type=int,
        default=int(os.getenv("MAX_CONCURRENT_TASKS", "1")),
        help="Max concurrent tasks when using the async rate limiter",
    )
    parser.add_argument(
        "--parallel-workers",
        type=int,
        default=int(os.getenv("PARALLEL_WORKERS", "1")),
        help="Worker count when not using the async rate limiter",
    )
    parser.add_argument(
        "--rate-limit-rpm",
        type=int,
        default=int(os.getenv("RATE_LIMIT_RPM", "200")),
        help="Requests-per-minute budget when dynamic rate limiting is on",
    )
    parser.add_argument(
        "--use-dynamic-rate-limit",
        action="store_true",
        default=os.getenv("USE_DYNAMIC_RATE_LIMIT", "true").lower()
        in ("1", "true", "yes"),
        help="Enable the async rate limiter",
    )
    parser.add_argument(
        "--wandb-mode",
        choices=["online", "offline", "disabled"],
        default=os.getenv("WANDB_MODE", "disabled"),
        help="Control Weights & Biases logging behavior",
    )

    return parser.parse_args()


class SequenceLengthSearcher:
    def __init__(
        self,
        args: argparse.Namespace,
        files: list[Path],
        metadata: dict[str, dict],
    ):
        self.args = args
        self.files = files
        self.metadata = metadata
        self.console_out = sys.stdout
        self.console_err = sys.stderr

        timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d_%H%M%S")
        default_root = (
            DEFAULT_OUTPUT_DIR
            / "sequence_length_study"
            / f"{timestamp}_bisect_{args.model_alias}"
        )
        self.study_root = args.study_root or default_root
        self.study_root = self.study_root.resolve()
        self.study_root.mkdir(parents=True, exist_ok=True)

        self.history_path = self.study_root / "search_history.jsonl"
        self.summary_path = self.study_root / "summary.json"
        self.selected_specs = [path.name for path in files]
        self.history_entries: list[dict[str, Any]] = []

    def run(self) -> dict[str, Any]:
        step = self.args.granularity
        if step <= 0:
            raise SystemExit("--granularity must be positive")

        min_tokens = self.args.min_tokens
        max_tokens = self.args.max_tokens
        if min_tokens > max_tokens:
            raise SystemExit("--min-tokens must be <= --max-tokens")
        if min_tokens % step != 0 or max_tokens % step != 0:
            raise SystemExit("Bounds must be multiples of --granularity")

        lo = min_tokens // step
        hi = max_tokens // step
        evaluated: dict[int, bool] = {}
        best_record: dict[str, Any] | None = None
        round_idx = 1

        while lo <= hi and round_idx <= self.args.max_rounds:
            mid = (lo + hi) // 2
            candidate_tokens = mid * step

            if candidate_tokens in evaluated:
                # Already evaluated this bucket; break to avoid infinite loops.
                break

            record = self._run_single_trial(
                max_tokens=candidate_tokens,
                round_idx=round_idx,
            )
            evaluated[candidate_tokens] = record["json_success"]
            self.history_entries.append(record)
            self._append_history(record)

            if record["json_success"]:
                best_record = record
                hi = mid - 1
            else:
                lo = mid + 1

            round_idx += 1

        if best_record is None:
            raise SystemExit(
                "Binary search exhausted without finding a token cap that yields JSON output."
            )

        summary = {
            "model_alias": self.args.model_alias,
            "backend": self.args.backend,
            "min_tokens_requested": self.args.min_tokens,
            "max_tokens_requested": self.args.max_tokens,
            "granularity": step,
            "max_rounds": self.args.max_rounds,
            "total_rounds_executed": len(self.history_entries),
            "final_max_tokens": best_record["max_tokens"],
            "final_output_dir": best_record["output_dir"],
            "study_root": str(self.study_root),
            "history_file": str(self.history_path),
            "selected_specs": self.selected_specs,
        }

        with self.summary_path.open("w") as f:
            json.dump(summary, f, indent=2)

        print(
            f"\n✅ Binary search complete. "
            f"Minimum safe --vllm-max-tokens ≈ {best_record['max_tokens']}."
        )
        print(f"Summary file: {self.summary_path}")
        return summary

    def _run_single_trial(self, max_tokens: int, round_idx: int) -> dict[str, Any]:
        run_dir = self.study_root / f"mtok{max_tokens}"
        if run_dir.exists():
            run_dir = self.study_root / f"mtok{max_tokens}_round{round_idx}"
        run_dir.mkdir(parents=True, exist_ok=True)

        log_path = run_dir / "run.log"
        token_log_path = run_dir / "token_usage.csv"
        os.environ["VERICODING_TOKEN_LOG"] = str(token_log_path)

        eval_args = self._build_eval_args(max_tokens=max_tokens, output_dir=run_dir)

        start = time()
        with log_path.open("w") as log_file:
            tee_out = Tee(self.console_out, log_file)
            tee_err = Tee(self.console_err, log_file)
            with redirect_stdout(tee_out), redirect_stderr(tee_err):
                results, model_output_dir = run_for_model(
                    eval_args, self.args.model_alias, self.files, self.metadata
                )
        duration = time() - start
        os.environ.pop("VERICODING_TOKEN_LOG", None)

        json_failures = [
            {"file": Path(result.file).name, "error": result.error}
            for result in results
            if result.error and "JSON parsing failed" in result.error
        ]
        json_success = len(json_failures) == 0

        record: dict[str, Any] = {
            "round": round_idx,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "max_tokens": max_tokens,
            "json_success": json_success,
            "json_failures": json_failures,
            "output_dir": str(model_output_dir),
            "log_path": str(log_path),
            "token_log": str(token_log_path),
            "duration_sec": duration,
            "selected_specs": self.selected_specs,
        }

        status = "✅ JSON OK" if json_success else "✗ JSON failed"
        print(
            f"\n[round {round_idx}] {status} at max_tokens={max_tokens} "
            f"(artifacts: {run_dir})"
        )

        return record

    def _append_history(self, record: dict[str, Any]) -> None:
        with self.history_path.open("a") as f:
            f.write(json.dumps(record) + "\n")

    def _build_eval_args(
        self,
        *,
        max_tokens: int,
        output_dir: Path,
    ) -> SimpleNamespace:
        return SimpleNamespace(
            tasks_dir=self.args.tasks_dir,
            verbose=self.args.verbose,
            backend=self.args.backend,
            vllm_base_url=self.args.vllm_base_url,
            vllm_api_key=self.args.vllm_api_key,
            vllm_max_tokens=max_tokens,
            vllm_request_timeout=self.args.vllm_request_timeout,
            output_dir=output_dir,
            use_dynamic_rate_limit=self.args.use_dynamic_rate_limit,
            rate_limit_rpm=self.args.rate_limit_rpm,
            max_concurrent_tasks=self.args.max_concurrent_tasks,
            parallel_workers=self.args.parallel_workers,
            max_iterations=self.args.max_iterations,
        )


def main() -> None:
    args = parse_args()
    ensure_env_loaded()
    configure_logging(args.verbose)
    os.environ["WANDB_MODE"] = args.wandb_mode

    metadata = load_hard_subset_metadata(args.tasks_dir)

    selection_args = SimpleNamespace(
        eval_hardest=args.eval_hardest,
        limit=args.limit,
        eval_all=args.eval_all,
        hardest_count=args.hardest_count,
        sources=args.sources,
        min_difficulty=args.min_difficulty,
        max_difficulty=args.max_difficulty,
        min_models_passed=args.min_models_passed,
        max_models_passed=args.max_models_passed,
    )

    files = select_tasks(metadata, args.tasks_dir / "files", selection_args)
    if not files:
        raise SystemExit("No tasks matched the provided filters.")

    print(f"Selected {len(files)} tasks: {[path.name for path in files]}")

    searcher = SequenceLengthSearcher(args, files, metadata)
    searcher.run()


if __name__ == "__main__":
    main()


