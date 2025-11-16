"""Prompt loading and validation."""

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml


@dataclass
class PromptValidationResult:
    """Result of prompt validation."""

    valid: bool
    missing: list[str]
    available: list[str]


class PromptLoader:
    """Handles loading and formatting of prompts for different languages."""

    def __init__(self, language: str, prompts_file: str = "prompts.yaml") -> None:
        self.language = language
        self.prompts_file = prompts_file
        self.prompts: dict[str, str] = {}
        self.prompts_path = self._determine_prompts_path()
        self._load_prompts()

    def _determine_prompts_path(self) -> Path:
        """Compute the canonical prompts path, honoring overrides."""
        override = os.environ.get("VERICODING_PROMPTS_PATH")
        if override:
            return Path(override).expanduser().resolve()

        vericoding_root = Path(__file__).resolve().parent.parent
        return (vericoding_root / self.language / self.prompts_file).resolve()

    def _load_prompts(self) -> None:
        """Load prompts from YAML file."""
        if not self.prompts_path.exists():
            raise FileNotFoundError(f"Prompts file not found: {self.prompts_path}")

        with self.prompts_path.open() as f:
            self.prompts = yaml.safe_load(f)

    def format_prompt(self, prompt_name: str, **kwargs: Any) -> str:
        """Format a prompt with the given parameters."""
        if prompt_name not in self.prompts:
            raise KeyError(f"Prompt '{prompt_name}' not found")
        try:
            return self.prompts[prompt_name].format(**kwargs)
        except KeyError as e:
            # Better error message for missing placeholders
            raise KeyError(f"Missing placeholder in prompt '{prompt_name}': {e}")
        except Exception as e:
            # Catch any other formatting errors
            raise ValueError(f"Error formatting prompt '{prompt_name}': {e}")

    def validate_prompts(self) -> PromptValidationResult:
        """Validate that required prompts are available."""
        required = ["generate_code", "fix_verification"]
        missing = [p for p in required if p not in self.prompts]
        return PromptValidationResult(
            valid=len(missing) == 0,
            missing=missing,
            available=list(self.prompts.keys()),
        )
