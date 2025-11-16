from importlib import util as importlib_util
from pathlib import Path
import sys

import types

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC_PATH = PROJECT_ROOT / "src"
PROMPTS_MODULE_PATH = SRC_PATH / "vericoding/core/prompts.py"
LLM_PROVIDERS_PATH = SRC_PATH / "vericoding/core/llm_providers.py"

if str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

PROMPTS_SPEC = importlib_util.spec_from_file_location(
    "vericoding.core.prompts", PROMPTS_MODULE_PATH
)
LLM_SPEC = importlib_util.spec_from_file_location(
    "vericoding.core.llm_providers", LLM_PROVIDERS_PATH
)
assert PROMPTS_SPEC and PROMPTS_SPEC.loader
assert LLM_SPEC and LLM_SPEC.loader

# Provide lightweight stubs for optional provider deps so imports succeed.
if "anthropic" not in sys.modules:
    class _AnthropicStub:
        def __init__(self, *args, **kwargs):
            pass

        class messages:
            @staticmethod
            def create(*args, **kwargs):
                raise NotImplementedError

    sys.modules["anthropic"] = types.SimpleNamespace(
        Anthropic=_AnthropicStub,
        RateLimitError=RuntimeError,
        APIError=RuntimeError,
    )

if "openai" not in sys.modules:
    class _OpenAIStub:
        def __init__(self, *args, **kwargs):
            pass

        class chat:
            class completions:
                @staticmethod
                def create(*args, **kwargs):
                    raise NotImplementedError

    sys.modules["openai"] = types.SimpleNamespace(
        OpenAI=_OpenAIStub,
        RateLimitError=RuntimeError,
    )

PROMPTS_MODULE = importlib_util.module_from_spec(PROMPTS_SPEC)
LLM_MODULE = importlib_util.module_from_spec(LLM_SPEC)
PROMPTS_SPEC.loader.exec_module(PROMPTS_MODULE)
LLM_SPEC.loader.exec_module(LLM_MODULE)
PromptLoader = PROMPTS_MODULE.PromptLoader
build_messages = LLM_MODULE._build_messages


def test_prompt_loader_loads_dafny_prompts() -> None:
    loader = PromptLoader(language="dafny")
    assert "generate_code" in loader.prompts
    assert loader.prompts_path.name == "prompts.yaml"


def test_prompt_loader_overrides_with_env(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    missing_path = tmp_path / "missing.yaml"
    monkeypatch.setenv("VERICODING_PROMPTS_PATH", str(missing_path))

    with pytest.raises(FileNotFoundError) as excinfo:
        PromptLoader(language="dafny")

    assert str(missing_path) in str(excinfo.value)


def test_build_messages_injects_harmony_system_prompt() -> None:
    messages = build_messages("hello", "openai/gpt-oss-20b")
    assert messages[0]["role"] == "system"
    assert "Reasoning: high" in messages[0]["content"]
    assert messages[1]["role"] == "user"


def test_build_messages_plain_model_keeps_user_only() -> None:
    messages = build_messages("hello", "other-model")
    assert len(messages) == 1
    assert messages[0]["role"] == "user"

