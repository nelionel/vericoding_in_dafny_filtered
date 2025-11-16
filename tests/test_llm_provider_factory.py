from types import SimpleNamespace
import types
from pathlib import Path
import sys
import importlib.util

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC_PATH = PROJECT_ROOT / "src"
FILE_PROCESSOR_PATH = SRC_PATH / "vericoding/processing/file_processor.py"

if str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))


class _TableStub:
    def __init__(self, *args, **kwargs):
        self.data = []

    def add_data(self, *args, **kwargs):
        self.data.append(args)


sys.modules.setdefault(
    "wandb",
    types.SimpleNamespace(run=None, Table=_TableStub, log=lambda *args, **kwargs: None),
)


class _GitError(Exception):
    pass


git_stub = types.SimpleNamespace(
    Repo=lambda *args, **kwargs: None,
)
sys.modules.setdefault("git", git_stub)
sys.modules.setdefault(
    "git.exc",
    types.SimpleNamespace(GitCommandError=_GitError, InvalidGitRepositoryError=_GitError),
)


SPEC = importlib.util.spec_from_file_location(
    "vericoding.processing.file_processor", FILE_PROCESSOR_PATH
)
assert SPEC and SPEC.loader
FILE_PROCESSOR_MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FILE_PROCESSOR_MODULE)
sys.modules["vericoding.processing.file_processor"] = FILE_PROCESSOR_MODULE
resolve_llm_provider = FILE_PROCESSOR_MODULE.resolve_llm_provider


def test_resolve_llm_provider_prefers_factory(monkeypatch: pytest.MonkeyPatch) -> None:
    called = {"create": 0, "factory": 0}

    def fake_create(llm_name: str):
        called["create"] += 1
        return ("create-provider", llm_name)

    def factory():
        called["factory"] += 1
        return ("factory-provider", "factory-model")

    monkeypatch.setattr(FILE_PROCESSOR_MODULE, "create_llm_provider", fake_create)

    config = SimpleNamespace(llm="gpt-oss-20b")
    provider, model = resolve_llm_provider(config, factory)

    assert provider == "factory-provider"
    assert model == "factory-model"
    assert called["factory"] == 1
    assert called["create"] == 0


def test_resolve_llm_provider_falls_back_to_create(monkeypatch: pytest.MonkeyPatch) -> None:
    recorded = {"llm": None}

    def fake_create(llm_name: str):
        recorded["llm"] = llm_name
        return ("create-provider", llm_name)

    monkeypatch.setattr(FILE_PROCESSOR_MODULE, "create_llm_provider", fake_create)

    config = SimpleNamespace(llm="openai/gpt-oss-20b")
    provider, model = resolve_llm_provider(config, None)

    assert provider == "create-provider"
    assert model == "openai/gpt-oss-20b"
    assert recorded["llm"] == "openai/gpt-oss-20b"

