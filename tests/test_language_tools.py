from types import SimpleNamespace
import shutil
from pathlib import Path
import sys

PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC_PATH = PROJECT_ROOT / "src"
if str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

from vericoding.core.language_tools import get_tool_path


def test_get_tool_path_uses_dafny_home(tmp_path, monkeypatch):
    install_root = tmp_path / "dafny_home"
    binary = install_root / "dafny" / "dafny"
    binary.parent.mkdir(parents=True)
    binary.write_text("#!/bin/bash\necho dafny")
    binary.chmod(0o755)

    monkeypatch.setenv("DAFNY_HOME", str(install_root))
    monkeypatch.delenv("DAFNY_PATH", raising=False)
    monkeypatch.setattr(shutil, "which", lambda _: None)

    config = SimpleNamespace(
        language="dafny",
        language_config=SimpleNamespace(
            default_tool_path="dafny",
            tool_path_env="DAFNY_PATH",
            name="Dafny",
        ),
    )

    assert get_tool_path(config) == str(binary)


def test_get_tool_path_defaults_for_other_languages(monkeypatch):
    monkeypatch.setattr(shutil, "which", lambda _: None)

    config = SimpleNamespace(
        language="lean",
        language_config=SimpleNamespace(
            default_tool_path="lake",
            tool_path_env="LEAN_PATH",
            name="Lean",
        ),
    )

    assert get_tool_path(config) == "lake"

