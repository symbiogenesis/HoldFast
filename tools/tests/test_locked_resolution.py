# SPDX-License-Identifier: Apache-2.0
"""The locked resolver refuses stale input before running a tool command."""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import corpus, toolenv

INDEPENDENT_CASES = True


def _locked_resolution() -> None:
    uv = shutil.which("uv")
    ensure(uv is not None, "the public tool bootstrap requires uv")
    with tempfile.TemporaryDirectory(prefix="holdfast-locked-resolution-") as directory:
        root = Path(directory)
        project = root / "pyproject.toml"
        declaration = ('[project]\nname = "holdfast-lock-fixture"\nversion = "0"\n'
                       'requires-python = ">=3.14,<3.15"\n'
                       '[tool.uv]\npackage = false\npython-downloads = "never"\n')
        project.write_text(declaration, encoding="utf-8")
        environment = {**os.environ, "UV_PROJECT_ENVIRONMENT": str(root / "venv")}
        environment.pop("VIRTUAL_ENV", None)
        command = [str(uv), "run", "--project", str(root), "--offline", "--exact",
                   "--no-python-downloads", "--python", sys.executable, "python", "-c",
                   "from pathlib import Path; Path('dispatched').write_text('yes')"]
        first = subprocess.run(command, cwd=root, env=environment, capture_output=True,
                               text=True, check=False, timeout=30)
        ensure(first.returncode == 0 and (root / "dispatched").is_file(),
               f"a coherent fixture must dispatch: {first.stderr}")
        locked = (root / "uv.lock").read_bytes()
        (root / "dispatched").unlink()
        project.write_text(declaration.replace('version = "0"', 'version = "1"'),
                           encoding="utf-8")
        stale = subprocess.run([*command[:2], "--locked", *command[2:]], cwd=root,
                               env=environment, capture_output=True, text=True,
                               check=False, timeout=30)
        ensure(stale.returncode != 0 and "lockfile" in stale.stderr.lower(),
               f"uv must refuse the stale lock: {stale.stderr}")
        ensure(not (root / "dispatched").exists(), "stale input reached command dispatch")
        ensure((root / "uv.lock").read_bytes() == locked,
               "locked validation must not repair dependency decisions")


def _exact_checker_pins() -> None:
    repo_root = corpus.find_root()
    live_pins = toolenv.checker_pins(repo_root)
    ensure(set(live_pins) == toolenv.REQUIRED_DEV_PINS,
           f"live checker pins must match REQUIRED_DEV_PINS: {live_pins!r}")
    with tempfile.TemporaryDirectory(prefix="holdfast-checker-pins-") as directory:
        root = Path(directory)
        (root / "tools").mkdir()
        path = root / toolenv.PROJECT
        for dependencies in ('["ty>=1", "ruff==2"]',
                             '["ty==1", "ty==1", "ruff==2"]',
                             '["ty==1", "ruff==2"]',
                             '"invalid"'):
            path.write_text(f"[dependency-groups]\ndev = {dependencies}\n", encoding="utf-8")
            try:
                toolenv.checker_pins(root)
            except (TypeError, ValueError):
                continue
            raise AssertionError(f"invalid exact checker pin policy accepted: {dependencies}")


def _guest_native_cache_and_warm_bootstrap() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-guest-env-") as directory:
        base = Path(directory)
        repo = base / "mnt-repo"
        (repo / "tools").mkdir(parents=True)
        (repo / toolenv.PROJECT).write_text('[project]\nname = "fixture"\n', encoding="utf-8")
        (repo / toolenv.LOCK).write_text("version = 1\n", encoding="utf-8")
        native_root = Path("/var/cache/holdfast-fixture-build")

        def fake_fs(path: Path | str) -> str:
            p = Path(path).resolve()
            return "9p" if p.is_relative_to(repo.resolve()) else "ext4"

        with (patch.object(toolenv.env, "filesystem", side_effect=fake_fs),
              patch.object(toolenv.env, "build_root", return_value=native_root)):
            ensure(toolenv.pycache_prefix(repo, "linux") == native_root.resolve() / "pycache",
                   "cross-OS guest run did not direct bytecode to persistent native storage")
            ensure(toolenv.pycache_prefix(repo, "win32") is None,
                   "Windows host run unexpectedly redirected pycache")
            with patch.object(toolenv.env, "lane_of", return_value=""):
                primary = toolenv.environment(repo, "linux")
            with patch.object(toolenv.env, "lane_of", return_value="feature-a"):
                linked_a = toolenv.environment(repo, "linux")
            with patch.object(toolenv.env, "lane_of", return_value="feature-b"):
                linked_b = toolenv.environment(repo, "linux")
            ensure(primary == native_root.resolve() / "venv-linux",
                   "primary checkout changed its expected guest venv path")
            ensure(linked_a == linked_b and linked_a.parent == native_root.resolve() / "venvs",
                   "linked worktrees with identical lockfiles did not share one lock-keyed venv")
            (repo / toolenv.LOCK).write_text("version = 2\n", encoding="utf-8")
            with patch.object(toolenv.env, "lane_of", return_value="feature-b"):
                linked_updated = toolenv.environment(repo, "linux")
            ensure(linked_updated != linked_b,
                   "changing uv.lock reused the previous lock-keyed venv")

        venv = base / "local-venv"
        py_exe = toolenv._venv_python(venv)
        py_exe.parent.mkdir(parents=True)
        py_exe.write_bytes(b"")
        sync_calls: list[list[str]] = []
        dispatch_calls: list[tuple[Path, list[str], str]] = []

        def fake_sync(cmd: list[str], **_kwargs: object) -> subprocess.CompletedProcess[bytes]:
            sync_calls.append(cmd)
            return subprocess.CompletedProcess(cmd, 0)

        def fake_dispatch(exe: Path, _script: Path, argv: list[str], env_map: dict[str, str]) -> int:
            dispatch_calls.append((exe, argv, env_map[toolenv.READY]))
            return 0

        with (patch.object(toolenv.pyversion, "require_supported"),
              patch.object(toolenv, "environment", return_value=venv),
              patch.object(toolenv, "pycache_prefix", return_value=None),
              patch.object(toolenv.shutil, "which", return_value="uv"),
              patch.object(toolenv.subprocess, "run", side_effect=fake_sync),
              patch.object(toolenv, "_dispatch", side_effect=fake_dispatch)):
            ensure(toolenv.bootstrap(repo, ["gate"]) == 0, "cold bootstrap failed")
            ensure(len(sync_calls) == 1 and "sync" in sync_calls[0], "cold bootstrap skipped uv sync")
            ensure(toolenv.bootstrap(repo, ["gate"]) == 0, "warm bootstrap failed")
            ensure(len(sync_calls) == 1 and len(dispatch_calls) == 2,
                   "warm bootstrap re-ran uv sync when environment token matched")
            (repo / toolenv.LOCK).write_text("version = 3\n", encoding="utf-8")
            ensure(toolenv.bootstrap(repo, ["gate"]) == 0, "re-sync bootstrap failed")
            ensure(len(sync_calls) == 2, "lockfile edit did not invalidate warm environment token")


def cases() -> list[Case]:
    return [Case("locked resolver refuses stale input before dispatch", _locked_resolution),
            Case("checker dependencies remain exact and unique", _exact_checker_pins),
            Case("guest native pycache, shared venvs, and warm bootstrap", _guest_native_cache_and_warm_bootstrap)]
