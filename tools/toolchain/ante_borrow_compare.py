# SPDX-License-Identifier: Apache-2.0
"""Replay the nested-row borrowing trial against the pinned Ante compiler."""

import os
import re
import subprocess
import sys
import tarfile
from io import BytesIO
from pathlib import Path

from toolchain.hashing import sha256_bytes

ANTEREV = "3916c257dd01e23a05564f925ea15b1f70a7435e"
MINICORO = "97ba5a836085b221e4e49a1bd16ca82bd9b16a56"
DIRECT = "nested_indexed_invalidation.an"
REWRITE = "nested_indexed_invalidation_rewrite.an"
FLAGS = ("--no-color", "--threads", "1")
TIMEOUT = 60
BUILD_TIMEOUT = 300


def _output(argv: list[str], cwd: Path, *, timeout: int = TIMEOUT, env: dict[str, str] | None = None) -> str:
    result = subprocess.run(argv, cwd=cwd, capture_output=True, text=True,
                            encoding="utf-8", check=False, timeout=timeout, env=env)
    if result.returncode != 0:
        raise ValueError(f"{argv}: exit={result.returncode}\n{result.stderr.strip()}")
    return result.stdout.strip()


def _stage_tree(checkout: Path, revision: str, destination: Path) -> None:
    archive = subprocess.run(["git", "archive", "--format=tar", revision], cwd=checkout, capture_output=True,
                             check=True, timeout=TIMEOUT).stdout
    with tarfile.open(fileobj=BytesIO(archive)) as tree:
        tree.extractall(destination, filter="data")


def _build_compiler(checkout: Path, work: Path) -> tuple[Path, dict[str, object]]:
    root = Path(_output(["git", "rev-parse", "--show-toplevel"], checkout))
    if root.resolve() != checkout:
        raise ValueError(f"{checkout} must be the root of the Ante checkout")
    revision = _output(["git", "rev-parse", "HEAD"], checkout)
    if revision != ANTEREV:
        raise ValueError(f"expected Ante revision {ANTEREV}, found {revision}")
    submodules = _output(["git", "submodule", "status", "--recursive"], checkout)
    if len(submodules.splitlines()) != 1 or submodules.split()[:2] != [MINICORO, "aminicoro"]:
        raise ValueError(f"expected pinned Ante submodule aminicoro at {MINICORO}: {submodules}")
    source = work / "ante-source"
    target = work / "ante-build"
    _stage_tree(checkout, revision, source)
    _stage_tree(checkout / "aminicoro", MINICORO, source / "aminicoro")
    flags = ["--locked", "--no-default-features", "--bin", "ante", "--target-dir", str(target)]
    build_env = os.environ.copy()
    build_env.pop("ANTE_STDLIB_DIR", None)
    build_env.pop("ANTE_MINICORO_PATH", None)
    _output(["cargo", "build", *flags], source, timeout=BUILD_TIMEOUT, env=build_env)
    executable = target / "debug" / ("ante.exe" if sys.platform == "win32" else "ante")
    return executable, {
        "revision": revision, "aminicoro_revision": MINICORO,
        "cargo": _output(["cargo", "--version"], source),
        "rustc": _output(["rustc", "-vV"], source),
        "build_flags": flags[:-2], "binary_sha256": sha256_bytes(executable.read_bytes()),
    }


def _check_invalidation(
    executable: Path, work: Path, fixture: str, source: str, env: dict[str, str],
) -> dict[str, object]:
    line, = [line for line, text in enumerate(source.splitlines(), 1) if text.strip() == "Some selected.*"]
    result = subprocess.run([str(executable), fixture, "--check", *FLAGS], cwd=work,
                            capture_output=True, text=True, encoding="utf-8", check=False, timeout=TIMEOUT, env=env)
    diagnostics = re.findall(rf"(?m)^{re.escape(fixture)}:(\d+):(\d+)$", result.stderr)
    error = "selected may have been invalidated by an earlier mutation"
    expected = f"{line} |         Some selected.*\t// error: {error}"
    if (result.returncode != 1 or diagnostics != [(str(line), "14")]
            or expected not in result.stderr or result.stderr.count("// error:") != 1
            or "Found 1 error and 0 warnings" not in result.stderr.splitlines()):
        raise ValueError(f"{fixture}: expected single invalidation at {line}:14, exit={result.returncode}\n{result.stderr}")
    return {
        "fixture": fixture, "flags": ["--check", *FLAGS], "decision": "rejected",
        "diagnostics": [{"message": error, "line": line, "column": 14}], "observations": "n/a",
    }


def compare_ante(checkout: Path, fixtures: Path, work: Path, sources: dict[str, str]) -> dict[str, object]:
    executable, identity = _build_compiler(checkout.resolve(), work)
    env = os.environ.copy()
    env.pop("ANTE_STDLIB_DIR", None)
    env.pop("ANTE_MINICORO_PATH", None)
    for name in (DIRECT, REWRITE, "nested-indexed-invalidation.hf"):
        source = (fixtures / name).read_bytes()
        sources[name] = sha256_bytes(source)
        if name.endswith(".an"):
            (work / name).write_bytes(source)
    direct = (work / DIRECT).read_text(encoding="utf-8")
    coincident_name = "nested_indexed_invalidation_coincident.an"
    mutation = "Vec.clear rows.[j]"
    if direct.count(mutation) != 1:
        raise ValueError(f"{DIRECT} must have exactly one clear to generate the coincident control")
    coincident = direct.replace(mutation, "Vec.clear rows.[i]")
    encoded = coincident.encode("utf-8")
    (work / coincident_name).write_bytes(encoded)
    sources[coincident_name] = sha256_bytes(encoded)
    results = [_check_invalidation(executable, work, name, source, env)
               for name, source in ((DIRECT, direct), (coincident_name, coincident))]
    runtime_flags = ["--backend", "c", "--delete-binary", *FLAGS]
    if _output([str(executable), REWRITE, *runtime_flags], work, env=env) != "verified 16 cases":
        raise ValueError(f"{REWRITE} did not execute its expected observations")
    results.append({
        "fixture": REWRITE, "flags": runtime_flags, "decision": "accepted",
        "diagnostics": [], "observations": "passed",
    })
    return {**identity, "results": results}
