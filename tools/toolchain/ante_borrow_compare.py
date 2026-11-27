# SPDX-License-Identifier: Apache-2.0
"""Replay borrowing trials against the pinned Ante compiler."""

import os
import re
import subprocess
import sys
import tarfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from io import BytesIO
from pathlib import Path

from toolchain.hashing import sha256_bytes

ANTEREV = "3916c257dd01e23a05564f925ea15b1f70a7435e"
MINICORO = "97ba5a836085b221e4e49a1bd16ca82bd9b16a56"
DIRECT = "nested_indexed_invalidation.an"
REWRITE = "nested_indexed_invalidation_rewrite.an"
MULTIDIM_DIRECT = "multidim_index_borrows.an"
MULTIDIM_REWRITE = "multidim_index_borrows_rewrite.an"
BRANCH_VIEW_DIRECT = "branch_view_last_use.an"
BRANCH_VIEW_REWRITE = "branch_view_last_use_rewrite.an"
LOOP_VIEW_DIRECT = "loop_view_return.an"
LOOP_VIEW_REWRITE = "loop_view_return_rewrite.an"
FLAGS = ("--no-color", "--threads", "1")
TIMEOUT = 60
BUILD_TIMEOUT = 300


@dataclass(frozen=True)
class AnteTrial:
    direct: str
    rewrite: str
    coincident: str
    direct_mutation: str
    coincident_mutation: str
    companion_hf: str | None = None
    invalidation_line: str = "        Some selected.*"
    invalidation_target: str = "selected.*"
    invalidation_message: str = "selected may have been invalidated by an earlier mutation"
    rewrite_output: str = "verified 16 cases"


TRIALS = (
    AnteTrial(
        direct=DIRECT,
        rewrite=REWRITE,
        coincident="nested_indexed_invalidation_coincident.an",
        direct_mutation="Vec.clear rows.[j]",
        coincident_mutation="Vec.clear rows.[i]",
        companion_hf="nested-indexed-invalidation.hf",
    ),
    AnteTrial(
        direct=MULTIDIM_DIRECT,
        rewrite=MULTIDIM_REWRITE,
        coincident="multidim_index_borrows_coincident.an",
        direct_mutation="Vec.clear grid.[r2]",
        coincident_mutation="Vec.clear grid.[r1]",
    ),
    AnteTrial(
        direct=BRANCH_VIEW_DIRECT,
        rewrite=BRANCH_VIEW_REWRITE,
        coincident="branch_view_last_use_coincident.an",
        direct_mutation="Vec.clear rows.[0]",
        coincident_mutation="Vec.clear rows.[i]",
        companion_hf="branch-view-last-use.hf",
        invalidation_line="            Some selected.*",
    ),
    AnteTrial(
        direct=LOOP_VIEW_DIRECT,
        rewrite=LOOP_VIEW_REWRITE,
        coincident="loop_view_return_coincident.an",
        direct_mutation="if n <= 3 then",
        coincident_mutation="if n <= 4 then",
        companion_hf="loop-view-return.hf",
    ),
)


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
    executable: Path, work: Path, fixture: str, source: str, trial: AnteTrial, env: dict[str, str],
) -> dict[str, object]:
    matches = [(n, text) for n, text in enumerate(source.splitlines(), 1) if text == trial.invalidation_line]
    if len(matches) != 1:
        raise ValueError(f"{fixture}: expected a single invalidation line {trial.invalidation_line!r}")
    line, line_text = matches[0]
    if trial.invalidation_target not in line_text:
        raise ValueError(f"{fixture}: invalidation target {trial.invalidation_target!r} missing from {line_text!r}")
    column = line_text.index(trial.invalidation_target) + 1
    result = subprocess.run([str(executable), fixture, "--check", *FLAGS], cwd=work,
                            capture_output=True, text=True, encoding="utf-8", check=False, timeout=TIMEOUT, env=env)
    diagnostics = re.findall(rf"(?m)^{re.escape(fixture)}:(\d+):(\d+)$", result.stderr)
    expected = f"{line} | {line_text}\t// error: {trial.invalidation_message}"
    if (result.returncode != 1 or diagnostics != [(str(line), str(column))]
            or expected not in result.stderr or result.stderr.count("// error:") != 1
            or "Found 1 error and 0 warnings" not in result.stderr.splitlines()):
        raise ValueError(
            f"{fixture}: expected single invalidation at {line}:{column}, exit={result.returncode}\n{result.stderr}"
        )
    return {
        "fixture": fixture, "flags": ["--check", *FLAGS], "decision": "rejected",
        "diagnostics": [{"message": trial.invalidation_message, "line": line, "column": column}],
        "observations": "n/a",
    }


def _run_trial(
    executable: Path,
    fixtures: Path,
    work: Path,
    sources: dict[str, str],
    trial: AnteTrial,
    env: dict[str, str],
) -> list[dict[str, object]]:
    inputs = [trial.direct, trial.rewrite]
    if trial.companion_hf is not None:
        inputs.append(trial.companion_hf)
    for name in inputs:
        source = (fixtures / name).read_bytes()
        sources[name] = sha256_bytes(source)
        if name.endswith(".an"):
            (work / name).write_bytes(source)
    direct = (work / trial.direct).read_text(encoding="utf-8")
    if direct.count(trial.direct_mutation) != 1:
        raise ValueError(f"{trial.direct} must have exactly one mutation {trial.direct_mutation!r}")
    coincident = direct.replace(trial.direct_mutation, trial.coincident_mutation)
    encoded = coincident.encode("utf-8")
    (work / trial.coincident).write_bytes(encoded)
    sources[trial.coincident] = sha256_bytes(encoded)
    results = [_check_invalidation(executable, work, name, source, trial, env)
               for name, source in ((trial.direct, direct), (trial.coincident, coincident))]
    runtime_flags = ["--backend", "c", "--delete-binary", *FLAGS]
    if _output([str(executable), trial.rewrite, *runtime_flags], work, env=env) != trial.rewrite_output:
        raise ValueError(f"{trial.rewrite} did not execute its expected observations")
    results.append({
        "fixture": trial.rewrite, "flags": runtime_flags, "decision": "accepted",
        "diagnostics": [], "observations": "passed",
    })
    return results


def compare_ante(
    checkout: Path,
    fixtures: Path,
    work: Path,
    sources: dict[str, str],
    *,
    nested_rows_only: bool = False,
) -> dict[str, object]:
    executable, identity = _build_compiler(checkout.resolve(), work)
    env = os.environ.copy()
    env.pop("ANTE_STDLIB_DIR", None)
    env.pop("ANTE_MINICORO_PATH", None)
    selected = TRIALS[:1] if nested_rows_only else TRIALS

    def run_isolated(item: tuple[int, AnteTrial]) -> tuple[dict[str, str], list[dict[str, object]]]:
        idx, trial = item
        trial_work = work / f"ante-trial-{idx}"
        trial_work.mkdir()
        trial_sources: dict[str, str] = {}
        entries = _run_trial(executable, fixtures, trial_work, trial_sources, trial, env)
        return trial_sources, entries

    with ThreadPoolExecutor(max_workers=min(4, os.process_cpu_count() or 1, max(1, len(selected)))) as pool:
        outcomes = list(pool.map(run_isolated, enumerate(selected)))
    results: list[dict[str, object]] = []
    for trial_sources, entries in outcomes:
        sources.update(trial_sources)
        results.extend(entries)
    return {**identity, "results": results}
