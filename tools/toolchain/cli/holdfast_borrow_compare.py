# SPDX-License-Identifier: Apache-2.0
"""Replay the Rust side of the source borrowing comparison."""

import argparse
import json
import platform
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from time import perf_counter_ns

from toolchain import corpus
from toolchain.hashing import sha256_bytes

NIGHTLY = "nightly-2026-11-20"
REVISION = "6905905bb7727fd0f9223f5fdc9ad4e62236d5a2"
EDITION = "2024"
MODES = ("default", "off", "legacy", "next")
TIMEOUT = 60
ANALYSIS_FLAGS = ("-Zno-codegen", "-Ztime-passes", "-Ztime-passes-format=json")
WARM_SAMPLES = 5
TIMING_PREFIX = "time: "

type Diagnostic = tuple[str, str]
type LocatedDiagnostic = tuple[str, int]


@dataclass(frozen=True)
class Trial:
    fixture: str
    configuration: str | None
    expected: tuple[Diagnostic, ...] = ()
    next_solver: bool = False


def trials(mode: str) -> tuple[Trial, ...]:
    sibling = (("E0506", "sibling-write"),) if mode == "off" else ()
    loop = () if mode == "legacy" else (("E0499", "loop-reborrow"), ("E0503", "loop-reborrow"))
    nonzero_write = ("E0506", "nonzero-write")
    filtered = (("E0499", "filtered-reborrow"),) if mode == "off" else ()
    owner_conflict = (("E0503", "owner-conflict"), ("E0506", "owner-conflict"))
    escaping = (("E0521", "escaping-view"),)
    common = (
        Trial("indexed_loans.rs", "direct", (("E0499", "direct-conflict"),)),
        Trial("indexed_loans.rs", "coincident", (("E0499", "coincident-conflict"),)),
        Trial("indexed_loans.rs", None),
        Trial("mixed_indexed_loans.rs", "direct", (("E0502", "direct-mixed-conflict"),)),
        Trial("mixed_indexed_loans.rs", "coincident", (("E0502", "coincident-mixed-conflict"),)),
        Trial("mixed_indexed_loans.rs", None),
        Trial("owner_coordinate_loans.rs", "direct", (("E0502", "owner-coordinate-conflict"),)),
        Trial("owner_coordinate_loans.rs", "coincident", (("E0502", "owner-coordinate-coincident"),)),
        Trial("owner_coordinate_loans.rs", None),
        Trial("composed_view_loans.rs", "direct", (("E0502", "composed-view-conflict"),)),
        Trial("composed_view_loans.rs", "coincident", (("E0502", "composed-view-coincident"),)),
        Trial("composed_view_loans.rs", None),
        Trial("updated_view_loans.rs", "direct", (("E0506", "disjoint-write"),)),
        Trial("updated_view_loans.rs", "overlapping_write", (("E0506", "overlapping-write"),)),
        Trial("updated_view_loans.rs", None),
        Trial("conditional_loans.rs", None, sibling),
        Trial("conditional_loans.rs", "live_conflict", (("E0506", "live-conflict"), *sibling)),
        Trial("joined_view_return.rs", "direct", (("E0506", "disjoint-zero-write"), nonzero_write)),
        Trial("joined_view_return.rs", "coincident", (("E0506", "coincident-zero-write"), nonzero_write)),
        Trial("joined_view_return.rs", None),
        Trial("loop_view_return.rs", "direct", (("E0506", "loop-prefix-write"),)),
        Trial("loop_view_return.rs", "coincident", (("E0506", "loop-prefix-write"),)),
        Trial("loop_view_return.rs", None),
        Trial("loop_reborrowing.rs", None, loop),
        Trial("loop_reborrowing.rs", "live_conflict", (("E0506", "live-conflict"),)),
        Trial("lending_iterator.rs", None),
        Trial("lending_iterator.rs", "filter_return", filtered),
        Trial("lending_iterator.rs", "live_conflict", (("E0499", "live-conflict"),)),
        Trial("lending_iterator.rs", "owner_conflict", owner_conflict),
        Trial("lifetime_callback.rs", None),
        Trial("lifetime_callback.rs", "escaping_view", escaping),
    )
    if mode == "default":
        return (*common, Trial("lifetime_callback.rs", None, next_solver=True),
                Trial("lifetime_callback.rs", "escaping_view", escaping, next_solver=True))
    return common


def _errors(output: str, fixture: str) -> list[LocatedDiagnostic]:
    errors: list[LocatedDiagnostic] = []
    for line in output.splitlines():
        if line.startswith(TIMING_PREFIX):
            continue
        message = json.loads(line)
        if message.get("level") != "error":
            continue
        spans = message["spans"]
        code = message["code"]
        if code is None and not spans and message["message"].startswith("aborting due to "):
            continue
        if code is None:
            raise ValueError((message.get("rendered") or message["message"]).strip())
        primary = [span for span in spans if span["is_primary"] and span["file_name"] == fixture]
        if len(primary) != 1:
            raise ValueError(f"unexpected error location: {message['message']}")
        errors.append((code["code"], primary[0]["line_start"]))
    return sorted(errors)


def _marker_line(source: str, marker: str) -> int:
    matches = [line for line, text in enumerate(source.splitlines(), 1)
               if text.endswith(f"// {marker}")]
    if len(matches) != 1:
        raise ValueError(f"expected a single location for {marker!r}")
    return matches[0]


def _check_compile(argv: list[str], work: Path, fixture: str, expected: list[LocatedDiagnostic]) -> tuple[str, int]:
    start = perf_counter_ns()
    compiled = subprocess.run(argv, cwd=work, capture_output=True, text=True,
                              encoding="utf-8", check=False, timeout=TIMEOUT)
    elapsed = perf_counter_ns() - start
    observed = _errors(compiled.stderr, fixture)
    expected_exit = 1 if expected else 0
    if compiled.returncode != expected_exit or observed != expected:
        raise ValueError(f"{argv}: exit={compiled.returncode}, errors={observed}, expected={expected}")
    return compiled.stderr, elapsed


def _analysis_sample(argv: list[str], work: Path, fixture: str, expected: list[LocatedDiagnostic]) -> dict[str, object]:
    stderr, elapsed = _check_compile(argv, work, fixture, expected)
    passes = [json.loads(line.removeprefix(TIMING_PREFIX))
              for line in stderr.splitlines() if line.startswith(TIMING_PREFIX)]
    for name in ("MIR_checking", "total"):
        if sum(item["pass"] == name for item in passes) != 1:
            raise ValueError(f"{argv}: expected a single timing entry for {name}")
    return {"elapsed_ns": elapsed, "rustc_passes": passes}


def _measure_analysis(argv: list[str], work: Path, fixture: str, expected: list[LocatedDiagnostic]) -> dict[str, object]:
    command = [*argv, *ANALYSIS_FLAGS]
    first = _analysis_sample(command, work, fixture, expected)
    _analysis_sample(command, work, fixture, expected)
    warm = [_analysis_sample(command, work, fixture, expected) for _ in range(WARM_SAMPLES)]
    return {"argv": command, "first": first, "warm": warm}


def _run_trial(compiler: list[str], mode: str, trial: Trial, work: Path, *, measure: bool) -> dict[str, object]:
    flags: list[str] = []
    if mode != "default":
        flags.append(f"-Zpolonius={mode}")
    if trial.next_solver:
        flags.append("-Znext-solver=globally")
    if trial.configuration is not None:
        flags.extend(("--cfg", trial.configuration))
    argv = [*compiler, "--edition", EDITION, "--test", "--error-format=json", *flags, trial.fixture]
    config = trial.configuration or "plain"
    solver = "-next-solver" if trial.next_solver else ""
    binary = work / f"{Path(trial.fixture).stem}-{mode}-{config}{solver}.exe"
    source = (work / trial.fixture).read_text(encoding="utf-8")
    expected = sorted((code, _marker_line(source, marker)) for code, marker in trial.expected)
    output_flags = ("--emit=mir=-",) if expected else ("-o", str(binary))
    result: dict[str, object] = {"mode": mode, "fixture": trial.fixture, "cfg": trial.configuration,
                                 "flags": flags, "decision": "rejected" if expected else "accepted",
                                 "diagnostics": [{"code": code, "line": line} for code, line in expected],
                                 "observations": "n/a" if expected else "passed"}
    if measure:
        result["analysis_timing"] = _measure_analysis(argv, work, trial.fixture, expected)
    _check_compile([*argv, *output_flags], work, trial.fixture, expected)
    if not expected:
        output = subprocess.run([str(binary), "--exact", "expected_observations"], cwd=work,
                                capture_output=True, text=True, encoding="utf-8",
                                check=True, timeout=TIMEOUT).stdout
        if "test expected_observations ... ok" not in output.splitlines():
            raise ValueError(f"{trial.fixture} did not execute its expected observations")
    return result


def compare(root: Path, *, measure: bool = False) -> dict[str, object]:
    compiler = ["rustc", f"+{NIGHTLY}"]
    version = subprocess.run([*compiler, "-vV"], cwd=root, capture_output=True, text=True,
                             encoding="utf-8", check=True, timeout=TIMEOUT).stdout
    if f"commit-hash: {REVISION}" not in version.splitlines():
        raise ValueError(f"unexpected compiler revision:\n{version}")
    host = next((line.removeprefix("host: ") for line in version.splitlines()
                 if line.startswith("host: ")), None)
    if host is None:
        raise ValueError("rustc did not identify its host")
    fixtures = root / "tools" / "tests" / "fixtures"
    with tempfile.TemporaryDirectory(prefix="holdfast-borrow-compare-") as temporary:
        work = Path(temporary)
        sources = {}
        for name in sorted({trial.fixture for mode in MODES for trial in trials(mode)}):
            source = (fixtures / name).read_bytes()
            (work / name).write_bytes(source)
            sources[name] = sha256_bytes(source)
        results = [_run_trial(compiler, mode, trial, work, measure=measure)
                   for mode in MODES for trial in trials(mode)]
    report: dict[str, object] = {"rustc": {"toolchain": NIGHTLY, "revision": REVISION, "host": host},
                                 "edition": EDITION, "sources_sha256": sources, "results": results}
    if measure:
        report["measurement_environment"] = {
            "platform": platform.platform(), "python": platform.python_version(),
            "processor": platform.processor() or "unknown", "workers": 1, "os_cache": "uncontrolled",
            "runner_sha256": sha256_bytes(Path(__file__).read_bytes()),
        }
    return report


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--measure", action="store_true", help="sample check-only compiler timings for every trial")
    args = parser.parse_args(argv)
    try:
        report = compare(corpus.find_root(), measure=args.measure)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"FAIL holdfast-borrow-compare: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2))
    return 0
