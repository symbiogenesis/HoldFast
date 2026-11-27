# SPDX-License-Identifier: Apache-2.0
"""Run the behavioral suite in isolated worker processes.

The runner reuses workers, so cases restore any state they modify. Reports
follow module order. Shards stride over the sorted module list. An independent
module keeps its place in that list and distributes its ordered cases across shards.
See the [tool guide](../../README.md) for command usage.
"""

import argparse
import importlib
import multiprocessing
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from contextlib import redirect_stderr, redirect_stdout
from functools import partial
from io import StringIO
from pathlib import Path

from tests.harness import Case, Lane
from toolchain import env, sharding, timings
from toolchain.report import Reporter
from toolchain.sharding import Shard


def switches() -> set[str]:
    """Installed opam switches on the current machine."""
    try:
        done = subprocess.run(
            ["opam", "switch", "list", "--short"],
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            check=False,
            timeout=60,
            stdin=subprocess.DEVNULL,
            env=env.declining_environment(),
        )
    except OSError, subprocess.SubprocessError:
        return set()
    return set(done.stdout.splitlines()) if done.returncode == 0 else set()

# Execution lane of the current process.
LANE: Lane = "host" if sys.platform == "win32" else "guest"

TESTS = Path(__file__).resolve().parents[2] / "tests"

# Top-level declaration marking a test module's cases as independent across shards.
# The parent process scans the module source with `_DECLARED`, and the worker verifies
# that the imported module's attribute matches.
INDEPENDENT = "INDEPENDENT_CASES"
_DECLARED = re.compile(rf"(?m)^{INDEPENDENT} = True$")


class ModuleReport(Reporter):
    """Per-module test report, tracking executed case count and elapsed seconds."""

    def __init__(self) -> None:
        super().__init__()
        self.cases = 0
        self.skipped_slow = 0
        self.skipped_lane = 0
        self.seconds = 0.0
        self.failure_messages: list[str] = []
        self.captured_lines: list[str] = []


def _lanes() -> frozenset[Lane]:
    """Return the `Case.lane` values runnable in this process.

    Admits `"any"` and the current platform lane (`"host"` on Windows, `"guest"` on
    Linux), plus `"toolchain"` on a Linux guest when the expected opam switch is
    installed.
    """
    lanes: set[Lane] = {"any", LANE}
    if LANE == "guest" and env.SAIL_SWITCH in switches():
        lanes.add("toolchain")
    return frozenset(lanes)


def _module_names(only: str | None) -> list[str]:
    """Every test module under `tools/tests/`, sorted so the report order is fixed."""
    if only is not None and not only.strip():
        raise ValueError("--only requires a nonempty module-name substring")
    names = sorted(path.stem for path in TESTS.glob("test_*.py"))
    if only is not None:
        names = [name for name in names if only in name]
    return names


def _declares(name: str) -> bool:
    """Whether a test module's source declares `INDEPENDENT_CASES = True`."""
    try:
        return _DECLARED.search((TESTS / f"{name}.py").read_text(encoding="utf-8")) is not None
    except OSError, UnicodeDecodeError:
        return False


def _load(name: str, split: bool | None = None) -> list[Case] | str:
    """Import a test module inside a worker and return its validated `Case` list or an error string.

    Importing inside the worker allows cases to carry unpicklable closures and keeps
    module patches isolated. When `split` is not `None`, verifies that the module's
    runtime `INDEPENDENT_CASES` attribute matches the source scan.
    """
    try:
        module = importlib.import_module(f"tests.{name}")
        found: object = module.cases()
    except (Exception, SystemExit) as err:  # importing a test must not exit the runner
        return f"failed to load: {err!r}"
    declared = getattr(module, INDEPENDENT, False) is True
    if split is not None and declared != split:
        return (f"sets {INDEPENDENT} in a form a sharded run does not read; state it as "
                f"'{INDEPENDENT} = True' at the left margin" if declared else
                f"its source reads '{INDEPENDENT} = True', but the module does not set it")
    # Validate the dynamic return value of cases() before running.
    if not isinstance(found, list):
        return f"cases() returned {type(found).__name__}, not a list"
    if not found:
        return "cases() returned an empty list"
    narrowed: list[Case] = []
    for item in found:
        if not isinstance(item, Case):
            return f"cases() returned a member that is not a Case: {item!r}"
        narrowed.append(item)
    return narrowed


_HEAVY_RE = re.compile(r"\brocqchk\b|\b_replay(?:_|\b)")
_CASE_RE = re.compile(r"\bCase\(")


def _module_profile(name: str) -> tuple[int, int]:
    """Estimate execution weight and case count for LPT scheduling and internal fan-out."""
    path = TESTS / f"{name}.py"
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError, UnicodeDecodeError:
        return 0, 0
    multiplier = 4 if _HEAVY_RE.search(raw) is not None else 1
    case_count = len(_CASE_RE.findall(raw))
    return len(raw) * multiplier, case_count


def _fanout_count(name: str, total_modules: int, worker_budget: int, case_count: int) -> int:
    if worker_budget <= 1 or not _declares(name):
        return 1
    try:
        size = (TESTS / f"{name}.py").stat().st_size
    except OSError:
        return 1
    if total_modules == 1:
        return min(worker_budget, max(1, case_count))
    if size > 80_000 and worker_budget >= 6:
        return min(6, worker_budget, max(1, case_count))
    if size > 40_000 and worker_budget >= 4:
        return min(4, worker_budget, max(1, case_count))
    return 1


def _run_cases(name: str, cases: list[Case] | str, slow: bool,
               lanes: frozenset[Lane], share: Shard | None = None, *,
               emit: bool = True) -> ModuleReport:
    """Run a module's selected cases (or `share`'s stride before `--slow` and lane filtering)."""
    rep = ModuleReport()
    if isinstance(cases, str):
        rep.failure_messages.append(cases)
        if emit:
            rep.report(name, "module error(s):", [cases])
        else:
            rep.findings += 1
        return rep

    listed = len(cases)
    failures: list[str] = []
    for case in cases if share is None else share.share(cases):
        if case.slow and not slow:
            rep.skipped_slow += 1
            continue
        if case.lane not in lanes:
            rep.skipped_lane += 1
            continue
        rep.cases += 1
        try:
            case.fn()
        except (Exception, SystemExit) as err:  # an unexpected exit is a failed case
            failures.append(f"{case.name}: {err}")
    rep.failure_messages.extend(failures)
    if emit:
        rep.report(name, "failure(s):", failures,
                   ok=f"{rep.cases} case(s)"
                   + ("" if share is None else f", this shard's share of {listed}"))
        if rep.skipped_slow or rep.skipped_lane:
            rep.line(f"       skipped: {rep.skipped_slow} slow case(s), "
                     f"{rep.skipped_lane} case(s) for unavailable lanes")
    else:
        rep.findings += len(failures)
    return rep


def _run_module(name: str, slow: bool, lanes: frozenset[Lane], shard: Shard | None = None,
                splits: frozenset[str] = frozenset(), *,
                virtual_shard: Shard | None = None) -> ModuleReport:
    """Load and run one module, retaining its captured output on failure. Under `shard`,
    a module named in `splits` runs that shard's share of its cases."""
    split = name in splits
    started = time.perf_counter()
    output = StringIO()
    with redirect_stdout(output), redirect_stderr(output):
        active_share = virtual_shard if virtual_shard is not None else (shard if split else None)
        report = _run_cases(
            name,
            _load(name, None if shard is None else split),
            slow,
            lanes,
            active_share,
            emit=virtual_shard is None,
        )
    if report.findings:
        lines = output.getvalue().splitlines()
        if virtual_shard is None:
            report.out.extend(lines)
        else:
            report.captured_lines.extend(lines)
    report.seconds = time.perf_counter() - started
    return report


def _run_work_item(
    item: tuple[str, Shard | None],
    *,
    slow: bool,
    lanes: frozenset[Lane],
    shard: Shard | None,
    splits: frozenset[str],
) -> ModuleReport:
    name, virtual_shard = item
    return _run_module(name, slow, lanes, shard, splits, virtual_shard=virtual_shard)


def _merge_reports(name: str, parts: list[ModuleReport]) -> ModuleReport:
    if len(parts) == 1:
        return parts[0]
    merged = ModuleReport()
    failures: list[str] = []
    seen_failures: set[str] = set()
    for part in parts:
        merged.cases += part.cases
        merged.skipped_slow += part.skipped_slow
        merged.skipped_lane += part.skipped_lane
        for message in part.failure_messages:
            if message not in seen_failures:
                seen_failures.add(message)
                failures.append(message)
        merged.seconds = max(merged.seconds, part.seconds)
    merged.report(name, "failure(s):", failures, ok=f"{merged.cases} case(s)")
    if merged.skipped_slow or merged.skipped_lane:
        merged.line(f"       skipped: {merged.skipped_slow} slow case(s), "
                    f"{merged.skipped_lane} case(s) for unavailable lanes")
    if merged.findings:
        for part in parts:
            merged.out.extend(part.captured_lines)
    return merged


def run(only: str | None = None, slow: bool = False, jobs: int | None = None,
        shard: Shard | None = None, record: Path | None = None,
        require_toolchain: bool = False) -> Reporter:
    """Run the selected test suite and return the aggregated `Reporter`.

    If `record` is set, writes per-module case counts and durations to that path.
    """
    if jobs is not None and jobs < 1:
        raise ValueError("jobs must be positive")
    if only is not None and shard is not None:
        raise ValueError("--only cannot be combined with --shard")
    rep = Reporter()
    rep.line("=== tests ===")

    names = _module_names(only)
    splits = frozenset[str]()
    if shard is not None:
        total = len(names)
        try:
            selected = shard.select(names)
        except ValueError as err:
            rep.report("tests", "invalid partition:", [str(err)])
            return rep
        # Partition over all modules before separating split modules so adding
        # INDEPENDENT_CASES to a module does not shift other modules between shards.
        splits = frozenset(name for name in names if _declares(name))
        whole = [name for name in selected if name not in splits]
        rep.line(f"shard {shard}: {len(whole)} of {total - len(splits)} modules"
                 + (f", and its share of the cases of {len(splits)} more" if splits else "")
                 + "; every shard must pass")
        names = [name for name in names if name in splits or name in whole]
    units: list[timings.Unit] = []
    executed = skipped_slow = skipped_lane = 0
    if not names:
        rep.report("tests", "empty suite:",
                   ["nothing under tools/tests/ matches test_*.py"
                    + (f" and --only '{only}'" if bool(only) else "")])
    else:
        # Probe runnable lanes once before spawning workers.
        lanes = _lanes()
        if require_toolchain and "toolchain" not in lanes:
            rep.report("tests", "required lane unavailable:",
                       [f"the native toolchain lane requires Linux and opam switch {env.SAIL_SWITCH}"])
            return rep
        default_jobs = (
            min(8, os.process_cpu_count() or 1)
            if sys.platform == "win32"
            else (os.process_cpu_count() or 1)
        )
        worker_budget = jobs or default_jobs
        work_entries: list[tuple[int, int, str, Shard | None]] = []
        for module_index, name in enumerate(names):
            weight, case_count = _module_profile(name)
            fanout = _fanout_count(name, len(names), worker_budget, case_count) if shard is None else 1
            if fanout > 1:
                per_slice = max(1, weight // fanout)
                work_entries.extend(
                    (per_slice, module_index, name, Shard(slice_index, fanout))
                    for slice_index in range(1, fanout + 1)
                )
            else:
                work_entries.append((weight, module_index, name, None))
        scheduled_order = sorted(
            range(len(work_entries)),
            key=lambda idx: (-work_entries[idx][0], work_entries[idx][1]),
        )
        scheduled_items = [(work_entries[idx][2], work_entries[idx][3]) for idx in scheduled_order]
        workers = min(worker_budget, len(scheduled_items))
        # Use spawn on all platforms so workers never inherit live threads or module patches.
        with ProcessPoolExecutor(max_workers=workers,
                                 mp_context=multiprocessing.get_context("spawn")) as pool:
            mapped = list(pool.map(partial(_run_work_item, slow=slow, lanes=lanes,
                                           shard=shard, splits=splits), scheduled_items))
        grouped: dict[str, list[ModuleReport]] = {name: [] for name in names}
        restored: list[ModuleReport | None] = [None] * len(work_entries)
        for sched_pos, part in zip(scheduled_order, mapped, strict=True):
            restored[sched_pos] = part
        for entry, maybe_part in zip(work_entries, restored, strict=True):
            assert maybe_part is not None  # noqa: S101
            grouped[entry[2]].append(maybe_part)
        for name in names:
            part = _merge_reports(name, grouped[name])
            rep.out.extend(part.out)
            rep.findings += part.findings
            executed += part.cases
            skipped_slow += part.skipped_slow
            skipped_lane += part.skipped_lane
            units.append({"kind": "module", "name": name, "cases": part.cases,
                          "skipped_slow": part.skipped_slow,
                          "skipped_lane": part.skipped_lane,
                          "share": str(shard) if name in splits else None,
                          "seconds": round(part.seconds, 3)})
    timings.write(record, units)
    rep.line(f"{executed} case(s) run; {skipped_slow} slow case(s) skipped; "
             f"{skipped_lane} case(s) skipped for unavailable lanes.")

    if rep.findings:
        rep.line(f"{rep.findings} finding(s).")
    else:
        rep.line("the tools behave as their tests hold them to.")
    return rep


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(suggest_on_error=True, description="Run the tools' own behavioral tests.")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--only", metavar="SUBSTRING",
                        help="run only the modules whose name carries this")
    selection.add_argument("--shard", type=sharding.parse, metavar="INDEX/TOTAL",
                           help="run a disjoint partition of the discovered modules, and "
                                "this shard's share of the cases of each module declaring "
                                "INDEPENDENT_CASES = True")
    parser.add_argument("--slow", action="store_true",
                        help="include the cases marked slow")
    parser.add_argument("--require-toolchain", action="store_true",
                        help="fail unless the native toolchain lane is available")
    parser.add_argument("--jobs", type=int,
                        help="worker processes (default: available CPUs on Linux, capped at eight on Windows)")
    args = parser.parse_args(argv)
    if args.jobs is not None and args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.only is not None and not args.only.strip():
        parser.error("--only requires a nonempty module-name substring")

    report = run(only=args.only, slow=args.slow, jobs=args.jobs, shard=args.shard,
                 record=timings.claim(), require_toolchain=args.require_toolchain)
    print("\n".join(report.out))
    return 1 if report.findings else 0
