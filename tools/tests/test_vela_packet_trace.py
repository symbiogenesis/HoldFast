# SPDX-License-Identifier: Apache-2.0
"""Independent packet phase ordering, child process identity and refusal controls."""

import copy
import sys
import tempfile
from pathlib import Path
from typing import cast

from tests.harness import Case, ensure
from toolchain import first_slice, packet_trace

INDEPENDENT_CASES = True
_PIDS = {"rocq-compile-process": 102, "rocq-audit-process": 103, "rocqchk-process": 104}


def _inventory_and_rebinding() -> None:
    original = packet_trace.fixture()
    packet_trace.validate(original, "a" * 64, 17, _PIDS)
    events = cast("list[dict[str, object]]", original["traceEvents"])
    ensure([event["ts"] for event in events] == [0, 10, 20, 40, 60, 80, 90, 120, 130, 160, 170, 200],
           "packet compiler, proof and subprocess intervals changed")
    for index, update in ((0, {"dur": 201}), (1, {"args": {"bytes": 18}}),
                          (3, {"ts": 29}), (5, {"dur": 12}), (6, {"pid": 1}),
                          (8, {"args": {"os_pid": 102}}), (11, {"ts": True})):
        altered = copy.deepcopy(original)
        cast("list[dict[str, object]]", altered["traceEvents"])[index].update(update)
        manifest = cast("dict[str, object]", altered["vela"])
        manifest.pop("binding_sha256")
        manifest["binding_sha256"] = packet_trace.digest(altered)
        try:
            packet_trace.validate(altered, "a" * 64, 17, _PIDS)
        except ValueError:
            continue
        raise AssertionError("altered compiler timeline survived a matching document digest")
    try:
        packet_trace.validate(original, "b" * 64, 17, _PIDS)
    except ValueError:
        pass
    else:
        raise AssertionError("packet trace survived a changed receipt")


def _partial_and_process() -> None:
    ticks = iter((1_000, 2_000, 1_000))
    limited = packet_trace.Recorder(clock=lambda: next(ticks), limit=1)
    with limited.span("packet"):
        limited.source_size(17)
    manifest = cast("dict[str, object]", limited.export("a" * 64, "cancelled")["vela"])
    ensure(manifest["complete"] is False and manifest["clock_fault"] is True
           and manifest["dropped_events"] == 1 and manifest["outcome"] == "cancelled",
           "cancelled, truncated or backwards clock produced a complete trace")
    recorder = packet_trace.Recorder()
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        steps: list[dict[str, object]] = []
        executable = str(Path(sys.base_prefix) / "python.exe") if sys.platform == "win32" else sys.executable
        pid = int(first_slice._run([executable, "-c", "import os; print(os.getpid())"], directory,
                                   directory / "FirstSlice.kernel.log", steps, timing=recorder))
        ensure(steps[0]["observed_pid"] == pid and recorder.events[1]["args"] == {"os_pid": pid}
               and recorder.events[1]["name"] == "rocqchk-process",
               "observed worker track differs from the child's own process identity")


def cases() -> list[Case]:
    return [Case("packet timeline inventory, source and proof worker bindings", _inventory_and_rebinding),
            Case("packet trace cancellation, truncation, clock fault and real process", _partial_and_process)]
