# SPDX-License-Identifier: Apache-2.0
"""Bounded Chrome Trace Event recording for the packet frontend, proof and C lowering."""

import time
from collections.abc import Callable, Generator
from contextlib import contextmanager

from toolchain.compiler_trace import MAX_TIME, _BaseChromeRecorder
from toolchain.jsonutil import json_digest as digest

type Object = dict[str, object]

# The proof subprocess tracks measure the parent's wait on a particular live child.
PHASES = ("packet", "source_bytes", "parse", "resolve-and-elaborate", "generate-gallina",
          "proof-compile", "rocq-compile-process", "proof-audit", "rocq-audit-process",
          "proof-kernel", "rocqchk-process", "lower-to-c")
CHILDREN = {"rocq-compile-process": 2, "rocq-audit-process": 3, "rocqchk-process": 4}
PROOF_STEPS = {"FirstSlice.compile.log": ("proof-compile", "rocq-compile-process"),
               "FirstSlice.assumptions.log": ("proof-audit", "rocq-audit-process"),
               "FirstSlice.kernel.log": ("proof-kernel", "rocqchk-process")}
FILENAME = "packet-trace.json"
MAX_BYTES = 16_384


def subjects(receipt: Object) -> str:
    """Bind this development recording to the qualification's source, outputs and producers."""
    return digest({key: receipt[key] for key in (
        "producer_revision", "inputs", "parser_outputs", "parser", "execution_inputs", "runtime", "trace_runtime_sha256",
        "toolchain", "source_sha256", "gallina_sha256", "lowered_c_sha256")})


class Recorder(_BaseChromeRecorder):
    def __init__(self, clock: Callable[[], int] = time.perf_counter_ns, *, limit: int = len(PHASES)) -> None:
        if type(limit) is not int or not 1 <= limit <= len(PHASES):
            raise ValueError("invalid packet trace limit")
        super().__init__(max_events=limit, clock=clock)
        self.limit = limit
        self.open = 0

    @contextmanager
    def span(self, name: str, os_pid: int | None = None) -> Generator[None]:
        if name not in PHASES or name == "source_bytes" or (name in CHILDREN) != (os_pid is not None):
            raise ValueError("invalid packet trace phase or worker")
        start = self._now()
        args: Object | None = {"os_pid": os_pid} if os_pid is not None else None
        event = self._span_event(name, start, pid=CHILDREN.get(name, 1), args=args)
        self._retain(event)
        self.open += 1
        try:
            yield
        finally:
            event["dur"] = self._now() - start
            self.open -= 1

    def source_size(self, size: int) -> None:
        self._retain(self._counter_event("source_bytes", self._now(), {"bytes": size}))

    def export(self, binding: str, outcome: str) -> Object:
        if outcome not in {"passed", "refused", "cancelled"}:
            raise ValueError("invalid packet trace outcome")
        manifest: Object = {"schema": 1, "scope": "packet-compiler-timing", "clock": "perf_counter_ns",
                            "unit": "us", "subjects_sha256": binding, "outcome": outcome,
                            "dropped_events": self.dropped, "open_spans": self.open, "clock_fault": self.clock_fault,
                            "complete": outcome == "passed" and len(self.events) == len(PHASES)
                                        and not (self.open or self.dropped or self.clock_fault)}
        document: Object = {"displayTimeUnit": "ms", "traceEvents": [dict(e) for e in self.events], "holdfast": manifest}
        manifest["binding_sha256"] = digest(document)
        return document


def validate(document: Object, binding: str, source_size: int, pids: dict[str, int]) -> None:
    """Check the exact complete event inventory and its host-observed child intervals."""
    events, raw = document.get("traceEvents"), document.get("holdfast")
    if (set(document) != {"displayTimeUnit", "traceEvents", "holdfast"} or document["displayTimeUnit"] != "ms"
            or not isinstance(raw, dict) or not isinstance(events, list) or len(events) != len(PHASES)):
        raise ValueError("invalid packet trace inventory")
    manifest = {key: value for key, value in raw.items() if key != "binding_sha256"}
    expected = {"schema": 1, "scope": "packet-compiler-timing", "clock": "perf_counter_ns", "unit": "us",
                "subjects_sha256": binding, "outcome": "passed", "dropped_events": 0, "open_spans": 0,
                "clock_fault": False, "complete": True}
    if (digest(manifest) != digest(expected) or raw.get("binding_sha256") != digest({**document, "holdfast": manifest})
            or set(pids) != set(CHILDREN) or any(type(pid) is not int or pid <= 0 for pid in pids.values())):
        raise ValueError("incomplete or stale packet trace")
    spans: dict[str, tuple[int, int]] = {}
    previous = 0
    for name, event in zip(PHASES, events, strict=True):
        if not isinstance(event, dict) or event.get("name") != name:
            raise ValueError("invalid packet trace event")
        start, duration = event.get("ts"), event.get("dur", 0)
        if (type(start) is not int or type(duration) is not int or not previous <= start <= MAX_TIME
                or not 0 <= duration <= MAX_TIME - start):
            raise ValueError("invalid packet trace timing")
        previous = start
        spans[name] = (start, start + duration)
        wanted: Object = {"ph": "X", "cat": "holdfast.compiler", "name": name, "pid": CHILDREN.get(name, 1),
                          "tid": 1, "ts": start, "dur": duration}
        if name == "source_bytes":
            wanted.pop("dur")
            wanted.update(ph="C", args={"bytes": source_size})
        if name in CHILDREN:
            wanted["args"] = {"os_pid": pids[name]}
        if digest(event) != digest(wanted):
            raise ValueError("packet trace worker, counter or phase mismatch")
    if spans["packet"][0] != 0:
        raise ValueError("invalid packet trace origin")
    host_end = 0
    for index, name in enumerate(PHASES[1:], 1):
        start, end = spans[name]
        if name in CHILDREN:
            parent_start, parent_end = spans[PHASES[index - 1]]
            if not parent_start <= start <= end <= parent_end:
                raise ValueError("packet proof worker escapes its parent phase")
        else:
            if not host_end <= start <= end <= spans["packet"][1]:
                raise ValueError("crossing packet compiler phases")
            host_end = end


def fixture() -> Object:
    ticks = iter(range(0, 1_000_000, 10_000))
    recorder = Recorder(clock=lambda: next(ticks))
    with recorder.span("packet"):
        recorder.source_size(17)
        for name in ("parse", "resolve-and-elaborate", "generate-gallina"):
            with recorder.span(name):
                pass
        for parent, child in zip(("proof-compile", "proof-audit", "proof-kernel"), CHILDREN, strict=True):
            with recorder.span(parent), recorder.span(child, 100 + CHILDREN[child]):
                pass
        with recorder.span("lower-to-c"):
            pass
    return recorder.export("a" * 64, "passed")
