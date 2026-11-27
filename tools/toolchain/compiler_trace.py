# SPDX-License-Identifier: Apache-2.0
"""Bounded, input-bound Chrome Trace Event recordings of the pure compiler."""

import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import time
from collections.abc import Callable, Generator
from contextlib import contextmanager
from importlib import import_module
from pathlib import Path
from typing import cast

from toolchain import trace_runtime
from toolchain.hashing import file_sha256
from toolchain.jsonutil import canonical_bytes, exceeds_nesting, json_digest, unique_object

MAX_EVENTS = 4096
MAX_TRACE_BYTES = 2_097_152
MAX_DEPTH = 64
MAX_TIME = 2**53 - 1
_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
type Object = dict[str, object]


def _python_identity() -> Object:
    descriptor = {"executable_sha256": file_sha256(Path(sys.executable)),
                  "version": sys.version, "implementation": platform.python_implementation(),
                  "platform": platform.system(), "machine": platform.machine()}
    descriptor["runtime_sha256"] = json_digest({"files": trace_runtime.identity(), "flags": str(sys.flags),
                                               "search_path": sys.path, "kernel": platform.version()})
    return dict(descriptor)


def _parser_images_identity(pid: int, executable: Path) -> str:
    process = Path(f"/proc/{pid}")
    with executable.open("rb") as stream:
        header = stream.readline(4096)
    with (process / "cmdline").open("rb") as stream:
        command = stream.read(65537)
    if len(command) > 65536:
        raise ValueError("live worker does not execute the selected checked parser")
    args = command.split(b"\0")
    if header.startswith(b"\x7fELF"):
        if args != [os.fsencode(executable), b"--batch", b""] or not executable.samefile(process / "exe"):
            raise ValueError("live worker does not execute the selected checked parser")
    elif header.startswith(b"#!/") and header.endswith(b"\n"):
        interpreter = Path(os.fsdecode(header[2:-1]))
        if (args != [os.fsencode(interpreter), os.fsencode(executable), b"--batch", b""]
                or not interpreter.samefile(process / "exe")):
            raise ValueError("live worker does not execute the selected checked parser")
    else:
        raise ValueError("checked parser has no supported executable format")
    return trace_runtime.file_identity(trace_runtime.process_images(pid))


def _native_runtime_identity(pid: int) -> Object:
    """Observe the checked parser's validated executable outside measured intervals."""
    checked = import_module("toolchain.parser_checked")
    compiled = checked.ensure_checked_build()
    parser_digest = file_sha256(compiled.executable)
    outputs = cast("dict[str, str]", compiled.receipt["generated_sha256"])
    if parser_digest != outputs["holdfast-parser"]:
        raise ValueError("checked parser executable changed during runtime observation")
    return {"python": _python_identity(),
            "parser_sha256": parser_digest,
            "parser_images_sha256": _parser_images_identity(pid, compiled.executable)}


def _runtime_identity(root: Path) -> Object:
    checked = import_module("toolchain.parser_checked")
    transport_pid, parser_pid = checked.trace_worker_pids()
    if sys.platform == "linux":
        if transport_pid != parser_pid:
            raise ValueError("unexpected checked parser process identity")
        return _native_runtime_identity(parser_pid)
    if sys.platform != "win32":
        raise ValueError("unsupported trace runtime platform")
    script = ("import json, sys; sys.path.insert(0, 'tools'); "
              "from toolchain.compiler_trace import _native_runtime_identity; "
              "print(json.dumps(_native_runtime_identity(int(sys.argv[1])), sort_keys=True))")
    try:
        result = subprocess.run(
            ["wsl", "-u", "root", "-e", "/usr/bin/env", "OPAMROOT=/root/.opam",
             "/root/build/venv-linux/bin/python", "-c", script, str(parser_pid)],
            cwd=root, stdin=subprocess.DEVNULL, capture_output=True, check=False, timeout=180)
    except subprocess.SubprocessError as error:
        raise ValueError("checked parser runtime identity is unavailable") from error
    if result.returncode or len(result.stdout) > 8192:
        raise ValueError("checked parser runtime identity is unavailable")
    try:
        descriptor = json.loads(result.stdout, object_pairs_hook=unique_object)
    except (ValueError, RecursionError) as error:
        raise ValueError("malformed checked parser runtime identity") from error
    if (not isinstance(descriptor, dict) or set(descriptor) != {"python", "parser_sha256", "parser_images_sha256"}
            or not isinstance(descriptor["python"], dict)
            or set(descriptor["python"]) != {"executable_sha256", "runtime_sha256", "version", "implementation", "platform", "machine"}
            or any(not isinstance(value, str) or not value for value in descriptor["python"].values())
            or not _SHA256.fullmatch(descriptor["python"]["executable_sha256"])
            or not _SHA256.fullmatch(descriptor["python"]["runtime_sha256"])
            or any(not isinstance(descriptor[field], str) or not _SHA256.fullmatch(descriptor[field])
                   for field in ("parser_sha256", "parser_images_sha256"))):
        raise ValueError("malformed checked parser runtime identity")
    descriptor["transport_images_sha256"] = trace_runtime.file_identity(trace_runtime.process_images(transport_pid))
    return cast("Object", descriptor)


def producer_identity() -> str:
    """Bind local implementation, dependency locks and selected runtime executables."""
    root = Path(__file__).resolve().parents[1]
    paths = sorted((root / "toolchain").rglob("*.py"))
    paths.extend(sorted((root / "toolchain" / "parser").glob("*")))
    owners = ("run.py", "pyproject.toml", "uv.lock", "opam/rocq.lock", "opam/sail.lock")
    inputs = {path.relative_to(root).as_posix(): file_sha256(path)
              for path in paths if path.is_file()}
    inputs.update({name: file_sha256(root / name) for name in owners})
    native = _runtime_identity(root.parent)
    return json_digest({"files": inputs, "host": _python_identity(), "native": native})


class _BaseChromeRecorder:
    """Shared bounded monotonic microsecond Chrome Trace Event buffer."""

    def __init__(self, *, max_events: int, clock: Callable[[], int] = time.perf_counter_ns) -> None:
        self.max_events = max_events
        self.clock = clock
        self.origin: int | None = None
        self.last = 0
        self.last_reading = 0
        self.events: list[Object] = []
        self.dropped = 0
        self.clock_fault = False

    def _now(self) -> int:
        reading = self.clock()
        if type(reading) is not int or reading < self.last_reading:
            self.clock_fault = True
            return self.last
        self.last_reading = reading
        if self.origin is None:
            self.origin = reading
        current = (reading - self.origin) // 1000
        if not self.last <= current <= MAX_TIME:
            self.clock_fault = True
            return self.last
        self.last = current
        return current

    def _retain(self, event: Object) -> bool:
        if len(self.events) >= self.max_events:
            self.dropped += 1
            return False
        self.events.append(event)
        return True

    @staticmethod
    def _span_event(name: str, start: int, *, pid: int = 1, args: Object | None = None) -> Object:
        event: Object = {"name": name, "cat": "holdfast.compiler", "ph": "X", "pid": pid,
                         "tid": 1, "ts": start, "dur": 0}
        if args is not None:
            event["args"] = args
        return event

    @staticmethod
    def _counter_event(name: str, ts: int, args: Object, *, pid: int = 1) -> Object:
        return {"name": name, "cat": "holdfast.compiler", "ph": "C", "pid": pid,
                "tid": 1, "ts": ts, "args": args}


class Recorder(_BaseChromeRecorder):
    """One synchronous worker; bounded complete events retain nested start order."""

    def __init__(self, *, max_events: int = MAX_EVENTS,
                 clock: Callable[[], int] = time.perf_counter_ns) -> None:
        if type(max_events) is not int or not 1 <= max_events <= MAX_EVENTS:
            raise ValueError(f"max_events must be between 1 and {MAX_EVENTS}")
        super().__init__(max_events=max_events, clock=clock)
        self.depth = 0
        self.overhead = 0
        self.declarations = 0

    @contextmanager
    def span(self, name: str) -> Generator[None]:
        if name not in {"compile", "parse", "checked-parse", "syntax-decode", "elaborate-and-emit"}:
            raise ValueError("unsupported pure compiler phase")
        with self._span(name):
            yield

    @contextmanager
    def declaration(self, name: str, kind: str, line: int, column: int) -> Generator[None]:
        if (not isinstance(name, str) or not _IDENTIFIER.fullmatch(name)
                or kind not in {"function", "constant"}
                or any(type(value) is not int or not 1 <= value <= 65_536 for value in (line, column))):
            raise ValueError("invalid compiler declaration site")
        self.declarations += 1
        with self._span("declaration", {"name": name, "kind": kind, "line": line, "column": column}):
            yield

    @contextmanager
    def _span(self, name: str, details: Object | None = None) -> Generator[None]:
        if self.depth >= MAX_DEPTH:
            raise ValueError("trace nesting exceeds limit")
        overhead = time.perf_counter_ns()
        start = self._now()
        event = self._span_event(name, start, args=details)
        retained = self._retain(event)
        self.depth += 1
        self.overhead += time.perf_counter_ns() - overhead
        try:
            yield
        finally:
            overhead = time.perf_counter_ns()
            end = self._now()
            if retained:
                event["dur"] = end - start
            self.depth -= 1
            self.overhead += time.perf_counter_ns() - overhead

    def counter(self, name: str, value: int) -> None:
        if name not in {"source_bytes", "gallina_bytes"} or type(value) is not int or not 0 <= value <= MAX_TIME:
            raise ValueError("unsupported counter or value")
        overhead = time.perf_counter_ns()
        self._retain(self._counter_event(name, self._now(), {"bytes": value}))
        self.overhead += time.perf_counter_ns() - overhead

    def export(self, source: bytes, producer: str, *, outcome: str) -> Object:
        if outcome not in {"success", "refused", "cancelled"} or not _SHA256.fullmatch(producer):
            raise ValueError("invalid trace outcome or producer identity")
        manifest: Object = {
            "schema": 3, "scope": "pure-compiler-timing", "clock": "perf_counter_ns",
            "timestamp_unit": "microseconds", "origin": "recording-relative",
            "worker": "synchronous-host-including-parser-wait", "source_sha256": hashlib.sha256(source).hexdigest(),
            "producer_sha256": producer, "max_events": self.max_events,
            "event_count": len(self.events), "dropped_events": self.dropped,
            "declaration_count": self.declarations,
            "incomplete_spans": self.depth, "clock_fault": self.clock_fault,
            "outcome": outcome, "recording_overhead_ns": self.overhead,
            "complete": outcome == "success" and not (self.dropped or self.depth or self.clock_fault),
        }
        # Copy the records so later span completion cannot mutate an exported manifest.
        document: Object = {"traceEvents": json.loads(canonical_bytes(self.events)),
                            "displayTimeUnit": "ms", "holdfast": manifest}
        manifest["binding_sha256"] = json_digest(document)
        if len(canonical_bytes(document)) > MAX_TRACE_BYTES:
            raise ValueError("trace export exceeds byte limit")
        return document


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _natural(value: object) -> bool:
    return type(value) is int and 0 <= value <= MAX_TIME


def validate(document: object, source: bytes, producer: str, *, require_complete: bool = True) -> Object:
    """Check event structure and freshness before handing a recording to a viewer.

    Hash bindings detect changed data; they supply no producer authentication.
    """
    _require(isinstance(document, dict), "trace must be an object")
    data = cast("Object", document)
    _require(set(data) == {"traceEvents", "displayTimeUnit", "holdfast"}, "unsupported trace fields")
    _require(data["displayTimeUnit"] == "ms" and isinstance(data["holdfast"], dict), "unsupported trace format")
    manifest = cast("Object", data["holdfast"])
    fields = {"schema", "scope", "clock", "timestamp_unit", "origin", "worker", "source_sha256",
              "producer_sha256", "max_events", "event_count", "dropped_events", "incomplete_spans",
              "clock_fault", "outcome", "recording_overhead_ns", "complete", "binding_sha256", "declaration_count"}
    _require(set(manifest) == fields, "unsupported manifest fields")
    binding = manifest["binding_sha256"]
    unsigned = {key: value for key, value in manifest.items() if key != "binding_sha256"}
    _require(binding == json_digest({**data, "holdfast": unsigned}), "trace binding mismatch")
    _require(type(manifest["schema"]) is int and manifest["schema"] == 3
             and manifest["scope"] == "pure-compiler-timing"
             and manifest["clock"] == "perf_counter_ns"
             and manifest["timestamp_unit"] == "microseconds"
             and manifest["origin"] == "recording-relative"
             and manifest["worker"] == "synchronous-host-including-parser-wait", "unsupported trace schema")
    _require(manifest["source_sha256"] == hashlib.sha256(source).hexdigest()
             and manifest["producer_sha256"] == producer, "stale trace input or producer")
    for name in ("max_events", "event_count", "dropped_events", "incomplete_spans", "recording_overhead_ns", "declaration_count"):
        _require(_natural(manifest[name]), f"invalid {name}")
    _require(1 <= cast("int", manifest["max_events"]) <= MAX_EVENTS, "invalid event bound")
    _require(type(manifest["complete"]) is bool and type(manifest["clock_fault"]) is bool, "invalid completeness flags")
    _require(manifest["outcome"] in ("success", "refused", "cancelled"), "invalid outcome")
    complete = manifest["outcome"] == "success" and not (
        manifest["dropped_events"] or manifest["incomplete_spans"] or manifest["clock_fault"])
    _require(manifest["complete"] == complete, "false completeness claim")
    events = data["traceEvents"]
    _require(isinstance(events, list), "events must be an array")
    events = cast("list[object]", events)
    _require(len(events) == manifest["event_count"] and len(events) <= cast("int", manifest["max_events"]), "event count mismatch")
    previous = 0
    phases: list[str] = []
    counters: dict[str, int] = {}
    spans: dict[str, tuple[int, int]] = {}
    counter_times: dict[str, int] = {}
    ordered_names: list[str] = []
    declarations: list[tuple[int, int]] = []
    previous_site = (0, 0)
    for item in events:
        _require(isinstance(item, dict), "event must be an object")
        event = cast("Object", item)
        phase = event.get("ph")
        fields = {"name", "cat", "ph", "pid", "tid", "ts", "dur" if phase == "X" else "args"}
        if event.get("name") == "declaration":
            fields.add("args")
        _require(phase in ("X", "C") and set(event) == fields, "unsupported event fields")
        _require(type(event["pid"]) is int and event["pid"] == 1
                 and type(event["tid"]) is int and event["tid"] == 1
                 and event["cat"] == "holdfast.compiler", "invalid worker")
        _require(_natural(event["ts"]), "invalid timestamp")
        start = cast("int", event["ts"])
        _require(start >= previous, "events out of start order")
        previous = start
        if phase == "X":
            _require(event["name"] in ("compile", "parse", "checked-parse", "syntax-decode", "elaborate-and-emit", "declaration") and _natural(event["dur"]), "invalid phase or duration")
            end = start + cast("int", event["dur"])
            _require(end <= MAX_TIME, "overflowing span")
            name = cast("str", event["name"])
            if name == "declaration":
                site = _declaration_site(event["args"], source)
                _require(site > previous_site, "declaration sites are duplicated or out of source order")
                previous_site = site
                declarations.append((start, end))
                continue
            _require(name not in spans, "duplicate compiler phase")
            spans[name] = (start, end)
            phases.append(name)
        else:
            name = event["name"]
            args = event["args"]
            _require(name in ("source_bytes", "gallina_bytes") and isinstance(args, dict), "unsupported counter")
            args = cast("Object", args)
            _require(set(args) == {"bytes"} and _natural(args["bytes"]), "invalid counter value")
            _require(name not in counters, "duplicate counter")
            counters[cast("str", name)] = cast("int", args["bytes"])
            counter_times[cast("str", name)] = start
        ordered_names.append(cast("str", event["name"]))
    count = cast("int", manifest["declaration_count"])
    _require(len(declarations) <= count <= len(declarations) + cast("int", manifest["dropped_events"]),
             "declaration inventory mismatch")
    if complete:
        _require(phases == ["compile", "parse", "checked-parse", "syntax-decode", "elaborate-and-emit"]
                 and set(counters) == {"source_bytes", "gallina_bytes"}, "incomplete compiler phase inventory")
        _require(counters["source_bytes"] == len(source), "source byte counter mismatch")
        _require(ordered_names == ["compile", "source_bytes", "parse", "checked-parse", "syntax-decode", "elaborate-and-emit", "gallina_bytes"], "incorrect compiler event order")
        _require(0 == spans["compile"][0] <= counter_times["source_bytes"]
                 <= spans["parse"][0] <= spans["checked-parse"][0] <= spans["checked-parse"][1]
                 <= spans["syntax-decode"][0] <= spans["syntax-decode"][1] <= spans["parse"][1]
                 <= spans["elaborate-and-emit"][0] <= spans["elaborate-and-emit"][1]
                 <= counter_times["gallina_bytes"] <= spans["compile"][1], "crossing or incorrectly nested compiler spans")
        previous_end = spans["elaborate-and-emit"][0]
        for start, end in declarations:
            _require(previous_end <= start <= end <= spans["elaborate-and-emit"][1],
                     "crossing or incorrectly nested declaration spans")
            previous_end = end
    _require(not require_complete or complete, "recording is incomplete")
    return manifest


def _declaration_site(value: object, source: bytes) -> tuple[int, int]:
    _require(isinstance(value, dict), "invalid declaration details")
    details = cast("Object", value)
    _require(set(details) == {"name", "kind", "line", "column"}, "unsupported declaration details")
    name = details["name"]
    _require(isinstance(name, str) and _IDENTIFIER.fullmatch(name) is not None
             and details["kind"] in ("function", "constant"), "invalid declaration name or kind")
    line, column = details["line"], details["column"]
    _require(all(type(value) is int and 1 <= value <= 65_536 for value in (line, column)),
             "invalid declaration coordinates")
    line, column = cast("int", line), cast("int", column)
    try:
        lines = source.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n").split("\n")
    except UnicodeDecodeError as error:
        raise ValueError("declaration source is not UTF-8") from error
    _require(line <= len(lines), "declaration line outside source")
    tail = lines[line - 1][column - 1:]
    match = re.match(r"[A-Za-z_][A-Za-z0-9_]*", tail)
    _require(match is not None and match.group() == name
             and (column == 1 or not re.match(r"[A-Za-z0-9_]", lines[line - 1][column - 2])),
             "declaration name does not match its source site")
    return line, column


def decode(raw: bytes) -> Object:
    if len(raw) > MAX_TRACE_BYTES:
        raise ValueError("trace exceeds byte limit")
    if exceeds_nesting(raw, 8):
        raise ValueError("trace nesting exceeds limit")

    def reject(value: str) -> object:
        raise ValueError(f"unsupported trace number: {value}")
    value = json.loads(raw, object_pairs_hook=unique_object, parse_float=reject, parse_constant=reject)
    _require(isinstance(value, dict), "trace must be an object")
    return cast("Object", value)
