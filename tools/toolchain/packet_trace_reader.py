# SPDX-License-Identifier: Apache-2.0
"""Independent Perfetto import of a deterministic packet compiler trace."""

from pathlib import Path
from typing import cast

from toolchain import packet_trace, trace_viewer
from toolchain.hashing import file_sha256

type Object = dict[str, object]

OS_PID_SQL = ("SELECT s.name, a.int_value AS os_pid FROM slice s JOIN args a USING (arg_set_id) "
              "WHERE a.key = 'args.os_pid' ORDER BY s.ts")
QUERIES = {
    "slices": (trace_viewer.SLICES_SQL, [
        ["name", "ts", "dur", "depth", "tid", "pid"],
        ["packet", "0", "220000", "0", "1", "1"],
        ["parse", "20000", "10000", "1", "1", "1"],
        ["resolve-and-elaborate", "40000", "10000", "1", "1", "1"],
        ["generate-gallina", "60000", "10000", "1", "1", "1"],
        ["proof-compile", "80000", "30000", "1", "1", "1"],
        ["rocq-compile-process", "90000", "10000", "0", "1", "2"],
        ["proof-audit", "120000", "30000", "1", "1", "1"],
        ["rocq-audit-process", "130000", "10000", "0", "1", "3"],
        ["proof-kernel", "160000", "30000", "1", "1", "1"],
        ["rocqchk-process", "170000", "10000", "0", "1", "4"],
        ["lower-to-c", "200000", "10000", "1", "1", "1"],
    ]),
    "counters": (trace_viewer.COUNTERS_SQL, [["name", "ts", "value"], ["source_bytes bytes", "10000", "17"]]),
    "processes": (OS_PID_SQL, [["name", "os_pid"], ["rocq-compile-process", "102"],
                              ["rocq-audit-process", "103"], ["rocqchk-process", "104"]]),
}


def _harness() -> str:
    root = Path(__file__).resolve().parent
    return packet_trace.digest({name: file_sha256(root / name) for name in (
        "atomic.py", "packet_trace_reader.py", "packet_trace.py", "trace_viewer.py", "compiler_trace.py", "hashing.py", "jsonutil.py", "cli/holdfast.py")})


def _fixture() -> Object:
    document = packet_trace.fixture()
    packet_trace.validate(document, "a" * 64, 17,
                          {"rocq-compile-process": 102, "rocq-audit-process": 103, "rocqchk-process": 104})
    return document


def check_current(executable: Path, report: Object) -> None:
    if trace_viewer.reader_identity(executable) != report["reader"] or _harness() != report["harness_sha256"]:
        raise ValueError("packet trace reader or harness changed during qualification")


def qualify(executable: Path) -> Object:
    executable = executable.resolve(strict=True)
    reader, harness = trace_viewer.reader_identity(executable), _harness()
    fixture = _fixture()
    version = trace_viewer._run(executable, ["--version"])
    trace_viewer.check_version(version)
    report: Object = {"schema": 1, "scope": "packet-trace-independent-importer", "accepted": True,
                      "reader": reader, "harness_sha256": harness, "version": version, "trace": fixture,
                      "queries": trace_viewer.read_queries(executable, fixture, QUERIES)}
    report["binding_sha256"] = packet_trace.digest(report)
    check_current(executable, report)
    return report


def validate(document: object, executable: Path) -> Object:
    fields = {"schema", "scope", "accepted", "reader", "harness_sha256", "version", "trace", "queries", "binding_sha256"}
    if not isinstance(document, dict) or set(document) != fields:
        raise ValueError("invalid packet trace importer report")
    report = cast("Object", document)
    if (type(report["schema"]) is not int or report["schema"] != 1 or report["accepted"] is not True
            or report["scope"] != "packet-trace-independent-importer"
            or report["binding_sha256"] != packet_trace.digest({k: v for k, v in report.items() if k != "binding_sha256"})
            or packet_trace.digest(report["trace"]) != packet_trace.digest(_fixture())):
        raise ValueError("stale or malformed packet trace importer evidence")
    trace_viewer.check_version(report["version"])
    trace_viewer.check_queries(report["queries"], QUERIES)
    check_current(executable, report)
    return report
