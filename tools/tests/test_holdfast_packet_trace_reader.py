# SPDX-License-Identifier: Apache-2.0
"""Refuse altered packet worker, clock, counter and process observations in retained imports."""

import copy
import csv
import hashlib
import tempfile
from io import StringIO
from pathlib import Path
from typing import cast
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import packet_trace, packet_trace_reader, trace_viewer


def _observations() -> None:
    reader = packet_trace_reader
    with tempfile.TemporaryDirectory(prefix="packet-viewer-") as folder:
        executable = Path(folder) / "reader"
        executable.write_bytes(b"test importer")
        digest = hashlib.sha256(executable.read_bytes()).hexdigest()

        def run(path: Path, args: list[str]) -> trace_viewer.Object:
            ensure(path == executable, "another reader was invoked")
            if args == ["--version"]:
                stdout = "Perfetto v58.2-add693d8b (add693d8b338ba9599dbcbc3e300b1ab8c000897)"
            else:
                rows = next(rows for sql, rows in reader.QUERIES.values() if sql == args[2])
                csv_output = StringIO()
                csv.writer(csv_output).writerows(rows)
                stdout = csv_output.getvalue()
            return {"returncode": 0, "stdout": stdout, "stderr": ""}

        with (patch.object(trace_viewer, "PINS", {"test": digest}),
              patch.object(trace_viewer, "_run", side_effect=run) as launch):
            report = reader.qualify(executable)
            ensure(reader.validate(report, executable) == report and launch.call_count == 4,
                   "report did not retain all three reader queries independently of replay")
            for subject, before, after in (
                    ("slices", "200000,10000", "200000,9999"),
                    ("slices", "90000,10000,0,1,2", "90000,10000,0,1,1"),
                    ("counters", "10000,17", "10000,16"),
                    ("processes", "rocq-audit-process,103", "rocq-audit-process,102")):
                altered = copy.deepcopy(report)
                query = cast("dict[str, trace_viewer.Object]", altered["queries"])[subject]
                transcript = cast("trace_viewer.Object", query["transcript"])
                stdout = cast("str", transcript["stdout"])
                ensure(before in stdout, "test failed to locate its intended observation")
                transcript["stdout"] = stdout.replace(before, after)
                query["rows"] = list(csv.reader(StringIO(cast("str", transcript["stdout"]))))
                altered["binding_sha256"] = packet_trace.digest(
                    {key: value for key, value in altered.items() if key != "binding_sha256"})
                try:
                    reader.validate(altered, executable)
                except ValueError:
                    continue
                raise AssertionError(f"accepted altered {subject} in a rehashed report")


def cases() -> list[Case]:
    return [Case("reader-binds-child-processes-worker-tracks-timestamps-and-source-bytes", _observations)]
