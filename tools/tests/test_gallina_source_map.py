# SPDX-License-Identifier: Apache-2.0
"""Independent ECMA-426 coordinate and retained-file controls."""

import hashlib
import json
import tempfile
from contextlib import nullcontext
from pathlib import Path
from unittest.mock import Mock, patch

from tests.harness import Case, ensure
from toolchain import gallina_source_map as maps
from toolchain.elaborate_types import GallinaOrigin


def _coordinates() -> None:
    source = "x\r\n🧭 y\rc".encode()
    # Generated order visits c (2,0), then y (1,3). Two UTF-16 units in
    # the generated prefix end the first mapped segment at column 2.
    origins = [GallinaOrigin(1, 1, (10, 11), (10, 11), "declaration"),
               GallinaOrigin(3, 1, (8, 9), (8, 9), "word-equation")]
    record = json.loads(maps._source_map("in #1.vela", source, "stub\n🗺\n\nabc\n", origins))
    expected_uri = "vela-source://sha256/" + hashlib.sha256(source).hexdigest() + "/in%20%231.vela"
    ensure(record["version"] == 3 and record["sources"] == [expected_uri]
           and record["sourcesContent"] == [source.decode()] and record["mappings"] == "A;AAEA,E;A;AADG,G;A",
           f"unexpected standard map coordinate deltas: {record}")
    other = json.loads(maps._source_map("in #1.vela", source + b" ", "", []))
    ensure(other["sources"] != record["sources"], "distinct source snapshots with one basename have the same URI")


def _freshness() -> None:
    with tempfile.TemporaryDirectory() as temporary, patch.object(maps.subprocess, "run") as run:
        path = Path(temporary)
        compiled = Mock(spec=maps.parser.Build)
        files = {maps.GALLINA: b"def\n", maps.MAP: b"{}", maps.MANIFEST: b"{}"}
        for name, body in files.items():
            (path / name).write_bytes(body)
        for name, body in files.items():
            (path / name).write_bytes(body + b" ")
            try:
                maps.read_positions(compiled, path / "source", files, path, path / "reader", [(0, 0)])
            except ValueError as error:
                ensure(str(error) == f"stale or changed source map input: {name}", "wrong refusal")
            else:
                raise AssertionError("stale input reached the source-map reader")
            (path / name).write_bytes(body)
        for positions in ([], [(-1, 0)], [(0, 4)], [(2, 0)], [(0, 0)] * 65):
            try:
                maps.read_positions(compiled, path / "source", files, path, path / "reader", positions)
            except ValueError as error:
                ensure("coordinate" in str(error), "wrong lookup budget or bounds refusal")
            else:
                raise AssertionError("out-of-range lookup reached the source-map reader")
        run.assert_not_called()


def _late_change() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        source = directory / "map.vela"
        data = b"module Map;"
        manifest = {"source_sha256": maps._digest(data), "producer": {"compiler": "first"}}
        files = {maps.GALLINA: b"generated", maps.MAP: b"{}", maps.MANIFEST: json.dumps(manifest).encode()}
        for name, body in files.items():
            (directory / name).write_bytes(body)
        for changed in ("source", "producer"):
            source.write_bytes(data)
            with (patch.object(maps.parser, "cached_build", return_value=nullcontext(Mock())),
                  patch.object(maps, "_compile", return_value=files), patch.object(maps, "_producer") as producer,
                  patch.object(maps, "_file_digest") as digest, patch.object(maps.subprocess, "run") as run):
                producer.return_value = {"compiler": "first"}

                def replace_before_launch(_node: Path, changed: str = changed) -> str:
                    if changed == "source":
                        source.write_bytes(b"module Edited;")
                    else:
                        producer.return_value = {"compiler": "second"}
                    return maps.NODE_SHA256

                digest.side_effect = replace_before_launch
                try:
                    maps.query(directory, source, directory, directory / "reader", 1, 1)
                except ValueError as error:
                    ensure(str(error) == "source map inputs changed before handoff", "wrong live-input refusal")
                else:
                    raise AssertionError("an input changed between map compilation and reader handoff")
                run.assert_not_called()


def cases() -> list[Case]:
    return [Case("source maps compose signed UTF-16 deltas across source line endings", _coordinates),
            Case("source, map and layout handoffs refuse stale bytes and invalid lookup positions", _freshness),
            Case("changes after map compilation invalidate the Node reader handoff", _late_change)]
