# SPDX-License-Identifier: Apache-2.0
"""ECMA-426 export and independent lookup for generated mathematical Gallina."""

import json
import subprocess
import sys
import tempfile
from dataclasses import asdict
from pathlib import Path
from typing import cast
from urllib.parse import quote

from toolchain import elaborate, parser
from toolchain.elaborate_types import GallinaOrigin
from toolchain.hashing import file_sha256 as _file_digest
from toolchain.hashing import sha256_bytes
from toolchain.inspection import compiler_dependency_hashes

GALLINA = "module.v"
MAP = "module.v.map"
MANIFEST = "manifest.json"
NODE_VERSION = "v22.22.1"
NODE_SHA256 = "1ea16f5e8d590ca819f1db81e61a6bc4c8e7d8b69776c9236f8ebbf717113225"
_DIGITS = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
_QUERY = """
const { SourceMap } = require('node:module');
const { map, positions } = JSON.parse(require('node:fs').readFileSync(0, 'utf8'));
const reader = new SourceMap(map);
const sites = positions.map(([line, column]) => {
  const entry = reader.findEntry(line, column);
  return entry.originalSource === undefined ? null :
    [entry.originalSource, entry.originalLine, entry.originalColumn];
});
process.stdout.write(JSON.stringify({ version: process.version, sites }));
"""


def _encode(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n").encode("ascii")


def _vlq(delta: int) -> str:
    value = 2 * abs(delta) + (delta < 0)
    digits = ""
    while value >= 32:
        digits += _DIGITS[32 + value % 32]
        value //= 32
    return digits + _DIGITS[value]


def _coordinates(source: bytes, offsets: set[int]) -> dict[int, tuple[int, int]]:
    line, column, previous = 0, 0, 0
    positions = {}
    for offset in sorted(offsets):
        segment = source[previous:offset].decode().replace("\r\n", "\n").replace("\r", "\n")
        line += segment.count("\n")
        trailing = segment.rsplit("\n", 1)[-1]
        column = (0 if "\n" in segment else column) + len(trailing.encode("utf-16-le")) // 2
        positions[offset] = (line, column)
        previous = offset
    return positions


def _source_map(name: str, source: bytes, gallina: str, origins: list[GallinaOrigin]) -> bytes:
    lines = gallina.split("\n")
    # A generated-only segment also prevents readers carrying the last matching
    # entry across an empty line or into the synthesized prelude or footer.
    mappings = ["A"] * len(lines)
    positions = _coordinates(source, {origin.source[0] for origin in origins})
    previous_line, previous_column = 0, 0
    for origin in origins:
        line, column = positions[origin.source[0]]
        for i in range(origin.first_line, origin.first_line + origin.line_count):
            content = lines[i]
            if content:
                end = len(content.encode("utf-16-le")) // 2
                mappings[i] = "AA" + _vlq(line - previous_line) + _vlq(column - previous_column) + "," + _vlq(end)
                previous_line, previous_column = line, column
    embedded_uri = f"holdfast-source://sha256/{sha256_bytes(source)}/{quote(name, safe='')}"
    return _encode({"version": 3, "file": GALLINA, "sources": [embedded_uri], "names": [],
                    "sourcesContent": [source.decode()], "mappings": ";".join(mappings)})


def _producer(compiled: parser.Build) -> dict[str, str]:
    return {"compiler_sha256": sha256_bytes(_encode(compiler_dependency_hashes())),
            "python": sys.version, "python_sha256": _file_digest(Path(sys.executable)),
            "parser_sha256": _file_digest(compiled.executable), "ocamlrun_sha256": parser.interpreter_digest(compiled)}


def _compile(compiled: parser.Build, path: Path) -> dict[str, bytes]:
    source = parser.read_source(path)
    producer = _producer(compiled)
    parsed = parser.parse_source(compiled, source, surface=True)
    origins: list[GallinaOrigin] = []
    result, _ = elaborate._checked_elaboration(source, parsed, require_word_proofs=True, origins=origins)
    gallina = result.gallina.encode()
    source_map = _source_map(path.name, source, result.gallina, origins)
    manifest = _encode({"schema": 1, "target": "rocq-gallina", "edition": "ECMA-426:2024",
                        "options": {"require_word_proofs": True}, "producer": producer,
                        "source": path.name, "source_sha256": sha256_bytes(source), "gallina_sha256": sha256_bytes(gallina),
                        "map_sha256": sha256_bytes(source_map), "origins": [asdict(origin) for origin in origins]})
    if producer != _producer(compiled) or source != parser.read_source(path):
        raise ValueError("inputs changed during source map generation")
    return {GALLINA: gallina, MAP: source_map, MANIFEST: manifest}


def export(root: Path, source: Path, destination: Path) -> dict[str, str]:
    with parser.cached_build(root) as compiled, tempfile.TemporaryDirectory(dir=destination.parent) as temporary:
        files = _compile(compiled, source)
        pending = Path(temporary) / "map"
        pending.mkdir()
        for name, data in files.items():
            (pending / name).write_bytes(data)
        if destination.exists() or destination.is_symlink():
            raise ValueError("source map export requires a new directory")
        _current(files, compiled, source)
        pending.rename(destination)
    return {"status": "mapped", "directory": str(destination), "manifest_sha256": sha256_bytes(files[MANIFEST])}


def _current(files: dict[str, bytes], compiled: parser.Build, source: Path) -> None:
    manifest = json.loads(files[MANIFEST])
    if _producer(compiled) != manifest["producer"] or sha256_bytes(parser.read_source(source)) != manifest["source_sha256"]:
        raise ValueError("source map inputs changed before handoff")


def _verified(files: dict[str, bytes], directory: Path) -> None:
    for name, expected in files.items():
        path = directory / name
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"missing or invalid source map input: {name}")
        with path.open("rb") as stream:
            if stream.read(len(expected) + 1) != expected:
                raise ValueError(f"stale or changed source map input: {name}")


def read_positions(compiled: parser.Build, source: Path, files: dict[str, bytes], directory: Path, node: Path,
                   positions: list[tuple[int, int]]) -> list[list[str | int] | None]:
    _verified(files, directory)
    lines = files[GALLINA].decode().split("\n")
    if not 1 <= len(positions) <= 64 or any(
        not 0 <= line < len(lines) or not 0 <= column <= len(lines[line].encode("utf-16-le")) // 2
        for line, column in positions
    ):
        raise ValueError("generated UTF-16 coordinate outside Gallina output")
    if _file_digest(node) != NODE_SHA256:
        raise ValueError("source map reader differs from the pinned Node.js executable")
    packet = _encode({"map": json.loads(files[MAP]), "positions": positions})
    _verified(files, directory)
    _current(files, compiled, source)
    run = subprocess.run([str(node.resolve()), "-e", _QUERY], input=packet, capture_output=True, timeout=20,
                         env={}, check=False)
    if run.returncode:
        raise ValueError("pinned source map reader failed")
    result = json.loads(run.stdout)
    if not isinstance(result, dict) or result.get("version") != NODE_VERSION or _file_digest(node) != NODE_SHA256:
        raise ValueError("source map reader identity changed")
    sites = result.get("sites")
    if (not isinstance(sites, list) or len(sites) != len(positions)
            or any(site is not None and (
                not isinstance(site, list) or len(site) != 3 or not isinstance(site[0], str)
                or type(site[1]) is not int or type(site[2]) is not int or min(site[1:]) < 0) for site in sites)):
        raise ValueError("source map reader returned invalid coordinates")
    return cast("list[list[str | int] | None]", sites)


def query(root: Path, path: Path, directory: Path, node: Path, line: int, column: int) -> dict[str, object]:
    with parser.cached_build(root) as compiled:
        files = _compile(compiled, path)
        site, = read_positions(compiled, path, files, directory, node, [(line - 1, column - 1)])
        _verified(files, directory)
        manifest = json.loads(files[MANIFEST])
        _current(files, compiled, path)
    if site is None:
        return {"status": "unmapped"}
    origin = next(row for row in manifest["origins"] if row["first_line"] <= line - 1 < row["first_line"] + row["line_count"])
    return {"status": "mapped", "source": path.resolve().as_uri(), "embedded_source": site[0],
            "line": int(site[1]) + 1, "column": int(site[2]) + 1,
            "origin": origin}
