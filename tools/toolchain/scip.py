# SPDX-License-Identifier: Apache-2.0
"""Publish and recheck a bounded SCIP projection of a locked mathematical build."""

import json
import re
from bisect import bisect_right
from dataclasses import dataclass, field
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import cast

from toolchain import packages, parser
from toolchain.elaborate_types import CheckedElaboration
from toolchain.hashing import file_sha256
from toolchain.package_navigation import Navigation, Site

SCHEMA = "b38021b65ef90cbbf6af9c829ff75192859ad9b5da05439ef154bea4ceb2bf03"
MAX_INDEX_BYTES = 32 * 1024 * 1024
MAX_OCCURRENCES = 100_000
_DEFINITION = re.compile(rb"^Definition (\w+) (?:\:|\:=)", re.MULTILINE)


def _varint(value: int) -> bytes:
    data = bytearray()
    while value >= 128:
        data.append((value & 127) | 128)
        value >>= 7
    data.append(value)
    return bytes(data)


def _field(number: int, value: str | bytes | int) -> bytes:
    if isinstance(value, int):
        return _varint(number << 3) + _varint(value)
    data = value.encode("utf-8") if isinstance(value, str) else value
    return _varint(number << 3 | 2) + _varint(len(data)) + data


@dataclass
class _Document:
    path: str
    language: str
    source: bytes
    occurrences: set[tuple[int, int, str, int]] = field(default_factory=set)
    symbols: dict[str, bytes] = field(default_factory=dict)

    def declare(self, start: int, end: int, symbol: str, name: str, *, related: str = "",
                relation: int = 0, generated: bool = False) -> None:
        row = _field(1, symbol) + _field(6, name)
        if related:
            row += _field(4, _field(1, related) + _field(relation, 1))
        self.symbols[symbol] = row
        self.occurrences.add((start, end, symbol, 17 if generated else 1))

    def encode(self) -> bytes:
        starts = [0, *(m.end() for m in re.finditer(rb"\r\n|\r|\n", self.source))]
        data = bytearray(_field(1, self.path) + _field(4, self.language) + _field(6, 1))
        for start, end, symbol, roles in sorted(self.occurrences):
            if not 0 <= start < end <= len(self.source):
                raise ValueError("navigation span outside its document")
            first, last = bisect_right(starts, start) - 1, bisect_right(starts, end) - 1
            coords = [first, start - starts[first]]
            if first != last:
                coords.append(last)
            coords.append(end - starts[last])
            value = _field(1, b"".join(_varint(n) for n in coords)) + _field(2, symbol) + _field(3, roles)
            data.extend(_field(2, value))
            if len(data) > MAX_INDEX_BYTES:
                raise ValueError("SCIP index exceeds its byte budget")
        for symbol in sorted(self.symbols):
            data.extend(_field(3, self.symbols[symbol]))
        return bytes(data)


def _complete(module: str, output: CheckedElaboration, nav: Navigation) -> bool:
    """Total authored name-use coverage only for the explicit scalar definition fragment."""
    # Inspect syntax for coverage only. All symbol identities come from the elaborator.
    def supported(value: object) -> bool:
        if isinstance(value, list):
            return all(supported(child) for child in value)
        if not isinstance(value, dict):
            return True
        node = cast("dict[str, object]", value)
        kind = node.get("kind")
        if kind is None:
            return True
        if kind not in {"surface_file", "definition", "parameter", "type", "call", "argument", "name",
                        "expression_body", "nat", "bool", "group", "binary", "unary"}:
            return False
        if kind == "type" and cast("dict[str, object]", node["name"])["text"] not in {"Nat", "bool"}:
            return False
        if kind == "argument" and node.get("label") is not None:
            return False
        if kind == "name" and Site.at(module, cast("dict[str, object]", node["name"])) not in referenced:
            return False
        return all(supported(child) for child in node.values())

    referenced = {use for use, _ in nav.references if use.module == module}
    return supported(json.loads(output.syntax)["ast"])


def _documents(closure: packages.Closure, outputs: dict[str, CheckedElaboration],
               nav: Navigation) -> dict[str, _Document]:
    docs: dict[str, _Document] = {}
    generated: dict[str, _Document] = {}
    prefixes: dict[str, str] = {}
    for name, raw in packages._object(closure.lock["packages"], "packages").items():
        package = packages._object(raw, "package")
        for module, filename in packages._object(package["modules"], "modules").items():
            docs[module] = _Document(f"{name}/{package['revision']}/{filename}", "Vela", closure.sources[module])
            generated[module] = _Document(f"__generated__/{module}.v", "Coq", outputs[module].gallina.encode("utf-8"))
            prefixes[module] = f"vela vela {name} {package['instance']} " + module.replace(".", "/") + "/"

    symbols = {site: (f"local {site.start}" if decl.kind == "parameter" else
                      f"{prefixes[site.module]}{decl.name}({site.start}).")
               for site, decl in nav.declarations.items()}
    emissions: dict[str, dict[str, Site]] = {module: {} for module in docs}
    for site, decl in nav.declarations.items():
        doc = docs[site.module]
        if doc.source[site.start:site.end] != decl.name.encode("ascii"):
            raise ValueError("navigation declaration lost its authored spelling")
        doc.declare(site.start, site.end, symbols[site], decl.name,
                    related=symbols[decl.implements] if decl.implements is not None else "", relation=3)
        if decl.emitted is not None:
            emissions[site.module][decl.emitted] = site
    for use, target in nav.references:
        docs[use.module].occurrences.add((use.start, use.end, symbols[target], 0))
    for site, (target, arguments) in nav.instances.items():
        decl = nav.declarations[target]
        docs[site.module].declare(site.start, site.end, f"{prefixes[site.module]}instantiation({site.start}).",
                                  f"{decl.name}<{', '.join(arguments)}>", related=symbols[target],
                                  relation=2, generated=True)
    for module, generated_doc in generated.items():
        expected = emissions[module].copy()
        for match in _DEFINITION.finditer(generated_doc.source):
            emitted = match[1].decode("ascii")
            if emitted in expected:
                site = expected.pop(emitted)
                generated_doc.declare(*match.span(1), f"{prefixes[module]}Gallina/{emitted}.", emitted,
                                      related=symbols[site], relation=5, generated=True)
        if expected:
            raise ValueError("generated declaration missing from its exact Gallina module")
    return {doc.path: doc for doc in [*docs.values(), *generated.values()]}


def _bundle(root: Path, workspace: Path, lock: Path, destination: Path) -> tuple[dict[str, bytes], packages.Object]:
    exporter_digest = file_sha256(Path(__file__))
    nav = Navigation()
    raw, closure, outputs = packages.checked_modules(root, workspace, lock, navigation=nav)
    docs = _documents(closure, outputs, nav)
    if sum(len(d.occurrences) for d in docs.values()) > MAX_OCCURRENCES:
        raise ValueError("SCIP index exceeds its occurrence budget")
    metadata = _field(2, _field(1, "vela") + _field(2, "1")) + _field(3, destination.as_uri()) + _field(4, 1)
    index = bytearray(_field(1, metadata))
    for path in sorted(docs):
        index.extend(_field(2, docs[path].encode()))
        if len(index) > MAX_INDEX_BYTES:
            raise ValueError("SCIP index exceeds its byte budget")
    files = {path: doc.source for path, doc in docs.items()}
    files["index.scip"] = bytes(index)
    incomplete = sorted(module for module, output in outputs.items() if not _complete(module, output, nav))
    manifest: packages.Object = {"schema": 1, "scip_schema_sha256": SCHEMA, "root": destination.as_uri(),
                                 "exporter_sha256": exporter_digest,
                                 "lock_sha256": packages._sha(raw), "complete": not incomplete,
                                 "incomplete_modules": incomplete,
                                 "scope": "authored scalar definition and value-parameter references",
                                 "files": {name: packages._sha(data) for name, data in files.items()}}
    files["manifest.json"] = packages._encode(manifest) + b"\n"
    return files, manifest


def _current_inputs(root: Path, workspace: Path, lock: Path, manifest: packages.Object) -> None:
    raw, locked, name, revision = packages.read_lock(lock)
    if packages._sha(raw) != manifest["lock_sha256"]:
        raise ValueError("SCIP lock changed during the handoff")
    with parser.cached_build(root) as compiled:
        packages._recheck_parser(root, compiled)
        packages.resolve(workspace, name, revision, packages._producer(root, compiled), locked=locked)
    if file_sha256(Path(__file__)) != manifest["exporter_sha256"]:
        raise ValueError("SCIP exporter changed during the handoff")


def export(root: Path, workspace: Path, lock: Path, destination: Path) -> packages.Object:
    destination = destination.absolute()
    if destination.exists() or destination.resolve() != destination:
        raise ValueError("SCIP output requires a new directory and an unaliased path")
    files, manifest = _bundle(root, workspace, lock, destination)
    with TemporaryDirectory(dir=destination.parent) as temporary:
        staging = Path(temporary) / "bundle"
        staging.mkdir()
        for name, data in files.items():
            path = staging / name
            path.parent.mkdir(exist_ok=True, parents=True)
            path.write_bytes(data)
        _current_inputs(root, workspace, lock, manifest)
        staging.rename(destination)
    return {"status": "indexed", **manifest}


def check(root: Path, workspace: Path, lock: Path, destination: Path, *, require_complete: bool = False) -> packages.Object:
    destination = destination.absolute()
    if destination.resolve() != destination or not destination.is_dir():
        raise ValueError("missing or aliased SCIP bundle")
    files, manifest = _bundle(root, workspace, lock, destination)
    for name, expected in files.items():
        path = destination / name
        if path.resolve() != path:
            raise ValueError(f"aliased SCIP bundle member: {name}")
        if packages._read(path, len(expected)) != expected:
            raise ValueError(f"stale or corrupt SCIP bundle: {name}")
    _current_inputs(root, workspace, lock, manifest)
    if require_complete and not manifest["complete"]:
        raise ValueError("incomplete index: absence of authored references is unverified")
    return {"status": "current", **manifest}
