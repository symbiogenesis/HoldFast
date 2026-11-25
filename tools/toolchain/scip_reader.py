# SPDX-License-Identifier: Apache-2.0
"""Exercise locked-package navigation offline through the upstream SCIP reader."""

import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import NotRequired, TypedDict, cast

from toolchain import packages, scip
from toolchain.hashing import file_sha256

READER_SHA256 = "2e808bcfc73711f1ab598412ac6ec6f7c68c2c3c07e02f63b05221a2250a357e"
READER_SIZE = 25_384_521
WEIGHTS = "weights/v1/Measure.hf"
SCALE = "scale/v1/Calibration.hf"
GENERATED = "__generated__/Weights.Measure.v"
DEFINITION = 1
GENERATED_DEFINITION = 17


class _Occurrence(TypedDict):
    range: list[int]
    symbol: str
    symbol_roles: NotRequired[int]


class _Symbol(TypedDict):
    symbol: str
    relationships: NotRequired[list[dict[str, object]]]


class _Document(TypedDict):
    relative_path: str
    position_encoding: int
    occurrences: list[_Occurrence]
    symbols: list[_Symbol]


def _stage_reader(reader: Path, directory: Path) -> Path:
    with reader.open("rb") as stream:
        content = stream.read(READER_SIZE + 1)
    if len(content) != READER_SIZE or hashlib.sha256(content).hexdigest() != READER_SHA256:
        raise ValueError("SCIP reader differs from the pinned v0.10.0 Linux ARM64 executable")
    executable = directory / "scip"
    executable.write_bytes(content)
    executable.chmod(0o700)
    return executable


def _read(executable: Path, bundle: Path, expected_paths: set[str]) -> dict[str, _Document]:
    result = subprocess.run(
        [executable, "print", "--json", "index.scip"], cwd=bundle, timeout=15,
        stdin=subprocess.DEVNULL, capture_output=True, check=False,
    )
    if result.returncode or result.stderr or len(result.stdout) > 4 * 1024 * 1024:
        raise ValueError("independent SCIP reader refused the index or exceeded its output bound")
    docs = cast("list[_Document]", json.loads(result.stdout)["documents"])
    by_path = {doc["relative_path"]: doc for doc in docs}
    if len(by_path) != len(docs) or set(by_path) != expected_paths:
        raise ValueError("independent SCIP reader found a different set of documents")
    global_symbols = {info["symbol"] for doc in docs for info in doc["symbols"] if not info["symbol"].startswith("local ")}
    for doc in docs:
        visible = global_symbols | {info["symbol"] for info in doc["symbols"]}
        if any(entry["symbol"] not in visible for entry in doc["occurrences"]):
            raise ValueError(f"unresolved occurrence in {doc['relative_path']}")
        if any(edge["symbol"] not in visible for info in doc["symbols"] for edge in info.get("relationships", [])):
            raise ValueError(f"unresolved relationship in {doc['relative_path']}")
    return by_path


def _site(source: bytes, needle: str, spelling: str) -> list[int]:
    prefix, separator, suffix = needle.partition("|")
    if not separator:
        raise ValueError("missing cursor in SCIP fixture")
    pattern = (prefix + spelling + suffix).encode()
    matches = [(line, data.index(pattern) + len(prefix.encode())) for line, data in
               enumerate(source.splitlines()) if pattern in data]
    if len(matches) != 1:
        raise ValueError(f"SCIP fixture has an ambiguous or missing site {needle!r}")
    line, column = matches[0]
    return [line, column, column + len(spelling.encode())]


def _at(doc: _Document, span: list[int], role: int) -> str:
    found = [entry["symbol"] for entry in doc["occurrences"] if entry["range"] == span
             and entry.get("symbol_roles", 0) & GENERATED_DEFINITION == role]
    if len(found) != 1:
        raise ValueError(f"SCIP reader found {len(found)} matches at {doc['relative_path']} {span}, role {role}")
    return found[0]


def _related(doc: _Document, symbol: str, relation: str) -> set[str]:
    return {str(edge["symbol"]) for info in doc["symbols"] if info["symbol"] == symbol
            for edge in info.get("relationships", []) if edge.get(relation) is True}


def _navigate(documents: dict[str, _Document], workspace: Path, bundle: Path, make: str) -> dict[str, str]:
    client, provider = (workspace / SCALE).read_bytes(), (workspace / WEIGHTS).read_bytes()
    weights, scale, generated = documents[WEIGHTS], documents[SCALE], documents[GENERATED]
    if weights["position_encoding"] != 1 or scale["position_encoding"] != 1:
        raise ValueError("SCIP reader expected UTF-8 source columns")
    make_symbol = _at(weights, _site(provider, "Weight |(Nat", make), DEFINITION)
    make_use = _at(scale, _site(client, "Measure(|(units:", make), 0)
    method = _at(weights, _site(provider, "Nat |(T value)", "Measure"), DEFINITION)
    concrete = _at(weights, _site(provider, "Nat |(Weight value)", "Measure"), DEFINITION)
    method_use = _at(scale, _site(client, "Weight.|(", "Measure"), 0)
    if make_symbol != make_use or method_use != method or method not in _related(weights, concrete, "is_implementation"):
        raise ValueError("offline imported definition, reference or implementation query disagreed")

    global_units = _at(scale, _site(client, "Nat |() => 5", "units"), DEFINITION)
    parameter = _at(scale, _site(client, "Echo(Nat |)", "units"), DEFINITION)
    parameter_use = _at(scale, _site(client, "Identity<Nat>(|)", "units"), 0)
    generic = _at(scale, _site(client, "T |<T>(T", "Identity"), DEFINITION)
    generic_use = _at(scale, _site(client, "=> |<Nat>(", "Identity"), 0)
    application = _at(scale, _site(client, "=> |;", "Identity<Nat>(units)"), GENERATED_DEFINITION)
    if parameter == global_units or parameter != parameter_use or generic != generic_use:
        raise ValueError("offline shadowed-parameter or generic definition query disagreed")
    if generic not in _related(scale, application, "is_reference"):
        raise ValueError("offline specialization does not reference its generic definition")

    # Follow the reverse definition relation and inspect the actual emitted identifier at its range.
    origins = [o for o in generated["occurrences"] if o.get("symbol_roles", 0) & GENERATED_DEFINITION == GENERATED_DEFINITION
               and make_symbol in _related(generated, o["symbol"], "is_definition")]
    if len(origins) != 1:
        raise ValueError("offline generated-to-authored definition query disagreed")
    row, start, end = origins[0]["range"]
    line = (bundle / GENERATED).read_bytes().splitlines()[row]
    name = line[start:end].decode()
    if not line[:start].endswith(b"Definition ") or not name.endswith("_" + make):
        raise ValueError(f"generated SCIP site identifies the wrong Gallina definition: {name}")
    return {"imported_function": make_symbol, "interface_method": method, "implementation": concrete,
            "shadowed_value": global_units, "parameter": parameter, "specialization": application,
            "generic": generic, "generated_function": name}


def _expect_stale(root: Path, workspace: Path, lock: Path, bundle: Path) -> None:
    try:
        scip.check(root, workspace, lock, bundle)
    except (OSError, ValueError):
        return
    raise ValueError("stale SCIP index survived an imported source change")


def _qualify_absence(root: Path, executable: Path, workspace: Path, directory: Path) -> dict[str, int]:
    source = (b"module Weights.Measure;\npublic definition Nat Unused(Nat x) => x;\n"
              b"public definition Nat Used(Nat x) => x;\npublic definition Nat Client() => Used(2);\n")
    (workspace / WEIGHTS).write_bytes(source)
    lock = directory / "scalar.lock"
    bundle = directory / "scalar-index"
    packages.lock_package(root, workspace, "weights", "v1", lock)
    scip.export(root, workspace, lock, bundle)
    scip.check(root, workspace, lock, bundle, require_complete=True)
    doc = _read(executable, bundle, {WEIGHTS, GENERATED})[WEIGHTS]
    counts = {}
    for name in ("Unused", "Used"):
        symbol = _at(doc, _site(source, "Nat |(Nat x)", name), DEFINITION)
        counts[name] = sum(o["symbol"] == symbol and not o.get("symbol_roles", 0) & DEFINITION for o in doc["occurrences"])
    if counts != {"Unused": 0, "Used": 1}:
        raise ValueError(f"offline reference counts disagree in the complete scalar package: {counts}")
    return counts


def qualify(root: Path, reader: Path) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="holdfast-scip-offline-") as temporary:
        directory = Path(temporary)
        executable = _stage_reader(reader, directory)
        workspace = directory / "packages"
        shutil.copytree(root / "examples" / "packages", workspace)
        client = workspace / SCALE
        provider = workspace / WEIGHTS
        client.write_bytes(client.read_bytes() + (
            b"\npublic definition Nat units() => 5;\n"
            b"public definition T Identity<T>(T value) => value;\n"
            b"public definition Nat Echo(Nat units) => Identity<Nat>(units);\n"
        ))
        lock = directory / "packages.lock"
        bundle = directory / "index"
        packages.lock_package(root, workspace, "scale", "v1", lock)
        scip.export(root, workspace, lock, bundle)
        scip.check(root, workspace, lock, bundle)
        paths = {WEIGHTS, SCALE, GENERATED, "__generated__/Scale.Calibration.v"}
        before = _navigate(_read(executable, bundle, paths), workspace, bundle, "Make")
        try:
            scip.check(root, workspace, lock, bundle, require_complete=True)
        except ValueError as error:
            if "incomplete" not in str(error):
                raise
        else:
            raise ValueError("partial SCIP coverage licensed an absence claim")
        previous = provider.read_bytes()
        provider.unlink()
        _expect_stale(root, workspace, lock, bundle)
        provider.write_bytes(previous.replace(b" Make(", b" Create("))
        client.write_bytes(client.read_bytes().replace(b"(Make(", b"(Create("))
        _expect_stale(root, workspace, lock, bundle)
        packages.lock_package(root, workspace, "scale", "v1", lock)
        _expect_stale(root, workspace, lock, bundle)
        renamed = directory / "renamed"
        scip.export(root, workspace, lock, renamed)
        scip.check(root, workspace, lock, renamed)
        documents = _read(executable, renamed, paths)
        after = _navigate(documents, workspace, renamed, "Create")
        if any(entry["symbol"] == before["imported_function"]
               for doc in documents.values() for entry in doc["occurrences"]):
            raise ValueError("renamed index still contains an occurrence of the old dependency")
        counts = _qualify_absence(root, executable, workspace, directory)
        return {"status": "qualified", "reader_sha256": READER_SHA256, "before": before, "after": after,
                "complete_package_references": counts,
                "indices_sha256": [file_sha256(item / "index.scip")
                                   for item in (bundle, renamed)],
                "refusals": ["incomplete-absence", "deleted-dependency", "renamed-dependency", "replaced-lock"]}
