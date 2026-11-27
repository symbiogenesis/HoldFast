# SPDX-License-Identifier: Apache-2.0
"""Publish versioned, read-only snapshots of pure compiler facts."""

import json
import sys
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from toolchain import (
    HoldFastError,
    concrete,
    inspection_reader,
    inspection_scopes,
    inspection_syntax,
    inspection_types,
    trace_runtime,
)
from toolchain.hashing import file_sha256, sha256_bytes
from toolchain.lsp_services import (
    Inspection,
    InspectionError,
    inspect_document,
    validate_inspection,
)
from toolchain.source import SourceSnapshot

SCHEMA_VERSION = 7
CONFIGURATION = "pure-default-v1"
TARGET = "gallina-pure-v1"
MAX_QUERY_RESULTS = 256
MAX_EXPORT_BYTES = 1_048_576
SCHEMA_PATH = Path(__file__).with_name("inspection.schema.json")


def _encoded(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode("utf-8")


def _python_sources(directory: Path) -> Iterator[Path]:
    for path in directory.iterdir():
        if path.info.is_dir(follow_symlinks=False):
            yield from _python_sources(path)
        elif path.match("*.py") and path.info.is_file():
            yield path


def compiler_dependency_hashes() -> dict[str, str]:
    """Conservatively bind all local compiler sources and locked tool dependencies."""
    root = Path(__file__).resolve().parents[2]
    toolchain = root / "tools/toolchain"
    paths = sorted(_python_sources(toolchain))
    paths.extend(sorted(path for path in (toolchain / "parser").iterdir() if path.info.is_file()))
    files = (root / "tools/opam/rocq.lock", root / "tools/opam/sail.lock", root / "tools/pyproject.toml",
             root / "tools/uv.lock", SCHEMA_PATH)
    paths.extend(path for path in files if path.is_file())
    return {path.relative_to(root).as_posix(): file_sha256(path) for path in paths}


def producer_identity() -> dict[str, object]:
    images = {"executable": Path(sys.executable)}
    if library := trace_runtime.configured_shared_library():
        images["shared-library"] = library
    producer = {"name": "holdfast-pure-development", "stage": "pure-resolution",
                "dependencies": compiler_dependency_hashes(), "python": sys.version,
                "implementation": sys.implementation.name, "interpreter_sha256": trace_runtime.file_identity(images)}
    return {**producer, "version": sha256_bytes(_encoded(producer))}


def _binding(document: SourceSnapshot, configuration: str, target: str) -> dict[str, object]:
    return {"uri": document.uri, "source_sha256": sha256_bytes(document.source),
            "producer": producer_identity(), "configuration": configuration, "target": target,
            "coordinate_unit": "utf8-byte", "symbol_lifetime": "snapshot"}


def current_binding(source: bytes, *, uri: str = "memory:holdfast", configuration: str = CONFIGURATION,
                    target: str = TARGET) -> dict[str, object]:
    """Identify current inputs without invoking the parser or semantic worker."""
    return _binding(SourceSnapshot(uri, 1, source.decode("utf-8"), 1), configuration, target)


def _span(document: SourceSnapshot, first: tuple[int, int], last: tuple[int, int]) -> list[int]:
    return [document.position_byte_offset(*first), document.position_byte_offset(*last)]


def _facts(document: SourceSnapshot, inspection: Inspection, identity: str) -> tuple[list[object], list[object]]:
    symbols: list[object] = []
    for index, symbol in enumerate(inspection.symbols):
        span = _span(document, symbol.start, symbol.end)
        symbols.append({"id": f"{identity}:symbol:{index}", "name": symbol.name,
                        "kind": symbol.kind, "detail": symbol.detail,
                        "type": symbol.value_type.export(), "span": span,
                        "origin": {"kind": "authored", "span": span},
                        "documentation": symbol.documentation})
    occurrences: list[object] = [
        {"symbol": f"{identity}:symbol:{occurrence.symbol}",
         "span": _span(document, occurrence.start, occurrence.end),
         "declaration": occurrence.declaration}
        for occurrence in inspection.occurrences]
    return symbols, occurrences


@dataclass(frozen=True)
class Snapshot:
    """Immutable publication; identifiers designate facts only in this exact binding."""

    document: SourceSnapshot
    publication: bytes

    def export(self) -> dict[str, object]:
        """Return a detached JSON value; caller mutations cannot change retained facts."""
        return cast("dict[str, object]", json.loads(self.publication))

    def query(self, source: bytes, request: object, *, uri: str | None = None,
              configuration: str = CONFIGURATION, target: str = TARGET) -> dict[str, object]:
        """Answer bounded queries only while the caller's input and producer closure match."""
        current = self.export()
        try:
            document = SourceSnapshot(self.document.uri if uri is None else uri, 1,
                                      source.decode("utf-8"), 1)
            binding = _binding(document, configuration, target)
        except (OSError, ValueError):
            return {
                "schema": SCHEMA_VERSION,
                "scope": "holdfast-pure-inspection-query",
                "snapshot": current["snapshot"],
                "binding": current["binding"],
                "status": "refused",
                "complete": False,
                "reason": "stale-input",
                "items": [],
                "total": 0,
            }
        return inspection_reader.Reader(self.publication).query(source, request, binding=binding)


def inspect(source: bytes, *, uri: str = "memory:holdfast", configuration: str = CONFIGURATION,
            target: str = TARGET) -> Snapshot:
    """Build a complete source-preserving snapshot using the isolated pure fact producer.

    The [inspection contract](../../docs/tooling/tooling-protocols.md#compiler-inspection-api)
    defines this diagnostic view's boundary. Wider syntax and proof views are unavailable.
    """
    document = SourceSnapshot(uri, 1, source.decode("utf-8"), 1)
    binding = _binding(document, configuration, target)
    identity = sha256_bytes(_encoded(binding))
    publication: dict[str, object] = {
        "schema": SCHEMA_VERSION, "scope": "holdfast-pure-inspection",
        "snapshot": identity, "binding": binding, "status": "unavailable", "complete": False,
        "reason": None, "source": document.text, "symbols": [], "occurrences": [], "concrete": [], "syntax": [],
        "expressions": [], "scopes": [],
        "supported_views": ["source-text", "pure-concrete-pieces", "pure-resolved-identifiers", "pure-syntax-tree",
                            "pure-typed-expressions", "pure-lexical-scopes"],
        "unsupported_views": ["imports", "generated-origins", "proof", "lowering"]}
    if configuration != CONFIGURATION or target != TARGET:
        publication.update(status="unsupported", reason="unsupported-configuration-or-target")
    else:
        try:
            raw = dict(inspect_document(source, concrete=True))
            raw_concrete = raw.pop("concrete", None)
            raw_syntax = raw.pop("syntax", None)
            raw_expressions = raw.pop("expressions", None)
            raw_scopes = raw.pop("scopes", None)
            facts = validate_inspection(document, raw)
            if facts is None:
                publication["reason"] = raw["reason"]
            else:
                symbols, occurrences = _facts(document, facts, identity)
                pieces = concrete.validate(source, raw_concrete)
                nodes = inspection_syntax.nodes(source, raw_syntax, identity)
                inspection_syntax.validate_inventory(nodes, symbols, occurrences)
                expressions = inspection_types.expressions(document, raw_expressions, nodes, symbols, occurrences)
                scopes = inspection_scopes.scopes(document, raw_scopes, nodes, symbols, occurrences, identity)
                publication.update(status="checked", complete=True, symbols=symbols,
                                   occurrences=occurrences, concrete=pieces, syntax=nodes, expressions=expressions,
                                   scopes=scopes)
        except InspectionError as error:
            timed_out = "exceeded 5 seconds" in str(error)
            publication.update(status="timed-out" if timed_out else "unavailable",
                               reason="producer-timeout" if timed_out else "producer-failure")
        except HoldFastError as error:
            publication["reason"] = error.kind
        except (ValueError, TypeError, KeyError):
            publication["reason"] = "producer-failure"
    if _binding(document, configuration, target) != binding:
        publication.update(status="refused", complete=False, reason="producer-changed",
                           symbols=[], occurrences=[], concrete=[], syntax=[], expressions=[], scopes=[])
    encoded = _encoded(publication)
    if len(encoded) > MAX_EXPORT_BYTES:
        publication.update(status="unavailable", complete=False, reason="export-limit",
                           symbols=[], occurrences=[], concrete=[], syntax=[], expressions=[], scopes=[])
        encoded = _encoded(publication)
        if len(encoded) > MAX_EXPORT_BYTES:
            raise ValueError("inspection source and provenance exceed export limit")
    return Snapshot(document, encoded)
