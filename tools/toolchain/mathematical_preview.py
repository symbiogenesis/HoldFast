# SPDX-License-Identifier: Apache-2.0
"""Checked, read-only grouping edits for mathematical VELA107 findings."""

import hashlib
import json
import sys
from typing import cast

from toolchain import mathematical, parser
from toolchain.inspection import compiler_dependency_hashes


def _producer(compiled: parser.Build) -> dict[str, str]:
    sources = json.dumps(compiler_dependency_hashes(), sort_keys=True).encode("ascii")
    return {"compiler_sha256": hashlib.sha256(sources).hexdigest(),
            "parser_sha256": hashlib.sha256(compiled.executable.read_bytes()).hexdigest(),
            "ocamlrun_sha256": parser.interpreter_digest(compiled),
            "python": sys.version, "implementation": sys.implementation.name}


def _tree(value: parser.Json, group_operand: tuple[int, int] | None = None) -> parser.Json:
    if isinstance(value, list):
        return [_tree(item, group_operand) for item in value]
    if isinstance(value, dict):
        if group_operand and value.get("kind") == "binary" and value.get("span") == list(group_operand):
            return {"kind": "group", "value": _tree(value)}
        return {key: _tree(item, group_operand) for key, item in value.items() if key != "span"}
    return value


def _gallina(translation: mathematical.Compilation, source: bytes) -> str:
    identity = f"Source SHA256: {hashlib.sha256(source).hexdigest()} *)\n"
    header, separator, body = translation.gallina.partition(identity)
    if not separator:
        raise ValueError("mathematical emission has no matching source identity")
    return header + body


def preview(compiled: parser.Build, source: bytes, line: int, column: int) -> dict[str, object]:
    """Group exactly one compiler-identified operand, preserving its complete checked term."""
    if any(type(i) is not int or i < 1 for i in (line, column)):
        raise ValueError("VELA107 requires positive one-based operator coordinates")
    producer = _producer(compiled)
    original = parser.parse_source(compiled, source, surface=True)
    checked = mathematical.inspect_source(source, original)
    spans = [(start, end) for finding, start, end in checked.precedence_operands
             if (finding.line, finding.column) == (line, column)]
    if len(spans) != 1:
        raise ValueError("select the start of one reported VELA107 bitwise operator")
    start, end = spans[0]
    replacement = b"(" + source[start:end] + b")"
    candidate = source[:start] + replacement + source[end:]
    parsed = parser.parse_source(compiled, candidate, surface=True)
    rechecked = mathematical.inspect_source(candidate, parsed)
    if (_tree(original["ast"], (start, end)) != _tree(parsed["ast"])
            or _gallina(checked, source) != _gallina(rechecked, candidate)):
        raise ValueError("grouping changed the checked mathematical program")
    if _producer(compiled) != producer:
        raise ValueError("mathematical preview producer changed during checking")
    return {"schema": 1, "scope": "mathematical-development", "rule": "VELA107",
            "producer": producer, "source_sha256": hashlib.sha256(source).hexdigest(),
            "line": line, "column": column, "span": [start, end],
            "replacement": replacement.decode("utf-8"), "candidate_sha256": hashlib.sha256(candidate).hexdigest()}


def validate(publication: object, compiled: parser.Build, source: bytes) -> bytes:
    """Recheck a retained edit against current source, compiler and native parser before use."""
    if not isinstance(publication, dict):
        raise TypeError("invalid mathematical preview")
    line, column = publication.get("line"), publication.get("column")
    if type(line) is not int or type(column) is not int:
        raise ValueError("invalid mathematical preview coordinates")
    expected = preview(compiled, source, line, column)
    if json.dumps(expected, sort_keys=True) != json.dumps(publication, sort_keys=True, allow_nan=False):
        raise ValueError("stale or changed mathematical preview")
    start, end = cast("list[int]", expected["span"])
    return source[:start] + cast("str", expected["replacement"]).encode("utf-8") + source[end:]
