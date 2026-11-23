# SPDX-License-Identifier: Apache-2.0
"""Native syntax adapter for bounded mathematical compilation and observation."""

from dataclasses import dataclass
from pathlib import Path
from typing import cast

from toolchain import (
    StaticEvaluation,
    ValueType,
)
from toolchain import (
    elaborate as holdfast_elaborate,
)
from toolchain import (
    parser as holdfast_parser,
)
from toolchain.ast import Name, position
from toolchain.authoring import Finding, generic_type_findings
from toolchain.elaborate import Elaboration
from toolchain.hashing import file_sha256
from toolchain.surface import nodes

_BUILD_CACHE: tuple[tuple[Path, int, int, int], holdfast_parser.Build] | None = None
_COMPARISON = frozenset({"==", "!=", "<", "<=", ">", ">="})
_BITWISE = frozenset({"&", "^", "|"})


def _build(parser: Path) -> holdfast_parser.Build:
    global _BUILD_CACHE  # noqa: PLW0603
    stat = parser.stat()
    key = (parser, stat.st_mtime_ns, stat.st_size, stat.st_ino)
    if _BUILD_CACHE is not None and _BUILD_CACHE[0] == key:
        return _BUILD_CACHE[1]
    digest = file_sha256(parser)
    built = holdfast_parser.Build(parser.parent, parser, {"generated_sha256": {"holdfast-parser": digest}})
    _BUILD_CACHE = (key, built)
    return built


@dataclass(frozen=True)
class Compilation(Elaboration):
    findings: tuple[Finding, ...] = ()
    precedence_operands: tuple[tuple[Finding, int, int], ...] = ()


def inspect_source(source: bytes, parsed: object) -> Compilation:
    """Inspect accepted syntax after complete exact-source semantic checking."""
    translation = holdfast_elaborate.elaborate(source, parsed)
    ast = cast("holdfast_parser.Json", cast("dict[str, object]", parsed)["ast"])
    names: list[tuple[int, Name]] = []
    operands: list[tuple[Finding, int, int]] = []
    for item in nodes(ast):
        if item.get("kind") == "generic_parameter" and item.get("mode") == "type":
            identifier = cast("dict[str, holdfast_parser.Json]", item["name"])
            offset = cast("int", cast("list[holdfast_parser.Json]", identifier["span"])[0])
            names.append((offset, Name(cast("str", identifier["text"]),
                                       position(source[:offset].decode("utf-8")))))
        if item.get("kind") == "binary" and _operator(item) in _COMPARISON:
            for side in ("left", "right"):
                operand = item.get(side)
                if isinstance(operand, dict) and operand.get("kind") == "binary" and _operator(operand) in _BITWISE:
                    byte_span = cast("list[holdfast_parser.Json]", operand["span"])
                    start, end = cast("int", byte_span[0]), cast("int", byte_span[1])
                    operator = cast("dict[str, holdfast_parser.Json]", operand["operator"])
                    offset = cast("int", cast("list[holdfast_parser.Json]", operator["span"])[0])
                    site = position(source[:offset].decode("utf-8"))
                    expression = source[start:end].decode("utf-8")
                    message = "parenthesize this bitwise operand to make comparison precedence explicit"
                    if len(expression) <= 60 and "\n" not in expression and "\r" not in expression:
                        message += f": ({expression})"
                    operands.append((Finding("HOLDFAST107", message, site.line, site.column), start, end))
    findings = [finding for finding, _, _ in operands]
    for offset, spelling in translation.constructor_suggestions.items():
        site = position(source[:offset].decode("utf-8"))
        findings.append(Finding("HOLDFAST108", f"this pattern binds every value. Use '{spelling}' to match the constructor",
                                site.line, site.column))
    names.sort(key=lambda item: item[0])
    findings.extend(generic_type_findings(tuple(name for _, name in names)))
    findings.sort(key=lambda item: (item.line, item.column, item.code))
    return Compilation(translation.module, translation.gallina, tuple(findings), tuple(operands))


def _operator(node: dict[str, holdfast_parser.Json]) -> str:
    operator = cast("dict[str, holdfast_parser.Json]", node["operator"])
    return cast("str", operator["text"])


def compile_source(source: bytes, parser: Path) -> Compilation:
    """Parse and elaborate HoldFast source with the given native parser binary."""
    parsed = holdfast_parser.parse_source(_build(parser), source, surface=True)
    return inspect_source(source, parsed)


def evaluate_source(source: bytes, expression: str, value_type: ValueType,
                    parser: Path) -> StaticEvaluation:
    """Check the entire module before parsing and reducing one console initializer."""
    compiled = _build(parser)
    parsed = holdfast_parser.parse_source(compiled, source, surface=True)
    return holdfast_elaborate.evaluate(
        source, parsed, expression, value_type,
        parse=lambda probe: holdfast_parser.parse_source(compiled, probe, surface=True))
