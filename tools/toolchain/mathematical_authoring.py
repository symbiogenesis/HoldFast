# SPDX-License-Identifier: Apache-2.0
"""Source-preserving authoring checks for the mathematical parser and elaborator."""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import cast

from toolchain import mathematical, parser
from toolchain.ast import MAX_SOURCE_BYTES, HoldFastError, position
from toolchain.authoring import Finding, is_camel_case, is_pascal_case
from toolchain.surface import nodes
from toolchain.syntax_campaigns import strip_spans

type Node = dict[str, parser.Json]


def _start(node: Node) -> int:
    return cast("Sequence[int]", node["span"])[0]


@dataclass(frozen=True)
class Part:
    start: int
    spelling: bytes
    before: int
    comment: bool


def _attached(parts: list[Part], index: int) -> tuple[bytes, ...]:
    comments = []
    while index and parts[index].before == 1:
        index -= 1
        previous = parts[index]
        if not previous.spelling.startswith(b"///") or (index and not previous.before):
            break
        comments.append(previous.spelling)
    return tuple(reversed(comments))


@dataclass
class Document:
    ast: Node
    parts: list[Part]
    checked: mathematical.Compilation
    documentation: dict[int, tuple[bytes, ...]]

    @classmethod
    def read(cls, compiled: parser.Build, source: bytes) -> Document:
        parsed = parser.parse_source(compiled, source, layout=True)
        ranges = cast("Sequence[Sequence[int]]", parsed.pop("layout"))
        checked = mathematical.inspect_source(source, parsed)
        ast = cast("Node", parsed["ast"])
        declarations = {_start(node) for node in nodes(ast) if "modifiers" in node}
        parts: list[Part] = []
        documentation = {}
        cursor = 0
        for start, end in ranges:
            gap = source[cursor:start]
            breaks = gap.count(b"\n") + gap.count(b"\r") - gap.count(b"\r\n")
            value = source[start:end]
            parts.append(Part(start, value, min(breaks, 2), value.startswith((b"//", b"/*"))))
            if start in declarations:
                documentation[start] = _attached(parts, len(parts) - 1)
            cursor = end
        return cls(ast, parts, checked, documentation)

    def render(self) -> bytes:
        roles: dict[int, str] = {}
        after_contract = set()
        for item in nodes(self.ast):
            kind = item["kind"]
            if kind in ("binary", "unary"):
                roles[_start(cast("Node", item["operator"]))] = str(kind)
            elif kind in ("contract", "effects"):
                roles[_start(item)] = "contract"
                after_contract.add(cast("Sequence[int]", item["span"])[1])
        top_level = {_start(item) for item in cast("Sequence[Node]", self.ast["declarations"])}
        sections = set()
        for index, part in enumerate(self.parts):
            if part.start in top_level:
                first = index
                while first and self.parts[first - 1].comment and self.parts[first - 1].before:
                    first -= 1
                sections.add(first)

        result = bytearray()
        depth = 0
        for index, part in enumerate(self.parts):
            value = part.spelling
            if value == b"}":
                depth -= 1
            if index:
                previous = self.parts[index - 1]
                left = previous.spelling
                breaks = int(value in (b"{", b"}", b"else") or left in (b"{", b"}", b";"))
                if value in (b";", b",", b")", b"]"):
                    breaks = 0
                if roles.get(part.start) == "contract" or (value != b";" and previous.start + len(left) in after_contract):
                    breaks = 1
                if part.comment or previous.comment:
                    breaks = part.before
                if index in sections:
                    breaks = 2
                if breaks:
                    indent = depth + int(roles.get(part.start) == "contract")
                    result.extend(b"\n" * breaks + b"    " * indent)
                elif _space(previous, part, roles):
                    result.extend(b" ")
            result.extend(value)
            if len(result) >= MAX_SOURCE_BYTES:
                raise HoldFastError("limit", 1, 1, "formatted mathematical source exceeds the byte budget")
            if value == b"{":
                depth += 1
        result.extend(b"\n")
        return bytes(result)


def _space(left: Part, right: Part, roles: dict[int, str]) -> bool:
    if left.comment or right.comment:
        return True
    before, after = left.spelling, right.spelling
    if after in (b";", b",", b".", b":", b")", b"]", b"?", b"::<") or before in (b".", b"(", b"[", b"::<"):
        return False
    if roles.get(left.start) == "unary":
        return before.isalpha()
    if after in (b"<", b">") and roles.get(right.start) != "binary":
        return False
    if before == b"<" and roles.get(left.start) != "binary":
        return False
    if after == b"(":
        return (roles.get(left.start) == "binary" or before in
                (b"if", b"while", b"match", b"foreach", b"forall", b"exists", b"let", b"in", b"return",
                 b"open", b"assert", b"definition", b"public", b"private", b"internal", b"const",
                 b"=", b"=>", b"->", b",", b":"))
    return after != b"["


def format_checked(compiled: parser.Build, source: bytes) -> tuple[bytes, mathematical.Compilation, mathematical.Compilation]:
    original = Document.read(compiled, source)
    candidate = original.render()
    checked = Document.read(compiled, candidate)
    if ([part.spelling for part in original.parts] != [part.spelling for part in checked.parts]
            or list(original.documentation.values()) != list(checked.documentation.values())
            or strip_spans(original.ast) != strip_spans(checked.ast)):
        raise HoldFastError("format", 1, 1, "formatting changed tokens, comments, documentation or syntax")
    if checked.render() != candidate:
        raise HoldFastError("format", 1, 1, "formatting did not reach a stable layout")
    return candidate, original.checked, checked.checked


def lint_source(compiled: parser.Build, source: bytes) -> tuple[Finding, ...]:
    document = Document.read(compiled, source)
    findings = list(document.checked.findings)
    record_fields = {_start(field) for item in nodes(document.ast) if item["kind"] == "record"
                     for field in cast("Sequence[Node]", item["parameters"])}
    bindings = {"parameter", "let", "var", "constant_local", "binding_pattern", "foreach",
                "foreach_collection", "out_variable"}
    for item in nodes(document.ast):
        name = item.get("name")
        if not isinstance(name, dict) or not isinstance(spelling := name.get("text"), str):
            continue
        modifiers = item.get("modifiers")
        if isinstance(modifiers, list) and "public" in modifiers:
            site = position(source[:_start(name)].decode("utf-8"))
            if not is_pascal_case(spelling):
                findings.append(Finding("HOLDFAST100", f"public member '{spelling}' should use PascalCase",
                                        site.line, site.column))
            if item["kind"] in ("definition", "function", "constant") and not document.documentation[_start(item)]:
                findings.append(Finding("HOLDFAST102", f"public member '{spelling}' should have a /// documentation comment",
                                        site.line, site.column))
        if item["kind"] in bindings and _start(item) not in record_fields and not is_camel_case(spelling):
            site = position(source[:_start(name)].decode("utf-8"))
            findings.append(Finding("HOLDFAST101", f"binding '{spelling}' should use camelCase", site.line, site.column))
    return tuple(sorted(findings, key=lambda finding: (finding.line, finding.column, finding.code)))
