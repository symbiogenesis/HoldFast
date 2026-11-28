# SPDX-License-Identifier: Apache-2.0
"""Source-preserving authoring checks for the mathematical parser and elaborator."""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import cast

from toolchain import mathematical, parser
from toolchain.ast import MAX_SOURCE_BYTES, HoldFastError, position
from toolchain.authoring import Finding, is_camel_case, is_pascal_case
from toolchain.elaborate import elaborate
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
    parsed: Node
    documentation: dict[int, tuple[bytes, ...]]

    @classmethod
    def read(cls, compiled: parser.Build, source: bytes) -> Document:
        parsed = parser.parse_source(compiled, source, layout=True)
        ranges = cast("Sequence[Sequence[int]]", parsed.pop("layout"))
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
        return cls(ast, parts, parsed, documentation)

    def render(self) -> bytes:
        roles: dict[int, str] = {}
        after_contract = set()
        for item in nodes(self.ast):
            kind = item["kind"]
            if kind in ("binary", "unary"):
                roles[_start(cast("Node", item["operator"]))] = str(kind)
            elif kind in ("contract", "effects", "type_constraint"):
                roles[_start(item)] = "contract"
                after_contract.add(cast("Sequence[int]", item["span"])[1])
                if kind == "type_constraint":
                    roles[_start(cast("Node", item["parameter"]))] = "constraint_parameter"
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
    if before == b"?" and after in (b"?", b"."):
        return True
    if after == b":" and roles.get(left.start) == "constraint_parameter":
        return True
    if after in (b";", b",", b".", b":", b")", b"]", b"?") or before in (b".", b"(", b"["):
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
                 b"open", b"using", b"effects", b"assert", b"definition", b"public", b"private", b"internal", b"const",
                 b"=", b"=>", b"->", b"|>", b",", b":"))
    return after != b"["


def format_document(compiled: parser.Build, original: Document) -> tuple[bytes, Document]:
    candidate = original.render()
    checked = Document.read(compiled, candidate)
    if ([part.spelling for part in original.parts] != [part.spelling for part in checked.parts]
            or list(original.documentation.values()) != list(checked.documentation.values())
            or strip_spans(original.ast) != strip_spans(checked.ast)):
        raise HoldFastError("format", 1, 1, "formatting changed tokens, comments, documentation or syntax")
    if checked.render() != candidate:
        raise HoldFastError("format", 1, 1, "formatting did not reach a stable layout")
    return candidate, checked


def format_syntax(compiled: parser.Build, source: bytes) -> bytes:
    return format_document(compiled, Document.read(compiled, source))[0]


def format_checked(compiled: parser.Build, source: bytes) -> tuple[bytes, mathematical.Compilation, mathematical.Compilation]:
    original = Document.read(compiled, source)
    checked_original = mathematical.inspect_source(source, original.parsed)
    candidate, formatted = format_document(compiled, original)
    return candidate, checked_original, mathematical.inspect_source(candidate, formatted.parsed)


def lint_source(compiled: parser.Build, source: bytes) -> tuple[Finding, ...]:
    document = Document.read(compiled, source)
    return lint_document(source, document, mathematical.inspect_source(source, document.parsed).findings)


def lint_document(source: bytes, document: Document, checked: tuple[Finding, ...]) -> tuple[Finding, ...]:
    findings = list(checked)
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


def annotation_findings(compiled: parser.Build, source: bytes) -> tuple[Finding, ...]:
    """Check omission against the exact source and its resolved compiler output."""
    document = Document.read(compiled, source)
    original = elaborate(source, document.parsed)
    local_kinds = {"let", "var", "typed_local"}
    candidates: list[tuple[int, int, str]] = []
    for item in nodes(document.ast):
        kind = item["kind"]
        if kind in local_kinds and isinstance(annotation := item.get("type"), dict):
            first, last = cast("Sequence[int]", annotation["span"])
            candidates.append((first, last, "local type annotation"))
        elif kind == "generic_application":
            _, end_name = cast("Sequence[int]", cast("Node", item["value"])["span"])
            _, end_application = cast("Sequence[int]", item["span"])
            first = end_name
            while source[first:first + 1].isspace() and first < end_application:
                first += 1
            candidates.append((first, end_application, "explicit generic arguments"))
    findings: list[Finding] = []
    for first, last, description in candidates:
        if any(part.comment and first <= part.start < last for part in document.parts):
            continue
        candidate = source[:first] + source[last:]
        try:
            checked = elaborate(candidate, parser.parse_source(compiled, candidate, surface=True))
        except HoldFastError:
            continue
        if checked.gallina.split("\n", 2)[2] != original.gallina.split("\n", 2)[2]:
            continue
        delta = last - first

        def relocate(offset: int, cut: int = first, shift: int = delta) -> int:
            return offset if offset < cut else offset - shift

        literal_types = {relocate(offset): value for offset, value in original.contextual_literal_types.items()
                         if not first <= offset < last}
        operations = {relocate(offset): value for offset, value in original.integer_operations.items()
                      if not first <= offset < last}
        calls = {relocate(offset): relocate(target) for offset, target in original.call_declarations.items()
                 if not first <= offset < last}
        if (literal_types == checked.contextual_literal_types and operations == checked.integer_operations
                and calls == checked.call_declarations):
            site = position(source[:first].decode("utf-8"))
            findings.append(Finding("HOLDFAST133", f"{description} can be inferred with the same elaboration",
                                    site.line, site.column))
    return tuple(sorted(findings, key=lambda finding: (finding.line, finding.column)))
