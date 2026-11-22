# SPDX-License-Identifier: Apache-2.0
"""String literal decoding, interpolated template holes, and Format.Write elaboration for Vela."""

from typing import TYPE_CHECKING, cast

from toolchain.ast import (
    VelaError,
    trivia_end,
)
from toolchain.authoring import assist_loan_argument
from toolchain.elaborate_types import (
    _BOOL,
    _CHAR,
    _NAT,
    MAX_STRING_BYTES,
    Node,
    _app,
    _apps,
    _Binding,
    _constant,
    _Term,
    _term,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


class _StringsMixin:
    def _decode_escaped_segment(self: _Elaborator, segment: str, node: Node) -> bytes:
        escapes = {"\\": "\\", '"': '"', "'": "'", "n": "\n", "r": "\r", "t": "\t", "0": "\0"}
        chars: list[str] = []
        index = 0
        while index < len(segment):
            ch = segment[index]
            if ch != "\\":
                chars.append(ch)
                index += 1
                continue
            if index + 1 >= len(segment):
                raise self.fail("syntax", "unterminated escape sequence in string literal", node)
            nxt = segment[index + 1]
            if nxt in escapes:
                chars.append(escapes[nxt])
                index += 2
                continue
            if nxt == "u" and index + 2 < len(segment) and segment[index + 2] == "{":
                end = segment.find("}", index + 3)
                if end == -1:
                    raise self.fail("syntax", "unterminated \\u{...} escape sequence", node)
                hex_digits = segment[index + 3:end]
                if not (1 <= len(hex_digits) <= 6 and all(c in "0123456789abcdefABCDEF" for c in hex_digits)):
                    raise self.fail("syntax", "invalid \\u{...} hex digits", node)
                codepoint = int(hex_digits, 16)
                if codepoint > 0x10FFFF or 0xD800 <= codepoint <= 0xDFFF:
                    raise self.fail("syntax", "Unicode scalar escape is out of range or a surrogate", node)
                chars.append(chr(codepoint))
                index = end + 1
                continue
            raise self.fail("syntax", f"unsupported string escape '\\{nxt}'", node)
        return "".join(chars).encode("utf-8")

    def _decode_char_literal(self: _Elaborator, spelling: str, node: Node) -> int:
        if len(spelling) < 3 or not spelling.startswith("'") or not spelling.endswith("'"):
            raise self.fail("protocol", "character literal lacks single-quote delimiters", node)
        body = spelling[1:-1]
        if "\n" in body or "\r" in body:
            raise self.fail("syntax", "character literal cannot contain a raw newline", node)
        if not body.startswith("\\") and "'" in body:
            raise self.fail("syntax", "unescaped single quote in character literal", node)
        raw_bytes = self._decode_escaped_segment(body, node)
        decoded = raw_bytes.decode("utf-8")
        if len(decoded) != 1:
            raise self.fail("syntax", "character literal must encode exactly one Unicode scalar value", node)
        return ord(decoded[0])

    def _decode_string_literal(self: _Elaborator, spelling: str, node: Node) -> bytes:
        if spelling.startswith('"""'):
            quotes = len(spelling) - len(spelling.lstrip('"'))
            body = spelling[quotes:-quotes]
            if "\n" in body or "\r" in body:
                normalized = body.replace("\r\n", "\n").replace("\r", "\n")
                lines = normalized.split("\n")
                closing_indent = lines[-1]
                dedented: list[str] = []
                for content_line in lines[1:-1]:
                    if content_line == "":
                        dedented.append("")
                    else:
                        if not content_line.startswith(closing_indent):
                            raise self.fail(
                                "syntax",
                                "raw string content line has less indentation than closing delimiter",
                                node,
                            )
                        dedented.append(content_line[len(closing_indent):])
                raw_bytes = "\n".join(dedented).encode("utf-8")
            else:
                raw_bytes = body.encode("utf-8")
        else:
            raw_bytes = self._decode_escaped_segment(spelling[1:-1], node)
        if len(raw_bytes) > MAX_STRING_BYTES:
            raise self.fail("limit", f"string literal exceeds {MAX_STRING_BYTES} UTF-8 bytes", node)
        return raw_bytes

    def _bytes_binding(self: _Elaborator, raw_bytes: bytes) -> _Binding:
        term = _apps(_constant("VNil"), _NAT, _term("unit"))
        for length, byte_val in enumerate(reversed(raw_bytes)):
            term = _apps(
                _constant("VCons"),
                _NAT,
                _term("nat", value=length),
                _term("nat", value=byte_val),
                term,
            )
        return _Binding(term, _apps(_constant("Vec"), _NAT, _term("nat", value=len(raw_bytes))))

    def _check_hole_target_alias(self: _Elaborator, node: Node, target_name: str) -> None:
        if node.get("kind") == "name" and self.name(node["name"]) == target_name:
            raise self.fail("type", f"Format.Write hole cannot alias or read target buffer '{target_name}'", node)
        for value in node.values():
            for child in value if isinstance(value, list) else (value,):
                if isinstance(child, dict) and "kind" in child:
                    self._check_hole_target_alias(child, target_name)

    def _format_write(
        self: _Elaborator, node: Node, arguments: list[Node], environment: dict[str, _Binding]
    ) -> _Binding:
        if len(arguments) != 2:
            raise self.fail("type", 'Format.Write requires (ref builder, $"...") arguments', node)
        labeled = False
        for idx, arg_node in enumerate(arguments):
            self.node(arg_node, "argument")
            label = arg_node["label"]
            if label is None and labeled:
                raise self.fail("name", "positional arguments cannot follow a named argument", arg_node)
            labeled = labeled or label is not None
            if label is not None:
                spelling = self.name(label)
                expected_label = "target" if idx == 0 else "template"
                if spelling != expected_label:
                    raise self.fail(
                        "name", f"expected argument label '{expected_label}', got '{spelling}'", arg_node
                    )
        target_arg = self.node(arguments[0]["value"])
        if (target_arg["kind"] != "unary"
                or not isinstance(target_arg["operator"], dict)
                or target_arg["operator"].get("text") != "ref"):
            hint = ""
            if target_arg["kind"] == "name":
                tname = self.name(target_arg["name"])
                t_err = self.protocol.error("type", "", target_arg)
                assist_loan_argument(self.protocol.source, t_err.line, t_err.column, "ref")
                hint = f"; write 'ref {tname}'"
            raise self.fail(
                "type",
                f"Format.Write requires an explicit ref TextBuilder<capacity> target{hint}",
                arguments[0],
            )
        target_inner = self.node(target_arg["value"])
        target_name = self.name(target_inner["name"]) if target_inner["kind"] == "name" else None
        origin = self.fail("type", "", target_arg)
        origin_message = f"exclusive 'ref' target loan starts at line {origin.line}, column {origin.column}"
        builder = self.expression(target_inner, environment)
        capacity = self.meta(_NAT, environment)
        self.unify(builder.type, _app(_constant("TextBuilder"), capacity))
        capacity = self.whnf(capacity)
        template_arg = self.node(arguments[1]["value"])
        if template_arg["kind"] != "interpolated_string":
            raise self.fail(
                "type",
                'Format.Write requires an interpolated $"..." format template',
                arguments[1],
            )
        spelling = cast("str", template_arg["value"])
        holes = iter(self.nodes(template_arg["holes"]))
        body = spelling[2:-1]
        body_start_byte = cast("list[int]", template_arg["span"])[0] + 2
        literal_chars: list[str] = []
        chunk_terms: list[_Term] = []
        concrete_bytes = 0
        index = 0
        while index < len(body):
            ch = body[index]
            if ch == "{":
                if index + 1 < len(body) and body[index + 1] == "{":
                    literal_chars.append("{")
                    index += 2
                    continue
                if literal_chars:
                    concrete_bytes += len(
                        self._decode_escaped_segment("".join(literal_chars), template_arg)
                    )
                    literal_chars.clear()
                hole_ast = next(holes, None)
                expr_byte_start = body_start_byte + len(body[:index + 1].encode("utf-8"))
                raw = self.protocol.source
                first = trivia_end(raw, expr_byte_start, block_comments=True)
                if hole_ast is None or cast("list[int]", hole_ast["span"])[0] != first:
                    raise self.fail("protocol", "interpolation hole differs from its source", template_arg)
                expr_byte_start, expr_byte_end = cast("list[int]", hole_ast["span"])
                delimiter = trivia_end(raw, expr_byte_end, block_comments=True)
                if raw[delimiter:delimiter + 1] == b":":
                    closing = raw.find(b"}", delimiter + 1, cast("list[int]", template_arg["span"])[1])
                    if closing <= delimiter + 1:
                        raise self.fail("syntax", "invalid interpolation format specifier", template_arg)
                    spec = raw[delimiter + 1:closing].decode("utf-8")
                elif raw[delimiter:delimiter + 1] == b"}":
                    closing = delimiter
                    spec = ""
                else:
                    raise self.fail("protocol", "interpolation expression leaves source tokens uncovered", hole_ast)
                end = len(raw[body_start_byte:closing].decode("utf-8"))
                if target_name is not None:
                    try:
                        self._check_hole_target_alias(hole_ast, target_name)
                    except VelaError as error:
                        repair = ""
                        offset, end_offset = cast("list[int]", node["span"])
                        raw = self.protocol.source
                        snapshot = f"Written({target_name})"
                        written = self.globals.get("Written")
                        if (not chunk_terms and spec in {"x2", "x4", "x8", "X2", "X4", "X8"}
                                and raw[expr_byte_start:expr_byte_end] == snapshot.encode()
                                and written is not None and written.term == _constant("Written")
                                and "Written" not in environment and b"writtenBeforeFormat" not in raw
                                and end_offset - offset <= 100 and b"\n" not in raw[offset:end_offset]
                                and b"\r" not in raw[offset:end_offset]):
                            revised = (
                                raw[offset:expr_byte_start] + b"writtenBeforeFormat" + raw[expr_byte_end:end_offset]
                            ).decode("utf-8")
                            repair = f". Snapshot the count before borrowing: (let writtenBeforeFormat = {snapshot} in {revised})"
                        raise VelaError(
                            error.kind, error.line, error.column, f"{error.message}. {origin_message}{repair}"
                        ) from error
                hole_binding = self.expression(hole_ast, environment)
                saved_count = (
                    hole_ast["kind"] == "name"
                    and self.name(hole_ast["name"]) in environment
                    and self.name(hole_ast["name"]) not in self.local_borrows
                    and self.whnf(hole_binding.type) == _NAT
                )
                if (not saved_count and builder.term.kind == "var"
                        and cast("int", builder.term.value) in self.free(hole_binding.term)):
                    raise self.fail(
                        "type",
                        f"Format.Write hole cannot alias or read target buffer '{target_name or 'target'}'. {origin_message}",
                        hole_ast,
                    )
                hole_type = self.whnf(hole_binding.type)
                head, type_args = self.spine(hole_type)
                hole_int_spec = self._int_spec(hole_type)
                if hole_type == _NAT or hole_int_spec is not None:
                    if spec not in {"", "d", "x", "x2", "x4", "x8", "X", "X2", "X4", "X8", "b"}:
                        raise self.fail(
                            "type", f"unsupported format specifier '{spec}' for Nat hole", template_arg
                        )
                    val = self.whnf(hole_binding.term)
                    if val.kind in {"nat", "int"}:
                        n_val = cast("int", val.value)
                        if spec in {"", "d"}:
                            concrete_bytes += len(str(n_val))
                        elif n_val < 0:
                            raise self.fail(
                                "type",
                                f"format specifier '{spec}' requires a non-negative integer value",
                                template_arg,
                            )
                        elif spec in {"x", "X"}:
                            concrete_bytes += len(format(n_val, "x"))
                        elif spec in {"x2", "X2"}:
                            concrete_bytes += max(2, len(format(n_val, "x")))
                        elif spec in {"x4", "X4"}:
                            concrete_bytes += max(4, len(format(n_val, "x")))
                        elif spec in {"x8", "X8"}:
                            concrete_bytes += max(8, len(format(n_val, "x")))
                        else:
                            concrete_bytes += len(format(n_val, "b"))
                    elif spec.lower() in {"x", "x2", "x4", "x8"} and (hole_int_spec is None or not hole_int_spec.signed):
                        minimum = int(spec[1:] or "1")
                        if hole_int_spec is not None and hole_int_spec.bits <= 4 * minimum:
                            concrete_bytes += minimum
                        else:
                            op = "nat_hex_width" if hole_int_spec is None else f"int_hex_width_{hole_int_spec.name}"
                            chunk_terms.append(_apps(_constant(op), _term("nat", value=minimum), hole_binding.term))
                    else:
                        raise self.fail(
                            "type",
                            "symbolic Nat hole requires a fixed-width hex specifier (x2, x4, x8) or concrete value",
                            template_arg,
                        )
                elif hole_type == _BOOL:
                    if spec != "":
                        raise self.fail(
                            "type", f"unsupported format specifier '{spec}' for bool hole", template_arg
                        )
                    val = self.whnf(hole_binding.term)
                    if val.kind == "bool":
                        concrete_bytes += 4 if val.value else 5
                    else:
                        chunk_terms.append(
                            _term("if", _NAT, hole_binding.term, _term("nat", value=4), _term("nat", value=5))
                        )
                elif hole_type == _CHAR:
                    if spec != "":
                        raise self.fail(
                            "type", f"unsupported format specifier '{spec}' for char hole", template_arg
                        )
                    val = self.whnf(hole_binding.term)
                    if val.kind == "char":
                        cp = cast("int", val.value)
                        concrete_bytes += len(chr(cp).encode("utf-8"))
                    elif self._prove_bool_precondition(
                        _apps(_constant("char_le"), hole_binding.term, _term("char", value=0x7F)), environment
                    ):
                        concrete_bytes += 1
                    else:
                        raise self.fail(
                            "type",
                            "symbolic char hole requires a concrete character value or proved ASCII bound (<= '\\u{7F}')",
                            template_arg,
                        )
                elif head == _constant("Vec") and len(type_args) == 2 and self.whnf(type_args[0]) == _NAT:
                    if spec != "":
                        raise self.fail(
                            "type", f"unsupported format specifier '{spec}' for byte-vector hole", template_arg
                        )
                    len_term = self.whnf(type_args[1])
                    if len_term.kind == "nat":
                        concrete_bytes += cast("int", len_term.value)
                    else:
                        chunk_terms.append(len_term)
                else:
                    raise self.fail(
                        "type",
                        "interpolated hole type does not implement static Format<T>",
                        template_arg,
                    )
                index = end + 1
                continue
            if ch == "}":
                if index + 1 < len(body) and body[index + 1] == "}":
                    literal_chars.append("}")
                    index += 2
                    continue
                raise self.fail("syntax", "unescaped closing '}' in interpolated format template", template_arg)
            literal_chars.append(ch)
            index += 1
        if next(holes, None) is not None:
            raise self.fail("protocol", "unexpected interpolation expression", template_arg)
        if literal_chars:
            concrete_bytes += len(self._decode_escaped_segment("".join(literal_chars), template_arg))
        if concrete_bytes > MAX_STRING_BYTES:
            raise self.fail(
                "limit", f"formatted template exceeds {MAX_STRING_BYTES} UTF-8 bytes", template_arg
            )
        total_chunk = _term("nat", value=concrete_bytes)
        for extra in chunk_terms:
            total_chunk = (
                extra if total_chunk == _term("nat", value=0) else _apps(_constant("+"), total_chunk, extra)
            )
        return _Binding(
            _apps(_constant("FormatStep"), capacity, builder.term, total_chunk),
            _app(_constant("TextBuilder"), capacity),
        )
