# SPDX-License-Identifier: Apache-2.0
"""Exact-source schema-2 AST protocol validation for HoldFast elaboration."""

import hashlib
import re
from collections.abc import Iterator
from itertools import accumulate
from typing import cast

from toolchain.ast import (
    DECIMAL,
    MAX_LITERAL_DIGITS,
    MAX_SOURCE_BYTES,
    HoldFastError,
    position,
    source_text,
    trivia_end,
)
from toolchain.elaborate_holes import MAX_HOLES
from toolchain.elaborate_types import MAX_DEPTH, Node


def syntax_nodes(node: Node) -> Iterator[Node]:
    """Walk located AST roles after protocol validation."""
    pending = [node]
    while pending:
        current = pending.pop()
        yield current
        for value in current.values():
            children = value if isinstance(value, list) else [value]
            pending.extend(child for child in children if isinstance(child, dict) and "kind" in child)


_FIELDS: dict[str, set[str]] = {
    "surface_file": {"name", "declarations"},
    "import": {"name"}, "import_item": {"name", "alias"},
    "alias": {"name", "generics", "contracts", "type", "modifiers"},
    "constant": {"name", "type", "value", "modifiers"},
    "constant_local": {"name", "type", "value"},
    "definition": {"name", "result", "generics", "parameters", "contracts", "value", "modifiers"},
    "function": {"name", "result", "generics", "parameters", "contracts", "body", "cancel", "modifiers"},
    "interface": {"name", "generics", "contracts", "declarations", "modifiers"},
    "impl": {"type", "generics", "contracts", "declarations", "modifiers"},
    "associated_type": {"name", "generics", "kind_annotation", "contracts", "definition", "modifiers"},
    "record": {"name", "generics", "parameters", "contracts", "declarations", "modifiers"},
    "union": {"name", "generics", "contracts", "constructors", "modifiers"},
    "constructor": {"name", "parameters", "result", "contracts"},
    "property": {"name", "type", "contracts", "value", "modifiers"},
    "theorem": {"name", "generics", "parameters", "contracts", "body", "modifiers"},
    "lemma": {"name", "generics", "parameters", "contracts", "body", "modifiers"},
    "generic_parameter": {"name", "mode", "type"},
    "parameter": {"name", "type", "grade"},
    "lambda_parameter": {"name", "type", "grade"},
    "type": {"name", "arguments"},
    "function_type": {"mode", "generics", "parameters", "result", "captures", "effects", "contracts"},
    "group_type": {"type"}, "computed_type": {"value"}, "type_argument": {"type"},
    "tuple_type": {"types"}, "modified_type": {"modifier", "lifetime", "type"},
    "name": {"name"}, "nat": {"value", "suffix"}, "bool": {"value"},
    "character": {"value"}, "string": {"value"}, "interpolated_string": {"value", "holes"},
    "member": {"value", "name"}, "index": {"value", "index"},
    "unit": set(), "tuple": {"values"}, "group": {"value"},
    "call": {"callee", "arguments"}, "generic_application": {"value", "arguments"},
    "argument": {"label", "value"}, "out_variable": {"name"},
    "binary": {"operator", "left", "right"}, "unary": {"operator", "value"},
    "is": {"value", "pattern"},
    "with_expression": {"value", "updates"}, "field_update": {"name", "value"},
    "operator": {"name"}, "type_expression": {"type"},
    "lambda": {"parameters", "body"}, "typed_lambda": {"signature", "body"},
    "let_expression": {"binding", "body"},
    "if_expression": {"condition", "then", "else"},
    "block": {"statements"}, "return": {"value"}, "expression_body": {"value"},
    "let": {"name", "type", "grade", "value"},
    "var": {"name", "type", "grade", "value"},
    "typed_local": {"name", "type", "grade", "value"},
    "let_pattern": {"pattern", "value"},
    "var_pattern": {"pattern", "value"},
    "let_else": {"pattern", "value", "else"},
    "var_else": {"pattern", "value", "else"},
    "assignment": {"target", "operator", "value"},
    "expression_statement": {"value"},
    "range": {"start", "end"},
    "foreach": {"name", "range", "contracts", "body"},
    "foreach_collection": {"name", "type", "mode", "collection", "contracts", "body"},
    "while": {"condition", "contracts", "body"},
    "break": set(), "continue": set(),
    "open_invariant": {"resources", "lifts", "body"},
    "if": {"condition", "then", "else"},
    "match": {"value", "motive", "cases"}, "case": {"pattern", "statements"},
    "match_expression": {"value", "motive", "cases"},
    "expression_case": {"pattern", "value"}, "match_motive": {"name", "type"},
    "wildcard_pattern": set(), "binding_pattern": {"name"},
    "unit_pattern": set(), "group_pattern": {"pattern"},
    "tuple_pattern": {"patterns"}, "bool_pattern": {"value"},
    "character_pattern": {"value"}, "string_pattern": {"value"},
    "nat_pattern": {"value", "suffix"}, "constructor_pattern": {"name", "arguments"},
    "labeled_pattern": {"label", "pattern"},
    "quantifier": {"quantifier", "parameters", "value"},
    "contract": {"role", "value"},
    "type_constraint": {"parameter", "bounds"},
    "effects": {"values"},
    "lifetime": {"name"},
    "propagate": {"value"},
    "assert": {"value", "by"}, "proof": {"body"}, "calc": {"body"},
    "hole": {"name"},
}
_OPTIONAL_FIELDS = {
    "parameter": {"const", "label"},
    "lambda_parameter": {"const"},
    "contract": {"name"},
    "import": {"modifiers", "alias", "items"},
    "binding_pattern": {"grade"},
    "match_motive": {"grade"},
    "foreach": {"grade"},
    "foreach_collection": {"grade"},
}

# Bytes are literal source tokens; strings are fields containing located children.
_FIXED_ENVELOPES: dict[str, tuple[bytes | str, ...]] = {
    "expression_statement": ("value", b";"),
    "range": ("start", b"..", "end"),
    "break": (b"break", b";"),
    "continue": (b"continue", b";"),
    "name": ("name",),
    "hole": ("name",),
    "out_variable": (b"out", b"var", "name"),
    "unary": ("operator", "value"),
    "field_update": ("name", b"=", "value"),
    "member": ("value", b".", "name"),
    "index": ("value", b"[", "index", b"]"),
    "typed_lambda": ("signature", b"=>", "body"),
    "type_expression": (b"type", "type"),
    "type_argument": (b"type", "type"),
    "computed_type": (b"type", b"[", "value", b"]"),
    "propagate": ("value", b"?"),
}

_PATTERN_KINDS = {
    "wildcard_pattern", "binding_pattern", "unit_pattern", "group_pattern",
    "tuple_pattern", "bool_pattern", "character_pattern", "string_pattern",
    "nat_pattern", "constructor_pattern",
}
_PATTERN_ARGUMENT_KINDS = _PATTERN_KINDS | {"labeled_pattern"}
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
_HEX_LITERAL = re.compile(r"0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*")
_BIN_LITERAL = re.compile(r"0[bB][01](?:_?[01])*")
_INT_SUFFIXES = {"", "u8", "u16", "u32", "u64", "usize", "i8", "i16", "i32", "i64", "byte"}
_OPERATORS = {
    "+", "*", "-", "/", "%", "&", "|", "^", "~",
    "==", "!=", "<", "<=", ">", ">=", "&&", "||", "!", "==>", "<==>",
}
_ASSIGN_OPERATORS = {"=", "+=", "-=", "*=", "/=", "%="}
# Match the [generic follower](../../docs/language/surface-grammar.md#bindings-match-arms-and-generic-calls)
# without accepting prefixes of longer lexer tokens.
_GENERIC_APPLICATION_FOLLOW = re.compile(
    rb"""
    [()\[\]};,^] | \|\|? | &&? | \.(?!\.) | :(?!:<) | \?(?![?.A-Za-z_])
  | ==(?!>) | != | <=(?!=>) | >= | => | <(?!=)
  | (?:is|as)(?![A-Za-z_0-9])
    """,
    re.VERBOSE,
)
_SYNTAX_WORDS = {
    "function_type": ("mode", {"Fn", "FnMut", "FnOnce"}),
    "generic_parameter": ("mode", {"type", "ghost", "region", "effect", "captures", "grade"}),
    "quantifier": ("quantifier", {"forall", "exists"}),
    "contract": ("role", {"requires", "ensures", "restores", "decreases", "progress", "invariant"}),
    "modified_type": ("modifier", {"owned", "in", "ref", "out", "ghost", "tracked", "scoped", "shared_ref"}),
    "foreach_collection": ("mode", {"value", "in", "ref"}),
}


class _Protocol:
    def __init__(self, source: bytes) -> None:
        text = source_text(source)
        self.source = source
        self.remaining = MAX_SOURCE_BYTES
        self.holes: dict[int, Node] = {}
        self.boundaries = set(accumulate((len(char.encode("utf-8")) for char in text), initial=0))

    def error(self, kind: str, message: str, node: Node | None = None) -> HoldFastError:
        offset = 0 if node is None else cast("list[int]", node.get("span", [0]))[0]
        site = position(self.source[:offset].decode("utf-8"))
        return HoldFastError(kind, site.line, site.column, message)

    def _span(self, raw: object, parent: tuple[int, int]) -> tuple[int, int]:
        if (not isinstance(raw, list) or len(raw) != 2
                or type(raw[0]) is not int or type(raw[1]) is not int):
            raise self.error("protocol", "syntax span must contain two integer offsets")
        start, end = cast("tuple[int, int]", tuple(raw))
        if (not parent[0] <= start < end <= parent[1]
                or start not in self.boundaries or end not in self.boundaries):
            raise self.error("protocol", "syntax span is empty, escaping or splits UTF-8")
        return start, end

    def _compact_name(self, raw: bytes) -> str:
        """Remove only lexer trivia; qualified names can contain nested comments."""
        value = raw.decode("utf-8")
        result: list[str] = []
        offset = 0
        while offset < len(value):
            if value[offset].isspace():
                offset += 1
            elif value.startswith("//", offset):
                found = re.search(r"[\r\n]", value[offset + 2:])
                offset = len(value) if found is None else offset + 2 + found.start()
            elif value.startswith("/*", offset):
                level = 1
                offset += 2
                while level and offset < len(value):
                    if value.startswith("/*", offset):
                        level += 1
                        offset += 2
                    elif value.startswith("*/", offset):
                        level -= 1
                        offset += 2
                    else:
                        offset += 1
                if level:
                    raise self.error("protocol", "unterminated trivia in syntax name")
            else:
                token = re.match(
                    r"\?[A-Za-z_][A-Za-z_0-9]*|'[A-Za-z_][A-Za-z_0-9]*|[A-Za-z_][A-Za-z_0-9]*|<==>|==>|&&|\|\||==|!=|<=|>=|\+=|-=|\*=|/=|%=|[.+*\-/%<>!&|^~=]",
                    value[offset:],
                )
                if token is None:
                    return "\x00"
                result.append(token.group())
                offset += len(token.group())
        if len(result) == 1:
            return result[0]
        if (len(result) % 2 == 1 and all(_IDENTIFIER.fullmatch(result[index]) for index in range(0, len(result), 2))
                and all(result[index] == "." for index in range(1, len(result), 2))):
            return "".join(result)
        return "\x00"

    @staticmethod
    def _word(value: bytes) -> bool:
        return value.isalnum() or value == b"_"

    def _is_shared_ref_span(self, span: tuple[int, int]) -> bool:
        start, end = span
        before = self.source[start - 1:start] if start > 0 else b""
        after = self.source[end:end + 1]
        if self._word(before) or self._word(after):
            return False
        if self.source[start:start + 6] != b"shared" or self._word(self.source[start + 6:start + 7]):
            return False
        mid = trivia_end(self.source, start + 6, block_comments=True)
        return mid >= 0 and self.source[mid:mid + 3] == b"ref" and mid + 3 == end

    def _token(self, node: Node, cursor: int, token: bytes) -> int:
        cursor = trivia_end(self.source, cursor, block_comments=True)
        end = cursor + len(token)
        if (self.source[cursor:end] != token
                or (self._word(token[-1:]) and self._word(self.source[end:end + 1]))):
            raise self.error("protocol", "syntax delimiter or keyword differs from source", node)
        return end

    def _child(self, node: Node, span: tuple[int, int], cursor: int, raw: object) -> int:
        if not isinstance(raw, dict):
            raise self.error("protocol", "syntax envelope requires a located child", node)
        child_span = self._span(raw.get("span"), span)
        if trivia_end(self.source, cursor, block_comments=True) != child_span[0]:
            raise self.error("protocol", "syntax child leaves source tokens uncovered", node)
        return child_span[1]

    def _list(self, node: Node, span: tuple[int, int], cursor: int, raw: object,
              opening: bytes = b"(", closing: bytes = b")", *, trailing: bool = True) -> int:
        if not isinstance(raw, list):
            raise self.error("protocol", "syntax envelope requires a child list", node)
        cursor = self._token(node, cursor, opening)
        for index, value in enumerate(raw):
            if index:
                cursor = self._token(node, cursor, b",")
            cursor = self._child(node, span, cursor, value)
        if raw and trailing:
            after = trivia_end(self.source, cursor, block_comments=True)
            if self.source[after:after + 1] == b",":
                cursor = after + 1
        return self._token(node, cursor, closing)

    def _generics(self, node: Node, span: tuple[int, int], cursor: int) -> int:
        values = node["generics"]
        if not isinstance(values, list):
            raise self.error("protocol", "generic telescope must be a child list", node)
        return self._list(node, span, cursor, values, b"<", b">") if values else cursor

    def _ordinary_envelope(self, node: Node, span: tuple[int, int]) -> None:
        kind = cast("str", node["kind"])
        cursor = span[0]
        if (layout := _FIXED_ENVELOPES.get(kind)) is not None:
            for part in layout:
                if isinstance(part, bytes):
                    cursor = self._token(node, cursor, part)
                else:
                    cursor = self._child(node, span, cursor, node[part])
        elif kind in {"definition", "function", "alias", "theorem", "lemma", "record", "union", "property"}:
            contracts = node.get("contracts")
            if node.get("cancel"):
                return  # These roles are refused by the mathematical consumer.
            if kind in {"theorem", "lemma"}:
                if not isinstance(contracts, list) or not contracts:
                    raise self.error("protocol", "theorem contracts must be a non-empty list", node)
                seen_ensures = False
                for item in contracts:
                    if not isinstance(item, dict) or item.get("kind") not in ("contract", "type_constraint"):
                        raise self.error("protocol", "theorem requires contract or type constraint nodes", node)
                    role = item.get("role") if item["kind"] == "contract" else "type_constraint"
                    if role == "ensures":
                        seen_ensures = True
                    elif seen_ensures or role not in ("decreases", "requires", "type_constraint"):
                        raise self.error(
                            "protocol",
                            "theorem contracts must be precontracts followed by ensures clauses",
                            node,
                        )
                if not seen_ensures:
                    raise self.error("protocol", "theorem requires at least one ensures clause", node)
            elif kind == "record" and contracts:
                if not isinstance(contracts, list) or any(
                    not isinstance(item, dict) or item.get("kind") != "contract"
                    for item in contracts
                ):
                    raise self.error("protocol", "record contracts must be contract nodes", node)
                if any(item.get("role") != "invariant" for item in contracts):
                    return
            elif contracts and (
                kind not in {"definition", "function"}
                or not isinstance(contracts, list)
                or any(
                    not isinstance(item, dict)
                    or (
                        item.get("kind") not in ("effects", "type_constraint")
                        and (
                            item.get("kind") != "contract"
                            or item.get("role") not in {"decreases", "requires", "ensures", "restores"}
                        )
                    )
                    for item in contracts
                )
            ):
                return
            modifiers = node["modifiers"]
            if not isinstance(modifiers, list) or any(not isinstance(item, str) for item in modifiers):
                raise self.error("protocol", "declaration modifiers must be a name list", node)
            for modifier in modifiers:
                cursor = self._token(node, cursor, cast("str", modifier).encode())
            if kind not in {"function", "property"}:
                cursor = self._token(node, cursor, kind.encode())
            if kind in {"definition", "function", "property"}:
                cursor = self._child(node, span, cursor, node["type" if kind == "property" else "result"])
            cursor = self._child(node, span, cursor, node["name"])
            if kind != "property":
                cursor = self._generics(node, span, cursor)
            if kind not in {"alias", "property", "union"}:
                cursor = self._list(node, span, cursor, node["parameters"])
            if contracts and isinstance(contracts, list):
                for contract_item in contracts:
                    cursor = self._child(node, span, cursor, contract_item)
            if kind in {"theorem", "lemma"}:
                if node["body"] is not None:
                    cursor = self._token(node, cursor, b"proof")
                    cursor = self._child(node, span, cursor, node["body"])
                else:
                    cursor = self._token(node, cursor, b";")
            elif kind == "record":
                after = trivia_end(self.source, cursor, block_comments=True)
                if self.source[after:after + 1] == b"{":
                    self._sequence_envelope(node, span, "declarations", after + 1, b"}")
                    return
                if node["declarations"]:
                    raise self.error("protocol", "semicolon record tail cannot carry member declarations", node)
                cursor = self._token(node, cursor, b";")
            elif kind == "union":
                constructors = node["constructors"]
                if (not isinstance(constructors, list)
                        or any(not isinstance(item, dict) or item.get("kind") != "constructor" for item in constructors)):
                    raise self.error("protocol", "union requires constructor children", node)
                cursor = self._token(node, cursor, b"{")
                self._sequence_envelope(node, span, "constructors", cursor, b"}")
                return
            elif kind in {"alias", "definition", "property"}:
                cursor = self._token(node, cursor, b"=" if kind == "alias" else b"=>")
                cursor = self._child(node, span, cursor, node["type"] if kind == "alias" else node["value"])
                cursor = self._token(node, cursor, b";")
            elif node["body"] is None:
                cursor = self._token(node, cursor, b";")
            else:
                cursor = self._child(node, span, cursor, node["body"])
        elif kind in {"interface", "impl"}:
            modifiers = node["modifiers"]
            if not isinstance(modifiers, list) or any(not isinstance(item, str) for item in modifiers):
                raise self.error("protocol", "declaration modifiers must be a name list", node)
            for modifier in modifiers:
                cursor = self._token(node, cursor, cast("str", modifier).encode())
            cursor = self._token(node, cursor, kind.encode())
            if kind == "interface":
                cursor = self._child(node, span, cursor, node["name"])
                cursor = self._generics(node, span, cursor)
            else:
                cursor = self._generics(node, span, cursor)
                cursor = self._child(node, span, cursor, node["type"])
            contracts = node["contracts"]
            if not isinstance(contracts, list) or any(
                not isinstance(item, dict) or item.get("kind") not in ("contract", "type_constraint")
                for item in contracts
            ):
                raise self.error("protocol", f"{kind} requires contract or type constraint nodes", node)
            for contract_item in contracts:
                cursor = self._child(node, span, cursor, contract_item)
            cursor = self._token(node, cursor, b"{")
            self._sequence_envelope(node, span, "declarations", cursor, b"}")
            return
        elif kind == "associated_type":
            modifiers = node["modifiers"]
            if not isinstance(modifiers, list) or any(not isinstance(item, str) for item in modifiers):
                raise self.error("protocol", "declaration modifiers must be a name list", node)
            for modifier in modifiers:
                cursor = self._token(node, cursor, cast("str", modifier).encode())
            cursor = self._token(node, cursor, b"type")
            cursor = self._child(node, span, cursor, node["name"])
            cursor = self._generics(node, span, cursor)
            if node["kind_annotation"] is not None:
                cursor = self._token(node, cursor, b":")
                cursor = self._child(node, span, cursor, node["kind_annotation"])
            contracts = node["contracts"]
            if not isinstance(contracts, list) or any(
                not isinstance(item, dict) or item.get("kind") not in ("contract", "type_constraint")
                for item in contracts
            ):
                raise self.error("protocol", "associated_type requires contract or type constraint nodes", node)
            for contract_item in contracts:
                cursor = self._child(node, span, cursor, contract_item)
            if node["definition"] is not None:
                cursor = self._token(node, cursor, b"=")
                cursor = self._child(node, span, cursor, node["definition"])
            cursor = self._token(node, cursor, b";")
        elif kind == "constructor":
            if node.get("contracts"):
                return
            cursor = self._child(node, span, cursor, node["name"])
            parameters = node["parameters"]
            if not isinstance(parameters, list):
                raise self.error("protocol", "constructor parameters must be a child list", node)
            after_name = trivia_end(self.source, cursor, block_comments=True)
            if self.source[after_name:after_name + 1] == b"(":
                cursor = self._list(node, span, cursor, parameters)
            elif parameters:
                raise self.error("protocol", "constructor parameters require parentheses", node)
            if node["result"] is not None:
                cursor = self._token(node, cursor, b":")
                cursor = self._child(node, span, cursor, node["result"])
            cursor = self._token(node, cursor, b";")
        elif kind in {"let", "var", "typed_local", "parameter", "lambda_parameter", "generic_parameter"}:
            if kind == "generic_parameter":
                if node["mode"] == "ghost":
                    cursor = self._token(node, cursor, b"ghost")
                    cursor = self._child(node, span, cursor, node["type"])
                elif node["mode"] == "region":
                    cursor = self._token(node, cursor, b"region")
                elif node["mode"] == "grade":
                    cursor = self._token(node, cursor, b"grade")
                elif node["mode"] != "type":
                    return
                cursor = self._child(node, span, cursor, node["name"])
                if node["mode"] == "grade" or (node["mode"] == "type" and node["type"] is not None):
                    cursor = self._token(node, cursor, b":")
                    cursor = self._child(node, span, cursor, node["type"])
            else:
                if kind in {"let", "var"}:
                    cursor = self._token(node, cursor, kind.encode())
                if kind in {"parameter", "lambda_parameter"} and node.get("const", False):
                    cursor = self._token(node, cursor, b"const")
                if node["type"] is not None:
                    cursor = self._child(node, span, cursor, node["type"])
                if node["name"] is not None:
                    cursor = self._child(node, span, cursor, node["name"])
                if kind == "parameter" and "label" in node:
                    if node["name"] is None:
                        raise self.error("protocol", "an argument label needs a local parameter", node)
                    cursor = self._token(node, cursor, b"as")
                    cursor = self._child(node, span, cursor, node["label"])
                if node["grade"] is not None:
                    cursor = self._token(node, cursor, b"@")
                    cursor = self._child(node, span, cursor, node["grade"])
                if kind in {"let", "var", "typed_local"}:
                    cursor = self._token(node, cursor, b"=")
                    cursor = self._child(node, span, cursor, node["value"])
                    if cursor < span[1]:
                        cursor = self._token(node, cursor, b";")
        elif kind in {"let_pattern", "var_pattern"}:
            pattern = node["pattern"]
            if (not isinstance(pattern, dict)
                    or pattern.get("kind") not in {"unit_pattern", "group_pattern", "tuple_pattern", "constructor_pattern"}):
                raise self.error("protocol", f"{kind} requires a parenthesized or constructor pattern", node)
            cursor = self._token(node, cursor, b"var" if kind == "var_pattern" else b"let")
            cursor = self._child(node, span, cursor, pattern)
            cursor = self._token(node, cursor, b"=")
            cursor = self._child(node, span, cursor, node["value"])
            if cursor < span[1]:
                cursor = self._token(node, cursor, b";")
        elif kind in {"let_else", "var_else"}:
            pattern = node["pattern"]
            if (not isinstance(pattern, dict)
                    or pattern.get("kind") not in {"unit_pattern", "group_pattern", "tuple_pattern", "constructor_pattern"}):
                raise self.error("protocol", f"{kind} requires a parenthesized or constructor pattern", node)
            if not isinstance(node["else"], dict) or node["else"].get("kind") != "block":
                raise self.error("protocol", f"{kind} requires a block else branch", node)
            cursor = self._token(node, cursor, b"var" if kind == "var_else" else b"let")
            cursor = self._child(node, span, cursor, pattern)
            cursor = self._token(node, cursor, b"=")
            cursor = self._child(node, span, cursor, node["value"])
            cursor = self._token(node, cursor, b"else")
            cursor = self._child(node, span, cursor, node["else"])
        elif kind == "assignment":
            op = node["operator"]
            if not isinstance(op, dict) or op.get("text") not in _ASSIGN_OPERATORS:
                raise self.error("protocol", "assignment operator differs from source", node)
            for field in ("target", "operator", "value"):
                cursor = self._child(node, span, cursor, node[field])
            cursor = self._token(node, cursor, b";")
        elif kind == "foreach":
            if not isinstance(node["range"], dict) or node["range"].get("kind") != "range":
                raise self.error("protocol", "foreach requires a range node", node)
            contracts = node["contracts"]
            if (not isinstance(contracts, list)
                    or any(not isinstance(item, dict) or item.get("kind") != "contract" for item in contracts)):
                raise self.error("protocol", "foreach contracts must be contract nodes", node)
            if not isinstance(node["body"], dict) or node["body"].get("kind") != "block":
                raise self.error("protocol", "foreach requires a block body", node)
            cursor = self._token(node, cursor, b"foreach")
            cursor = self._token(node, cursor, b"(")
            cursor = self._token(node, cursor, b"let")
            cursor = self._child(node, span, cursor, node["name"])
            if node.get("grade") is not None:
                cursor = self._token(node, cursor, b"@")
                cursor = self._child(node, span, cursor, node["grade"])
            cursor = self._token(node, cursor, b"in")
            cursor = self._child(node, span, cursor, node["range"])
            cursor = self._token(node, cursor, b")")
            for contract_item in contracts:
                cursor = self._child(node, span, cursor, contract_item)
            cursor = self._child(node, span, cursor, node["body"])
        elif kind == "foreach_collection":
            contracts = node["contracts"]
            if (not isinstance(contracts, list)
                    or any(not isinstance(item, dict) or item.get("kind") != "contract" for item in contracts)):
                raise self.error("protocol", "foreach_collection contracts must be contract nodes", node)
            if not isinstance(node["body"], dict) or node["body"].get("kind") != "block":
                raise self.error("protocol", "foreach_collection requires a block body", node)
            cursor = self._token(node, cursor, b"foreach")
            cursor = self._token(node, cursor, b"(")
            mode = cast("str", node["mode"])
            if mode == "value":
                after = trivia_end(self.source, cursor, block_comments=True)
                if node["type"] is None or (
                    self.source[after:after + 3] == b"let"
                    and not self._word(self.source[after + 3:after + 4])
                ):
                    cursor = self._token(node, cursor, b"let")
            else:
                cursor = self._token(node, cursor, mode.encode())
            if node["type"] is not None:
                cursor = self._child(node, span, cursor, node["type"])
            cursor = self._child(node, span, cursor, node["name"])
            if node.get("grade") is not None:
                cursor = self._token(node, cursor, b"@")
                cursor = self._child(node, span, cursor, node["grade"])
            cursor = self._token(node, cursor, b"in")
            cursor = self._child(node, span, cursor, node["collection"])
            cursor = self._token(node, cursor, b")")
            for contract_item in contracts:
                cursor = self._child(node, span, cursor, contract_item)
            cursor = self._child(node, span, cursor, node["body"])
        elif kind == "while":
            contracts = node["contracts"]
            if (not isinstance(contracts, list)
                    or any(not isinstance(item, dict) or item.get("kind") != "contract" for item in contracts)):
                raise self.error("protocol", "while contracts must be contract nodes", node)
            if not isinstance(node["body"], dict) or node["body"].get("kind") != "block":
                raise self.error("protocol", "while requires a block body", node)
            cursor = self._token(node, cursor, b"while")
            cursor = self._token(node, cursor, b"(")
            cursor = self._child(node, span, cursor, node["condition"])
            cursor = self._token(node, cursor, b")")
            for contract_item in contracts:
                cursor = self._child(node, span, cursor, contract_item)
            cursor = self._child(node, span, cursor, node["body"])
        elif kind == "open_invariant":
            resources = node["resources"]
            if not isinstance(resources, list) or not resources:
                raise self.error("protocol", "open requires a non-empty resource list", node)
            if not isinstance(node["body"], dict) or node["body"].get("kind") != "block":
                raise self.error("protocol", "open requires a block body", node)
            cursor = self._token(node, cursor, b"open")
            cursor = self._list(node, span, cursor, resources)
            lifts = node["lifts"]
            if not isinstance(lifts, list) or not lifts:
                raise self.error("protocol", "open lifts must be a non-empty identifier list", node)
            cursor = self._token(node, cursor, b"lifts")
            for index, item in enumerate(lifts):
                if index:
                    cursor = self._token(node, cursor, b",")
                cursor = self._child(node, span, cursor, item)
            after_lifts = trivia_end(self.source, cursor, block_comments=True)
            if self.source[after_lifts:after_lifts + 1] == b",":
                cursor = after_lifts + 1
            cursor = self._child(node, span, cursor, node["body"])
        elif kind == "return":
            cursor = self._token(node, cursor, b"return")
            if node["value"] is not None:
                cursor = self._child(node, span, cursor, node["value"])
            cursor = self._token(node, cursor, b";")
        elif kind == "assert":
            cursor = self._token(node, cursor, b"assert")
            cursor = self._child(node, span, cursor, node["value"])
            if node["by"] is not None:
                cursor = self._token(node, cursor, b"by")
                cursor = self._child(node, span, cursor, node["by"])
                if not isinstance(node["by"], dict) or node["by"].get("kind") != "block":
                    cursor = self._token(node, cursor, b";")
            else:
                cursor = self._token(node, cursor, b";")
        elif kind in {"calc", "proof"}:
            if not isinstance(node["body"], dict) or node["body"].get("kind") != "block":
                raise self.error("protocol", f"{kind} statement requires a block body", node)
            cursor = self._token(node, cursor, kind.encode())
            cursor = self._child(node, span, cursor, node["body"])
        elif kind in {"if", "if_expression"}:
            cursor = self._token(node, cursor, b"if")
            cursor = self._token(node, cursor, b"(")
            cursor = self._child(node, span, cursor, node["condition"])
            cursor = self._token(node, cursor, b")")
            cursor = self._child(node, span, cursor, node["then"])
            if kind == "if_expression" or node["else"] is not None:
                if node["else"] is None:
                    raise self.error("protocol", "if_expression requires an else branch", node)
                cursor = self._token(node, cursor, b"else")
                cursor = self._child(node, span, cursor, node["else"])
        elif kind in {"match", "match_expression"}:
            cursor = self._token(node, cursor, b"match")
            cursor = self._token(node, cursor, b"(")
            cursor = self._child(node, span, cursor, node["value"])
            cursor = self._token(node, cursor, b")")
            if node["motive"] is not None:
                if not isinstance(node["motive"], dict) or node["motive"].get("kind") != "match_motive":
                    raise self.error("protocol", "match motive must be a match_motive node", node)
                cursor = self._child(node, span, cursor, node["motive"])
            cases = node["cases"]
            expected_case = "expression_case" if kind == "match_expression" else "case"
            if (not isinstance(cases, list)
                    or any(not isinstance(item, dict) or item.get("kind") != expected_case for item in cases)):
                raise self.error("protocol", f"{kind} requires {expected_case} children", node)
            if kind == "match_expression":
                cursor = self._list(node, span, cursor, cases, b"{", b"}")
            else:
                cursor = self._token(node, cursor, b"{")
                for item in cases:
                    cursor = self._child(node, span, cursor, item)
                    after = trivia_end(self.source, cursor, block_comments=True)
                    if self.source[after:after + 1] == b",":
                        cursor = after + 1
                cursor = self._token(node, cursor, b"}")
        elif kind == "case":
            if not isinstance(node["pattern"], dict) or node["pattern"].get("kind") not in _PATTERN_KINDS:
                raise self.error("protocol", "match arm requires a pattern node", node)
            cursor = self._child(node, span, cursor, node["pattern"])
            cursor = self._token(node, cursor, b"=>")
            self._sequence_envelope(node, span, "statements", cursor)
            return
        elif kind == "expression_case":
            if not isinstance(node["pattern"], dict) or node["pattern"].get("kind") not in _PATTERN_KINDS:
                raise self.error("protocol", "match arm requires a pattern node", node)
            cursor = self._child(node, span, cursor, node["pattern"])
            cursor = self._token(node, cursor, b"=>")
            cursor = self._child(node, span, cursor, node["value"])
        elif kind == "match_motive":
            cursor = self._token(node, cursor, b"as")
            cursor = self._child(node, span, cursor, node["name"])
            if node.get("grade") is not None:
                cursor = self._token(node, cursor, b"@")
                cursor = self._child(node, span, cursor, node["grade"])
            cursor = self._token(node, cursor, b":")
            cursor = self._child(node, span, cursor, node["type"])
        elif kind == "wildcard_pattern":
            if self._word(self.source[span[0] - 1:span[0]]):
                raise self.error("protocol", "wildcard pattern splits a source token", node)
            cursor = self._token(node, cursor, b"_")
        elif kind == "binding_pattern":
            name = node["name"]
            if (not isinstance(name, dict) or not isinstance(name.get("text"), str)
                    or not name["text"] or name["text"] == "_" or "." in name["text"]
                    or ("A" <= name["text"][0] <= "Z")):
                raise self.error("protocol", "binding_pattern requires a lowercase or '_' non-wildcard unqualified name", node)
            cursor = self._child(node, span, cursor, name)
            if node.get("grade") is not None:
                cursor = self._token(node, cursor, b"@")
                cursor = self._child(node, span, cursor, node["grade"])
        elif kind == "constructor_pattern":
            cname = node["name"]
            arguments = node["arguments"]
            if (not isinstance(cname, dict) or not isinstance(cname.get("text"), str)
                    or not cname["text"].rsplit(".", 1)[-1]
                    or not ("A" <= cname["text"].rsplit(".", 1)[-1][0] <= "Z")):
                raise self.error("protocol", "constructor_pattern requires an uppercase constructor name", node)
            if (not isinstance(arguments, list)
                    or any(not isinstance(item, dict) or item.get("kind") not in _PATTERN_ARGUMENT_KINDS for item in arguments)):
                raise self.error("protocol", "constructor_pattern arguments must be pattern nodes", node)
            cursor = self._child(node, span, cursor, cname)
            if arguments:
                cursor = self._list(node, span, cursor, arguments)
        elif kind == "labeled_pattern":
            if not isinstance(node["pattern"], dict) or node["pattern"].get("kind") not in _PATTERN_KINDS:
                raise self.error("protocol", "labeled_pattern requires a pattern child", node)
            cursor = self._child(node, span, cursor, node["label"])
            cursor = self._token(node, cursor, b":")
            cursor = self._child(node, span, cursor, node["pattern"])
        elif kind == "binary":
            op = node["operator"]
            if not isinstance(op, dict) or op.get("text") not in _OPERATORS:
                raise self.error("protocol", "binary operator differs from source", node)
            for field in ("left", "operator", "right"):
                cursor = self._child(node, span, cursor, node[field])
        elif kind == "is":
            if not isinstance(node["pattern"], dict) or node["pattern"].get("kind") not in _PATTERN_KINDS:
                raise self.error("protocol", "is expression requires a pattern child", node)
            cursor = self._child(node, span, cursor, node["value"])
            cursor = self._token(node, cursor, b"is")
            cursor = self._child(node, span, cursor, node["pattern"])
        elif kind == "with_expression":
            updates = node["updates"]
            if (not isinstance(updates, list) or not updates
                    or any(not isinstance(item, dict) or item.get("kind") != "field_update" for item in updates)):
                raise self.error("protocol", "with_expression requires nonempty field_update children", node)
            cursor = self._child(node, span, cursor, node["value"])
            cursor = self._token(node, cursor, b"with")
            cursor = self._list(node, span, cursor, updates, b"{", b"}")
        elif kind in {"group", "group_type", "group_pattern", "operator"}:
            cursor = self._token(node, cursor, b"(")
            field = {"group": "value", "group_type": "type", "group_pattern": "pattern", "operator": "name"}[kind]
            if kind == "group_pattern" and (not isinstance(node["pattern"], dict) or node["pattern"].get("kind") not in _PATTERN_KINDS):
                raise self.error("protocol", "group_pattern requires a pattern child", node)
            cursor = self._child(node, span, cursor, node[field])
            cursor = self._token(node, cursor, b")")
        elif kind in {"tuple", "tuple_type", "tuple_pattern"}:
            field = {"tuple": "values", "tuple_type": "types", "tuple_pattern": "patterns"}[kind]
            if kind == "tuple_pattern":
                patterns = node["patterns"]
                if (not isinstance(patterns, list) or len(patterns) < 2
                        or any(not isinstance(item, dict) or item.get("kind") not in _PATTERN_KINDS for item in patterns)):
                    raise self.error("protocol", "tuple_pattern requires at least two pattern children", node)
            cursor = self._list(node, span, cursor, node[field], trailing=False)
        elif kind == "type":
            cursor = self._child(node, span, cursor, node["name"])
            values = node["arguments"]
            if not isinstance(values, list):
                raise self.error("protocol", "type arguments must be a child list", node)
            if values:
                cursor = self._list(node, span, cursor, values, b"<", b">")
        elif kind == "function_type":
            if node["captures"]:
                return
            cursor = self._token(node, cursor, cast("str", node["mode"]).encode())
            cursor = self._generics(node, span, cursor)
            cursor = self._list(node, span, cursor, node["parameters"])
            cursor = self._token(node, cursor, b"->")
            cursor = self._child(node, span, cursor, node["result"])
            if node["effects"]:
                cursor = self._token(node, cursor, b"effects")
                cursor = self._list(node, span, cursor, node["effects"])
            if node["contracts"]:
                clauses = node["contracts"]
                if not isinstance(clauses, list) or any(
                    not isinstance(clause, dict) or clause.get("kind") not in ("contract", "effects")
                    for clause in clauses
                ):
                    raise self.error("protocol", "callable type requires contract nodes", node)
                cursor = self._token(node, cursor, b"with")
                cursor = self._token(node, cursor, b"{")
                for clause in clauses:
                    cursor = self._child(node, span, cursor, clause)
                    cursor = self._token(node, cursor, b";")
                cursor = self._token(node, cursor, b"}")
        elif kind == "generic_application":
            cursor = self._child(node, span, cursor, node["value"])
            if not node["arguments"]:
                raise self.error("protocol", "generic application requires nonempty arguments", node)
            cursor = self._list(node, span, cursor, node["arguments"], b"<", b">")
            if self.source[cursor:cursor + 1] == b"=":
                raise self.error("protocol", "generic application requires a standalone '>' token", node)
            following = trivia_end(self.source, cursor, block_comments=True)
            if following < 0 or _GENERIC_APPLICATION_FOLLOW.match(self.source, following) is None:
                raise self.error("protocol", "generic application has an invalid following token", node)
        elif kind == "let_expression":
            binding = node["binding"]
            if not isinstance(binding, dict) or binding.get("kind") not in {"let", "typed_local", "let_pattern"}:
                raise self.error("protocol", "let_expression requires a local binding", node)
            cursor = self._child(node, span, cursor, binding)
            if self.source[cursor - 1:cursor] == b";":
                raise self.error("protocol", "let_expression binding cannot carry a statement semicolon", node)
            cursor = self._token(node, cursor, b"in")
            cursor = self._child(node, span, cursor, node["body"])
        elif kind == "quantifier":
            cursor = self._token(node, cursor, cast("str", node["quantifier"]).encode())
            cursor = self._list(node, span, cursor, node["parameters"])
            cursor = self._token(node, cursor, b"=>")
            cursor = self._child(node, span, cursor, node["value"])
        elif kind == "contract":
            if node["role"] not in {"decreases", "requires", "ensures", "restores", "invariant"}:
                return
            if "name" in node and node["role"] != "invariant":
                raise self.error("protocol", "only invariant contracts may carry a clause name", node)
            cursor = self._token(node, cursor, cast("str", node["role"]).encode())
            if "name" in node and node["name"] is not None:
                cursor = self._child(node, span, cursor, node["name"])
                cursor = self._token(node, cursor, b":")
            cursor = self._child(node, span, cursor, node["value"])
        elif kind == "type_constraint":
            parameter = node["parameter"]
            spelling = parameter.get("text") if isinstance(parameter, dict) else None
            if not isinstance(spelling, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", spelling):
                raise self.error("protocol", "type constraint requires an unqualified parameter name", node)
            bounds = node["bounds"]
            if not isinstance(bounds, list) or not bounds or any(
                not isinstance(bound, dict) or bound.get("kind") != "type" for bound in bounds
            ):
                raise self.error("protocol", "type constraint requires named interface bounds", node)
            cursor = self._token(node, cursor, b"where")
            cursor = self._child(node, span, cursor, parameter)
            cursor = self._token(node, cursor, b":")
            for index, bound in enumerate(bounds):
                if index:
                    cursor = self._token(node, cursor, b",")
                cursor = self._child(node, span, cursor, bound)
        elif kind == "modified_type":
            modifier = cast("str", node["modifier"])
            if modifier == "shared_ref":
                cursor = self._token(node, cursor, b"shared")
                cursor = self._token(node, cursor, b"ref")
            else:
                cursor = self._token(node, cursor, modifier.encode())
            if node.get("lifetime") is not None:
                cursor = self._child(node, span, cursor, node["lifetime"])
            cursor = self._child(node, span, cursor, node["type"])
        elif kind == "lifetime":
            after_lt = trivia_end(self.source, cursor, block_comments=True)
            if self.source[after_lt:after_lt + 1] == b"<":
                cursor = self._token(node, cursor, b"<")
                cursor = self._child(node, span, cursor, node["name"])
                cursor = self._token(node, cursor, b">")
            else:
                cursor = self._child(node, span, cursor, node["name"])
        elif kind == "effects":
            values = node["values"]
            if not isinstance(values, list) or not values:
                raise self.error("protocol", "effects clause requires a non-empty list", node)
            cursor = self._token(node, cursor, b"effects")
            for index, value in enumerate(values):
                if index:
                    cursor = self._token(node, cursor, b",")
                cursor = self._child(node, span, cursor, value)
            after = trivia_end(self.source, cursor, block_comments=True)
            if self.source[after:after + 1] == b",":
                cursor = after + 1
        elif kind == "import":
            modifiers = node.get("modifiers", [])
            if not isinstance(modifiers, list) or modifiers:
                raise self.error("protocol", "import declarations cannot carry modifiers", node)
            cursor = self._token(node, cursor, b"import")
            cursor = self._child(node, span, cursor, node["name"])
            if "items" in node:
                items = node["items"]
                if "alias" in node or not isinstance(items, list) or not items or any(
                    not isinstance(item, dict) or item.get("kind") != "import_item" for item in items
                ):
                    raise self.error("protocol", "selective imports require a nonempty list of import items", node)
                cursor = self._list(node, span, cursor, items, b"{", b"}")
            elif "alias" in node:
                cursor = self._token(node, cursor, b"as")
                cursor = self._child(node, span, cursor, node["alias"])
            cursor = self._token(node, cursor, b";")
        elif kind == "import_item":
            cursor = self._child(node, span, cursor, node["name"])
            if node["alias"] is not None:
                cursor = self._token(node, cursor, b"as")
                cursor = self._child(node, span, cursor, node["alias"])
        else:
            return
        if cursor != span[1]:
            raise self.error("protocol", "syntax envelope leaves trailing source tokens uncovered", node)

    def _lambda_envelope(self, node: Node, span: tuple[int, int]) -> None:
        parameters = node["parameters"]
        body = node["body"]
        if not isinstance(parameters, list) or not isinstance(body, dict):
            raise self.error("protocol", "lambda has invalid parameters or body", node)
        body_span = self._span(body.get("span"), span)
        if body_span[1] != span[1]:
            raise self.error("protocol", "lambda body leaves trailing source tokens", node)
        cursor = span[0]
        parenthesized = self.source[cursor:cursor + 1] == b"("
        if parenthesized:
            cursor += 1
        elif len(parameters) != 1:
            raise self.error("protocol", "a bare lambda requires one parameter", node)
        for index, parameter in enumerate(parameters):
            if not isinstance(parameter, dict):
                raise self.error("protocol", "lambda has an invalid parameter", node)
            parameter_span = self._span(parameter.get("span"), span)
            if trivia_end(self.source, cursor, block_comments=True) != parameter_span[0]:
                raise self.error("protocol", "lambda parameter leaves source tokens uncovered", node)
            if not parenthesized and parameter.get("type") is not None:
                raise self.error("protocol", "a bare lambda parameter cannot carry a type", node)
            cursor = trivia_end(self.source, parameter_span[1], block_comments=True)
            if index != len(parameters) - 1:
                if self.source[cursor:cursor + 1] != b",":
                    raise self.error("protocol", "lambda parameter separator differs from source", node)
                cursor += 1
        cursor = trivia_end(self.source, cursor, block_comments=True)
        if parenthesized:
            if parameters and self.source[cursor:cursor + 1] == b",":
                cursor = trivia_end(self.source, cursor + 1, block_comments=True)
            if self.source[cursor:cursor + 1] != b")":
                raise self.error("protocol", "lambda parameter delimiter differs from source", node)
            cursor = trivia_end(self.source, cursor + 1, block_comments=True)
        if (self.source[cursor:cursor + 2] != b"=>"
                or trivia_end(self.source, cursor + 2, block_comments=True) != body_span[0]):
            raise self.error("protocol", "lambda arrow or body leaves source tokens uncovered", node)

    def _call_envelope(self, node: Node, span: tuple[int, int]) -> None:
        callee, arguments = node["callee"], node["arguments"]
        if not isinstance(callee, dict) or not isinstance(arguments, list):
            raise self.error("protocol", "call has invalid callee or arguments", node)
        callee_span = self._span(callee.get("span"), span)
        cursor = trivia_end(self.source, callee_span[1], block_comments=True)
        if callee_span[0] != span[0] or self.source[cursor:cursor + 1] != b"(":
            raise self.error("protocol", "call callee or opening differs from source", node)
        cursor += 1
        for index, argument in enumerate(arguments):
            if not isinstance(argument, dict) or argument.get("kind") != "argument":
                raise self.error("protocol", "call requires located argument wrappers", node)
            argument_span = self._span(argument.get("span"), span)
            if trivia_end(self.source, cursor, block_comments=True) != argument_span[0]:
                raise self.error("protocol", "call argument leaves source tokens uncovered", node)
            cursor = trivia_end(self.source, argument_span[1], block_comments=True)
            if index != len(arguments) - 1:
                if self.source[cursor:cursor + 1] != b",":
                    raise self.error("protocol", "call argument separator differs from source", node)
                cursor += 1
        cursor = trivia_end(self.source, cursor, block_comments=True)
        if arguments and self.source[cursor:cursor + 1] == b",":
            cursor = trivia_end(self.source, cursor + 1, block_comments=True)
        if self.source[cursor:cursor + 1] != b")" or cursor + 1 != span[1]:
            raise self.error("protocol", "call closing or argument list differs from source", node)

    def _constant_envelope(self, node: Node, span: tuple[int, int]) -> None:
        annotation, name, value = node["type"], node["name"], node["value"]
        if not all(isinstance(part, dict) for part in (annotation, name, value)):
            raise self.error("protocol", "constant requires a type, name and initializer", node)
        annotation_span = self._span(cast("Node", annotation).get("span"), span)
        name_span = self._span(cast("Node", name).get("span"), span)
        value_span = self._span(cast("Node", value).get("span"), span)
        modifiers = node.get("modifiers", [])
        if not isinstance(modifiers, list) or any(not isinstance(item, str) for item in modifiers):
            raise self.error("protocol", "constant modifiers must be a list of names", node)
        cursor = span[0]
        for spelling in (*modifiers, "const"):
            token = cast("str", spelling).encode()
            following = self.source[cursor + len(token):cursor + len(token) + 1]
            if (self.source[cursor:cursor + len(token)] != token
                    or following.isalnum() or following == b"_"):
                raise self.error("protocol", "constant keyword or modifiers differ from source", node)
            cursor = trivia_end(self.source, cursor + len(token), block_comments=True)
        if cursor != annotation_span[0]:
            raise self.error("protocol", "constant type leaves source tokens uncovered", node)
        if trivia_end(self.source, annotation_span[1], block_comments=True) != name_span[0]:
            raise self.error("protocol", "constant name leaves source tokens uncovered", node)
        cursor = trivia_end(self.source, name_span[1], block_comments=True)
        if (self.source[cursor:cursor + 1] != b"="
                or trivia_end(self.source, cursor + 1, block_comments=True) != value_span[0]):
            raise self.error("protocol", "constant initializer differs from source", node)
        cursor = trivia_end(self.source, value_span[1], block_comments=True)
        if self.source[cursor:cursor + 1] != b";" or cursor + 1 != span[1]:
            raise self.error("protocol", "constant terminator leaves source tokens uncovered", node)

    def _sequence_envelope(self, node: Node, span: tuple[int, int], role: str,
                           cursor: int, closing: bytes = b"") -> None:
        values = node[role]
        if not isinstance(values, list):
            raise self.error("protocol", f"{role} must be an ordered syntax list", node)
        for value in values:
            if not isinstance(value, dict):
                raise self.error("protocol", f"{role} contains an invalid syntax node", node)
            child_span = self._span(value.get("span"), span)
            if trivia_end(self.source, cursor, block_comments=True) != child_span[0]:
                raise self.error("protocol", f"{role} are reordered or leave source tokens uncovered", node)
            cursor = child_span[1]
        end = trivia_end(self.source, cursor, block_comments=True)
        if not closing and cursor <= span[1] <= end:
            return
        cursor = end
        if self.source[cursor:cursor + len(closing)] != closing or cursor + len(closing) != span[1]:
            raise self.error("protocol", f"{role} leave trailing source tokens uncovered", node)

    def visit(self, raw: object, parent: tuple[int, int], depth: int = 0) -> None:
        if depth > MAX_DEPTH or self.remaining <= 0:
            raise self.error("limit", "surface syntax exceeds elaboration bounds")
        self.remaining -= 1
        if isinstance(raw, list):
            for value in raw:
                self.visit(value, parent, depth + 1)
            return
        if raw is None or isinstance(raw, (str, bool)):
            return
        if not isinstance(raw, dict):
            raise self.error("protocol", "unexpected syntax payload")
        node = cast("Node", raw)
        span = self._span(node.get("span"), parent)
        if "text" in node:
            text = node["text"]
            if text == "shared_ref" and self._is_shared_ref_span(span):
                if set(node) != {"text", "span"}:
                    raise self.error("protocol", "syntax identifier or operator differs from its source", node)
                return
            if (set(node) != {"text", "span"} or not isinstance(text, str)
                    or not (_IDENTIFIER.fullmatch(text) or text in _OPERATORS
                            or text in _ASSIGN_OPERATORS
                            or re.fullmatch(r"[?'][A-Za-z_][A-Za-z_0-9]*", text))
                    or self._compact_name(self.source[span[0]:span[1]]) != text):
                raise self.error("protocol", "syntax identifier or operator differs from its source", node)
            if ((_IDENTIFIER.fullmatch(text) or text.startswith(("?", "'")))
                    and (self._word(self.source[span[0] - 1:span[0]])
                         or self._word(self.source[span[1]:span[1] + 1]))):
                raise self.error("protocol", "syntax identifier splits a source token", node)
            return
        kind = node.get("kind")
        if not isinstance(kind, str):
            raise self.error("protocol", "syntax node has no kind", node)
        fields = _FIELDS.get(kind)
        if fields is None:
            raise self.error("unsupported", f"'{kind}' is outside mathematical elaboration", node)
        optional = _OPTIONAL_FIELDS.get(kind, set())
        if (set(node) - optional != {"kind", "span", *fields}
                or ("const" in node and type(node["const"]) is not bool)):
            raise self.error("protocol", f"invalid fields for '{kind}'", node)
        if kind in _SYNTAX_WORDS:
            field, spellings = _SYNTAX_WORDS[kind]
            word = node[field]
            if not isinstance(word, str) or word not in spellings:
                raise self.error("protocol", f"invalid syntax word for '{kind}.{field}'", node)
        if node.get("const", False) and kind == "lambda_parameter" and node["type"] is None:
            raise self.error("protocol", "a constant lambda parameter requires an explicit type", node)
        if ("grade" in fields or "grade" in optional) and node.get("grade") is not None:
            grade = node["grade"]
            if not isinstance(grade, dict) or not isinstance(grade.get("kind"), str):
                raise self.error("protocol", "optional grade must be null or a located syntax node", node)
            self._span(grade.get("span"), span)
        self._ordinary_envelope(node, span)
        if kind == "unary":
            op = node["operator"]
            if isinstance(op, dict) and op.get("text") == "shared_ref":
                op_span = self._span(op.get("span"), span)
                if not self._is_shared_ref_span(op_span):
                    raise self.error("protocol", "shared_ref operator differs from source", node)
        if kind == "hole":
            name = node["name"]
            spelling = self.source[span[0]:span[1]]
            if (not re.fullmatch(rb"\?[A-Za-z_][A-Za-z_0-9]*", spelling)
                    or not isinstance(name, dict) or name.get("span") != node["span"]
                    or name.get("text") != spelling.decode("ascii")):
                raise self.error("protocol", "named hole differs from its source", node)
            if len(self.holes) >= MAX_HOLES:
                raise self.error("limit", f"source exceeds the {MAX_HOLES} named-hole diagnostic budget", node)
            self.holes[span[0]] = node
        if kind in {"nat", "nat_pattern"}:
            value, suffix = node["value"], node["suffix"]
            if not isinstance(value, str) or not isinstance(suffix, str):
                raise self.error("protocol", "invalid numeric literal payload", node)
            digits = value[2:] if value.startswith(("0x", "0X", "0b", "0B")) else value
            if len(digits.replace("_", "")) > MAX_LITERAL_DIGITS:
                raise self.error("limit", "numeric literal exceeds digit bound", node)
            if self.source[span[0]:span[1]] != (value + suffix).encode():
                raise self.error("protocol", "numeric literal differs from its source", node)
            if suffix not in _INT_SUFFIXES or not (
                DECIMAL.fullmatch(value) or _HEX_LITERAL.fullmatch(value) or _BIN_LITERAL.fullmatch(value)
            ):
                raise self.error("unsupported", "unsupported numeric literal format or suffix", node)
        if kind in {"bool", "bool_pattern"}:
            value = node["value"]
            if type(value) is not bool or self.source[span[0]:span[1]] != (b"true" if value else b"false"):
                raise self.error("protocol", "Boolean literal differs from its source", node)
        if kind in {"string", "string_pattern", "interpolated_string", "character", "character_pattern"}:
            value = node["value"]
            if not isinstance(value, str) or self.source[span[0]:span[1]] != value.encode("utf-8"):
                raise self.error("protocol", "character or string literal differs from its source", node)
            if kind in {"string", "string_pattern"} and (
                len(value) < 2 or not value.startswith('"') or not value.endswith('"')
            ):
                raise self.error("protocol", "string literal lacks quotation delimiters", node)
            if kind == "interpolated_string" and (
                len(value) < 3 or not value.startswith('$"') or not value.endswith('"')
            ):
                raise self.error("protocol", "interpolated string literal lacks quotation delimiters", node)
            if kind in {"character", "character_pattern"} and (
                len(value) < 3 or not value.startswith("'") or not value.endswith("'")
            ):
                raise self.error("protocol", "character literal lacks single-quote delimiters", node)
        if kind in {"unit", "unit_pattern"}:
            cursor = trivia_end(self.source, span[0] + 1, block_comments=True)
            if (self.source[span[0]:span[0] + 1] != b"("
                    or self.source[cursor:cursor + 1] != b")" or cursor + 1 != span[1]):
                raise self.error("protocol", "unit value differs from its source", node)
        if kind in {"block", "case"}:
            statements = node["statements"]
            if isinstance(statements, list):
                for statement in statements:
                    if isinstance(statement, dict) and statement.get("kind") in {
                        "let",
                        "var",
                        "typed_local",
                        "let_pattern",
                        "var_pattern",
                    }:
                        statement_span = self._span(statement.get("span"), span)
                        if self.source[statement_span[1] - 1:statement_span[1]] != b";":
                            raise self.error("protocol", "statement local binding lacks its semicolon", statement)
        if kind == "expression_body":
            if (self.source[span[0]:span[0] + 2] != b"=>"
                    or self.source[span[1] - 1:span[1]] != b";"):
                raise self.error("protocol", "expression body differs from its source delimiters", node)
            value = node["value"]
            if not isinstance(value, dict):
                raise self.error("protocol", "expression body has no value node", node)
            value_span = self._span(value.get("span"), (span[0] + 2, span[1] - 1))
            if (trivia_end(self.source, span[0] + 2, block_comments=True) != value_span[0]
                    or trivia_end(self.source, value_span[1], block_comments=True) != span[1] - 1):
                raise self.error("protocol", "expression body leaves source tokens uncovered", node)
        if kind == "lambda":
            self._lambda_envelope(node, span)
        if kind == "call":
            self._call_envelope(node, span)
        if kind in {"constant", "constant_local"}:
            self._constant_envelope(node, span)
        if kind == "surface_file":
            name = node["name"]
            if not isinstance(name, dict):
                raise self.error("protocol", "module requires its located name", node)
            name_span = self._span(name.get("span"), span)
            cursor = trivia_end(self.source, span[0] + len(b"module"), block_comments=True)
            if (self.source[span[0]:span[0] + len(b"module")] != b"module"
                    or self._word(self.source[span[0] + len(b"module"):span[0] + len(b"module") + 1])
                    or cursor != name_span[0]):
                raise self.error("protocol", "module header differs from source", node)
            cursor = trivia_end(self.source, name_span[1], block_comments=True)
            if self.source[cursor:cursor + 1] != b";":
                raise self.error("protocol", "module header lacks its source terminator", node)
            self._sequence_envelope(node, span, "declarations", cursor + 1)
        if kind == "block":
            if self.source[span[0]:span[0] + 1] != b"{":
                raise self.error("protocol", "block opening differs from source", node)
            self._sequence_envelope(node, span, "statements", span[0] + 1, b"}")
        if kind == "argument":
            value = node["value"]
            if not isinstance(value, dict):
                raise self.error("protocol", "call argument has no expression", node)
            value_span = self._span(value.get("span"), span)
            label = node["label"]
            if label is None:
                if value_span != span:
                    raise self.error("protocol", "positional argument leaves source tokens uncovered", node)
            else:
                if not isinstance(label, dict):
                    raise self.error("protocol", "call argument has an invalid label", node)
                label_span = self._span(label.get("span"), span)
                cursor = trivia_end(self.source, label_span[1], block_comments=True)
                if (label_span[0] != span[0] or self.source[cursor:cursor + 1] != b":"
                        or trivia_end(self.source, cursor + 1, block_comments=True) != value_span[0]
                        or value_span[1] != span[1]):
                    raise self.error("protocol", "argument label differs from source delimiters", node)
        if kind == "lambda_parameter" and node["type"] is None:
            name = node["name"]
            if not isinstance(name, dict):
                raise self.error("protocol", "inferred lambda parameter has no binder", node)
            name_span = self._span(name.get("span"), span)
            if name_span[0] != span[0] or (node["grade"] is None and name_span != span):
                raise self.error("protocol", "inferred lambda parameter has an annotation span", node)
        for key, value in node.items():
            if key not in {"span", "kind"}:
                self.visit(value, span, depth + 1)

    def decode(self, response: object) -> Node:
        if (not isinstance(response, dict) or set(response) != {"schema", "source_sha256", "ast"}
                or type(response["schema"]) is not int or response["schema"] != 2
                or response["source_sha256"] != hashlib.sha256(self.source).hexdigest()):
            raise self.error("protocol", "surface response has invalid schema or source binding")
        if not isinstance(response["ast"], dict):
            raise self.error("protocol", "expected a complete surface_file object")
        self.visit(response["ast"], (0, len(self.source)))
        root = cast("Node", response["ast"])
        if root.get("kind") != "surface_file":
            raise self.error("protocol", "expected a complete surface_file")
        start, end = cast("list[int]", root["span"])
        if (trivia_end(self.source, 0, block_comments=True) != start
                or trivia_end(self.source, end, block_comments=True) != len(self.source)):
            raise self.error("protocol", "module omits nontrivial source outside its span", root)
        return root
