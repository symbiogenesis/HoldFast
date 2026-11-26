# SPDX-License-Identifier: Apache-2.0
"""Project natural-graded source into the dependent and modal Rocq checkers."""

import hashlib
import json
import re
import shutil
import subprocess
import tempfile
import time
from collections.abc import Callable, Mapping
from contextlib import ExitStack
from contextvars import ContextVar
from dataclasses import dataclass
from enum import StrEnum
from itertools import batched
from pathlib import Path
from types import MappingProxyType
from typing import cast, override

from filelock import FileLock

from toolchain import parser, proofenv
from toolchain.elaborate_intrinsics import _IntrinsicsMixin
from toolchain.elaborate_protocol import _Protocol, syntax_nodes
from toolchain.elaborate_types import Node
from toolchain.source_file import ensure_unchanged, read_source


class GradeDomain(StrEnum):
    EXACT = "NatExact"
    BOUND = "NatBound"


_PRIMITIVES = frozenset({"Nat", "Vec", "Type", *GradeDomain})
_ROCQ_FILES = ("graded_pure.v", "graded_domains.v", "graded_source.v")
_MODAL_FILES = ("graded_pure.v", "graded_domains.v", "graded_modal.v", "graded_modal_source.v")
SUPPORT_FILES = tuple(dict.fromkeys((*_ROCQ_FILES, *_MODAL_FILES)))
REPLAY_DEADLINE: ContextVar[float | None] = ContextVar("graded_replay_deadline", default=None)
_REPORT = re.compile(r"=\s*(\[[0-9\s;\[\]]*\])\s*:\s*list\s+\(list\s+\(list\s+nat\)\)")


def _name(node: object) -> str:
    return cast("str", cast("Node", node)["text"])


def _span(node: Node) -> list[int]:
    return cast("list[int]", node["span"])


@dataclass(frozen=True)
class _Parameter:
    index: int
    name: str
    span: list[int]
    domain: str
    allowance: int

    def abstract(self, constructor: str, body: str) -> str:
        return f"({constructor} {self.index} {self.allowance} {self.domain} {body})"


@dataclass(frozen=True)
class _Definition:
    index: int
    name: str
    source: Node
    term: str
    expected: str
    context: str | None = None
    records: tuple[str, ...] = ()


@dataclass(frozen=True)
class GradeExport:
    protocol: _Protocol
    syntax: Node
    name: str
    domain: GradeDomain
    receipt: str
    imports: Mapping[str, tuple[str, GradeExport]]
    modal: bool = False
    box_imports: Mapping[str, GradeDomain] = MappingProxyType({})


type GradeResolver = Callable[[str], tuple[str, GradeExport] | None]
type BoxResolver = Callable[[str], GradeDomain | None]


class _Projection:
    reserved = _PRIMITIVES

    def __init__(self, protocol: _Protocol, syntax: Node, domain: GradeDomain) -> None:
        self.protocol = protocol
        self.domain = domain
        self.declarations: dict[str, Node] = {}
        self.parameters: list[_Parameter] = []
        self.completed: dict[str, _Definition] = {}
        self.definitions: list[_Definition] = []
        self.annotations: set[int] = set()
        self.resolve_import: GradeResolver | None = None
        self.imports: dict[str, tuple[str, GradeExport]] = {}
        self.providers: dict[int, _Projection] = {}
        self.provider_receipts: set[tuple[str, str]] = set()
        for declaration in cast("list[Node]", syntax["declarations"]):
            if declaration["kind"] in {"import", "import_item"}:
                continue
            if declaration.get("name") is None:
                continue
            name = _name(declaration["name"])
            if name in _PRIMITIVES or name in self.declarations:
                raise self.protocol.error("grade", f"ambiguous declaration '{name}' in graded source replay", declaration)
            self.declarations[name] = declaration

    def _literal(self, node: Node) -> int:
        if node["kind"] != "nat" or node["suffix"]:
            raise self.protocol.error("unsupported", "expected a plain natural literal", node)
        spelling = cast("str", node["value"]).replace("_", "")
        if not spelling.isdecimal():
            raise self.protocol.error("unsupported", "expected a decimal natural literal", node)
        value = int(spelling)
        if value > 1024:
            raise self.protocol.error("limit", "graded source literals are bounded at 1024", node)
        return value

    def _grade(self, node: Node) -> int:
        grade = cast("Node | None", node["grade"])
        if grade is not None and grade["kind"] == "call":
            callee = cast("Node", grade["callee"])
            arguments = cast("list[Node]", grade["arguments"])
            if callee["kind"] == "name" and _name(callee["name"]) == self.domain and len(arguments) == 1:
                [argument] = arguments
                if argument["label"] is None:
                    allowance = self._literal(cast("Node", argument["value"]))
                    self.annotations.add(id(node))
                    return allowance
        raise self.protocol.error("unsupported", f"graded binders require an explicit @ {self.domain}(n) allowance", node)

    def _parameter(self, node: Node, scope: dict[str, _Parameter]) -> _Parameter:
        if node["name"] is None or node["type"] is None or node.get("const") or node.get("label"):
            raise self.protocol.error("unsupported", "graded replay requires named parameters with plain types", node)
        return self._bind(node, scope, self._type(cast("Node", node["type"]), scope), self._grade(node))

    def _bind(self, node: Node, scope: dict[str, _Parameter], domain: str, allowance: int) -> _Parameter:
        name = _name(node["name"])
        if name in self.reserved:
            raise self.protocol.error("grade", f"graded binder shadows primitive '{name}'", node)
        if name == "_" or "." in name or name in scope:
            raise self.protocol.error("grade", f"duplicate or invalid graded binder '{name}'", node)
        if len(self.parameters) == 256:
            raise self.protocol.error("limit", "graded source replay is bounded at 256 binders", node)
        parameter = _Parameter(len(self.parameters), name, _span(node), domain, allowance)
        self.parameters.append(parameter)
        scope[name] = parameter
        return parameter

    def _telescope(self, node: Node, scope: dict[str, _Parameter]) -> list[_Parameter]:
        return [self._parameter(parameter, scope) for parameter in cast("list[Node]", node["parameters"])]

    def _index(self, node: Node, scope: dict[str, _Parameter]) -> str:
        kind = node["kind"]
        if kind == "group":
            return self._index(cast("Node", node["value"]), scope)
        if kind == "nat":
            return f"(IndexLit {self._literal(node)})"
        if kind == "name" or (kind == "type" and not node["arguments"]):
            name = _name(node["name"])
            if name in scope:
                return f"(IndexVar {scope[name].index})"
            raise self.protocol.error("grade", f"unbound index '{name}'", node)
        if kind == "binary" and _name(node["operator"]) == "+":
            lhs = self._index(cast("Node", node["left"]), scope)
            rhs = self._index(cast("Node", node["right"]), scope)
            return f"(IndexAdd {lhs} {rhs})"
        raise self.protocol.error("unsupported", "expected a natural index formed from names, literals or addition", node)

    def _type(self, node: Node, scope: dict[str, _Parameter]) -> str:
        if node["kind"] in {"type_argument", "group_type"}:
            return self._type(cast("Node", node["type"]), scope)
        if node["kind"] == "type":
            name = _name(node["name"])
            arguments = cast("list[Node]", node["arguments"])
            if name == "Nat" and not arguments:
                return "Natural"
            if name == "Type":
                if not arguments:
                    return "(Universe 0)"
                if len(arguments) == 1 and arguments[0]["kind"] == "nat" and not arguments[0]["suffix"]:
                    spelling = cast("str", arguments[0]["value"]).replace("_", "")
                    if spelling.isdecimal():
                        level = int(spelling)
                        if level > 8:
                            raise self.protocol.error("limit", "graded universe levels are bounded at 8", arguments[0])
                        return f"(Universe {level})"
                raise self.protocol.error("unsupported", "graded Type<n> requires a natural literal level", node)
            if name == "Vec" and len(arguments) == 2 and self._type(arguments[0], scope) == "Natural":
                return f"(Vector {self._index(arguments[1], scope)})"
            if not arguments and name in scope:
                parameter = scope[name]
                if parameter.domain.startswith("(Universe "):
                    return f"(TypeVar {parameter.index})"
                raise self.protocol.error("grade", f"value binder '{name}' is not a type", node)
        if (node["kind"] == "function_type" and node["mode"] == "Fn" and node["parameters"]
                and not any(node[field] for field in ("generics", "captures", "effects", "contracts"))):
            extended = scope.copy()
            parameters = self._telescope(node, extended)
            codomain = self._type(cast("Node", node["result"]), extended)
            for parameter in reversed(parameters):
                codomain = parameter.abstract("Pi", codomain)
            return codomain
        raise self.protocol.error(
            "unsupported",
            "graded replay supports Nat, Type, Type<n>, type variables, Vec<Nat, n> and pure Fn types",
            node,
        )

    def _application(self, callee: str, node: Node, scope: dict[str, _Parameter], declaration: Node) -> str:
        if node["kind"] == "group":
            return self._application(callee, cast("Node", node["value"]), scope, declaration)
        if node["kind"] == "type_expression":
            return f"(ApplyType {callee} {self._type(cast('Node', node['type']), scope)})"
        if node["kind"] == "name":
            parameter = scope.get(_name(node["name"]))
            if parameter is not None and parameter.domain.startswith("(Universe "):
                return f"(ApplyType {callee} (TypeVar {parameter.index}))"
            is_index = parameter is not None and parameter.domain == "Natural"
        else:
            is_index = node["kind"] in {"nat", "binary"}
        if is_index:
            return f"(ApplyNat {callee} {self._index(node, scope)})"
        return f"(ApplyValue {callee} {self._term(node, scope, declaration)})"

    def _imported_definition(self, name: str, node: Node) -> _Definition | None:
        resolved = self.resolve_import(name) if self.resolve_import is not None else None
        if resolved is None:
            return None
        identity, provider = resolved
        if provider.domain != self.domain:
            raise self.protocol.error("grade", f"imported '{name}' requires the {provider.domain} grade domain", node)
        self.imports[name] = resolved
        module = id(provider.syntax)
        if module not in self.providers:
            projection = _Projection(provider.protocol, provider.syntax, self.domain)
            projection.parameters = self.parameters
            projection.definitions = self.definitions
            projection.providers = self.providers
            projection.provider_receipts = self.provider_receipts
            self.providers[module] = projection
        projection = self.providers[module]
        projection.resolve_import = provider.imports.get
        definition = projection.definition(provider.name)
        self.provider_receipts.add((identity, provider.receipt))
        return definition

    def _reference(self, node: Node, scope: dict[str, _Parameter], declaration: Node,
                   *, nullary: bool = False) -> str | None:
        name = _IntrinsicsMixin._dotted_member_path(node)
        if name is None or name.split(".", 1)[0] in scope:
            return None
        if name in self.declarations:
            local = self.declarations[name]
            if local["kind"] != "definition" or _span(local)[0] >= _span(declaration)[0]:
                return None
            definition = self.definition(name)
        else:
            definition = self._imported_definition(name, node)
        if definition is None:
            return None
        if bool(definition.source["parameters"]) == nullary:
            message = ("graded nullary calls require a zero-parameter definition" if nullary
                       else "graded zero-parameter definitions require a nullary call")
            raise self.protocol.error("unsupported", message, node)
        return f"source_term_{definition.index}"

    def _term(self, node: Node, scope: dict[str, _Parameter], declaration: Node) -> str:
        kind = node["kind"]
        if kind == "group":
            return self._term(cast("Node", node["value"]), scope, declaration)
        if kind == "let_expression":
            binding = cast("Node", node["binding"])
            annotation = cast("Node | None", binding.get("type"))
            if binding["kind"] != "let" or (annotation is not None and not _plain_type(annotation, "Nat")):
                raise self.protocol.error("unsupported", "graded let requires a natural name binding", binding)
            initializer = self._index(cast("Node", binding["value"]), scope)
            extended = scope.copy()
            parameter = self._bind(binding, extended, "Natural", self._grade(binding))
            body = self._term(cast("Node", node["body"]), extended, declaration)
            return f"(LetNat {parameter.index} {parameter.allowance} {initializer} {body})"
        if kind in {"name", "member"}:
            if kind == "name" and (name := _name(node["name"])) in scope:
                return f"(Var {scope[name].index})"
            if (reference := self._reference(node, scope, declaration)) is not None:
                return reference
            path = _IntrinsicsMixin._dotted_member_path(node) or _name(node["name"])
            raise self.protocol.error("grade", f"unbound value '{path}'", node)
        if kind == "lambda" and node["parameters"]:
            extended = scope.copy()
            parameters = self._telescope(node, extended)
            body = self._term(cast("Node", node["body"]), extended, declaration)
            for parameter in reversed(parameters):
                body = parameter.abstract("Lambda", body)
            return body
        if kind == "call":
            callee = cast("Node", node["callee"])
            while callee["kind"] == "group":
                callee = cast("Node", callee["value"])
            arguments = cast("list[Node]", node["arguments"])
            if any(argument["label"] is not None for argument in arguments):
                raise self.protocol.error("unsupported", "graded replay requires positional arguments or an earlier nullary definition", node)
            if not arguments:
                result = self._reference(callee, scope, declaration, nullary=True)
                if result is None:
                    raise self.protocol.error("unsupported", "graded replay requires an earlier or imported nullary definition", node)
                return result
            result = self._term(callee, scope, declaration)
            for argument in arguments:
                result = self._application(result, cast("Node", argument["value"]), scope, declaration)
            return result
        return f"(NatValue {self._index(node, scope)})"

    def _definition_node(self, name: str) -> Node:
        node = self.declarations.get(name)
        if node is None or node["kind"] != "definition":
            raise self.protocol.error("grade", f"graded definition '{name}' was not found", node)
        if node["generics"] or node["contracts"] or node["modifiers"] not in ([], ["public"]):
            raise self.protocol.error("unsupported", "graded replay requires a plain mathematical definition", node)
        return node

    def definition(self, name: str) -> _Definition:
        if name in self.completed:
            return self.completed[name]
        node = self._definition_node(name)
        scope: dict[str, _Parameter] = {}
        parameters = self._telescope(node, scope)
        expected = self._type(cast("Node", node["result"]), scope)
        term = self._term(cast("Node", node["value"]), scope, node)
        for parameter in reversed(parameters):
            term = parameter.abstract("Lambda", term)
            expected = parameter.abstract("Pi", expected)
        result = _Definition(len(self.definitions), name, node, term, expected)
        self.completed[name] = result
        self.definitions.append(result)
        return result


def _plain_type(node: Node | None, name: str) -> bool:
    return node is not None and node["kind"] == "type" and _name(node["name"]) == name and not node["arguments"]


def _valid_box_record(node: Node, domain: GradeDomain) -> bool:
    if (node["kind"] != "record" or node["contracts"] or node["declarations"]
            or node["modifiers"] not in ([], ["public"])):
        return False
    generics = cast("list[Node]", node["generics"])
    fields = cast("list[Node]", node["parameters"])
    if len(generics) != 2 or len(fields) != 1:
        return False
    element, grade = generics
    [field] = fields
    element_name, grade_name = _name(element["name"]), _name(grade["name"])
    annotation = cast("Node | None", field["grade"])
    return (element["mode"] == "type" and element["type"] is None and grade["mode"] == "grade"
            and element_name != grade_name and not {element_name, grade_name} & (_PRIMITIVES | {"Box", "_"})
            and _plain_type(cast("Node | None", grade["type"]), domain)
            and field["name"] is not None and _name(field["name"]) == "Value"
            and not field.get("const") and not field.get("label")
            and _plain_type(cast("Node", field["type"]), element_name)
            and annotation is not None and annotation["kind"] == "name" and _name(annotation["name"]) == grade_name)


@dataclass(frozen=True)
class _IndexedRecord:
    identity: int
    length_field: str
    extent: str

    @property
    def shape(self) -> str:
        return f"{{| record_id := {self.identity}; payload_extent := {self.extent} |}}"


class _ModalProjection(_Projection):
    reserved = _PRIMITIVES | {"Box"}

    def __init__(self, protocol: _Protocol, syntax: Node, domain: GradeDomain, *,
                 resolve_box: BoxResolver | None = None) -> None:
        super().__init__(protocol, syntax, domain)
        self.resolve_box = resolve_box
        self.box_imports: dict[str, GradeDomain] = {}
        self.local_box = _local_box(protocol, cast("list[Node]", syntax["declarations"]))
        self.records: set[str] = set()
        self.record_ids = {name: index for index, (name, node) in enumerate(self.declarations.items())
                           if node["kind"] == "record" and name != "Box"}
        self.indexed_records: dict[str, _IndexedRecord] = {}
        self.indexed_bindings: dict[int, _IndexedRecord] = {}

    def _is_box_name(self, name: str | None) -> bool:
        if name is None:
            return False
        if name == "Box" and "Box" in self.declarations:
            return self.local_box is not None
        return self.resolve_box is not None and self.resolve_box(name) is not None

    def _box_record(self, node: Node, box_name: str = "Box") -> None:
        expected = f"Box<T, grade q : {self.domain}>(T Value @ q)"
        if box_name == "Box" and "Box" in self.declarations:
            record = self.declarations["Box"]
            if _span(record)[0] >= _span(node)[0]:
                raise self.protocol.error("unsupported", f"modal replay requires an earlier record {expected}", node)
            if not _valid_box_record(record, self.domain):
                raise self.protocol.error("unsupported", f"modal replay requires record {expected}", record)
            self.records.add("Box")
            return
        if self.resolve_box is not None and (imported_domain := self.resolve_box(box_name)) is not None:
            if imported_domain != self.domain:
                raise self.protocol.error("grade", f"imported '{box_name}' requires the {imported_domain} grade domain", node)
            self.box_imports[box_name] = imported_domain
            self.records.add("Box")
            return
        raise self.protocol.error("unsupported", f"modal replay requires an earlier record {expected}", node)

    @override
    def _imported_definition(self, name: str, node: Node) -> _Definition | None:
        resolved = self.resolve_import(name) if self.resolve_import is not None else None
        if resolved is None:
            return None
        identity, provider = resolved
        if provider.domain != self.domain:
            raise self.protocol.error("grade", f"imported '{name}' requires the {provider.domain} grade domain", node)
        self.imports[name] = resolved
        module = id(provider.syntax)
        if module not in self.providers:
            projection = _ModalProjection(provider.protocol, provider.syntax, self.domain,
                                          resolve_box=provider.box_imports.get)
            projection.parameters = self.parameters
            projection.definitions = self.definitions
            projection.providers = self.providers
            projection.provider_receipts = self.provider_receipts
            self.providers[module] = projection
        projection = cast("_ModalProjection", self.providers[module])
        projection.resolve_import = provider.imports.get
        definition = projection.definition(provider.name, closed=True)
        self.provider_receipts.add((identity, provider.receipt))
        return definition

    @override
    def _reference(self, node: Node, scope: dict[str, _Parameter], declaration: Node,
                   *, nullary: bool = False) -> str | None:
        name = _IntrinsicsMixin._dotted_member_path(node)
        if name is None or name.split(".", 1)[0] in scope:
            return None
        if name in self.declarations:
            local = self.declarations[name]
            if local["kind"] != "definition" or _span(local)[0] >= _span(declaration)[0]:
                return None
            definition = self.definition(name, closed=True)
        else:
            definition = self._imported_definition(name, node)
        if definition is None:
            return None
        if bool(definition.source["parameters"]) == nullary:
            message = ("graded nullary calls require a zero-parameter definition" if nullary
                       else "graded zero-parameter definitions require a nullary call")
            raise self.protocol.error("unsupported", message, node)
        return f"source_term_{definition.index}"

    def _extent(self, node: Node, field: str) -> str:
        kind = node["kind"]
        if kind == "group":
            return self._extent(cast("Node", node["value"]), field)
        if kind == "nat":
            return f"(ExtentLiteral {self._literal(node)})"
        if (kind == "name" or (kind == "type" and not node["arguments"])) and _name(node["name"]) == field:
            return "ExtentField"
        if kind == "binary" and _name(node["operator"]) == "+":
            left = self._extent(cast("Node", node["left"]), field)
            right = self._extent(cast("Node", node["right"]), field)
            return f"(ExtentAdd {left} {right})"
        raise self.protocol.error("unsupported", f"indexed record extent may use '{field}', natural literals and addition", node)

    def _indexed_record(self, name: str, node: Node) -> _IndexedRecord:
        record = self.declarations.get(name)
        if record is None or name not in self.record_ids or _span(record)[0] >= _span(node)[0]:
            raise self.protocol.error("unsupported", f"modal replay requires an earlier indexed record '{name}'", node)
        if name in self.indexed_records:
            return self.indexed_records[name]
        error = "indexed records require a plain Nat field followed by a Vec<Nat, extent> field"
        fields = cast("list[Node]", record["parameters"])
        if (record["generics"] or record["contracts"] or record["declarations"]
                or record["modifiers"] not in ([], ["public"]) or len(fields) != 2
                or any(field["name"] is None or field.get("const") or field.get("label") or field["grade"]
                       for field in fields)):
            raise self.protocol.error("unsupported", error, record)
        length, payload = fields
        first, second = _name(length["name"]), _name(payload["name"])
        vector = cast("Node", payload["type"])
        if (first == second or "_" in {first, second} or not _plain_type(cast("Node", length["type"]), "Nat")
                or vector["kind"] != "type" or _name(vector["name"]) != "Vec"):
            raise self.protocol.error("unsupported", error, record)
        arguments = cast("list[Node]", vector["arguments"])
        if len(arguments) != 2 or not _plain_type(arguments[0], "Nat"):
            raise self.protocol.error("unsupported", error, vector)
        result = _IndexedRecord(self.record_ids[name], first, self._extent(arguments[1], first))
        self.indexed_records[name] = result
        self.records.add(name)
        return result

    @override
    def _parameter(self, node: Node, scope: dict[str, _Parameter]) -> _Parameter:
        parameter = super()._parameter(node, scope)
        annotation = cast("Node", node["type"])
        while annotation["kind"] in {"type_argument", "group_type"}:
            annotation = cast("Node", annotation["type"])
        if annotation["kind"] == "type" and (name := _name(annotation["name"])) in self.record_ids:
            self.indexed_bindings[parameter.index] = self.indexed_records[name]
        return parameter

    def _box_grade(self, arguments: list[Node], node: Node, box_name: str = "Box") -> int:
        if len(arguments) == 2 and _plain_type(arguments[0], "Nat"):
            self._box_record(node, box_name)
            return self._literal(arguments[1])
        raise self.protocol.error("unsupported", "modal replay requires Box<Nat, q> with a natural literal q", node)

    def _promote(self, node: Node, scope: dict[str, _Parameter]) -> tuple[int, str]:
        if node["kind"] == "call":
            callee = cast("Node", node["callee"])
            arguments = cast("list[Node]", node["arguments"])
            if callee["kind"] == "generic_application" and len(arguments) == 1 and arguments[0]["label"] is None:
                head = cast("Node", callee["value"])
                box_name = _IntrinsicsMixin._dotted_member_path(head)
                if self._is_box_name(box_name) and box_name is not None:
                    grade = self._box_grade(cast("list[Node]", callee["arguments"]), callee, box_name)
                    return grade, self._index(cast("Node", arguments[0]["value"]), scope)
        raise self.protocol.error("unsupported", "modal replay promotes a natural index with Box<Nat, q>(value)", node)

    def _boxed(self, node: Node, scope: dict[str, _Parameter]) -> str | None:
        if node["kind"] == "group":
            return self._boxed(cast("Node", node["value"]), scope)
        if node["kind"] == "name" and _name(node["name"]) in scope:
            return f"(BoxName {scope[_name(node['name'])].index})"
        if node["kind"] == "call":
            callee = cast("Node", node["callee"])
            if (callee["kind"] == "generic_application"
                    and self._is_box_name(_IntrinsicsMixin._dotted_member_path(cast("Node", callee["value"])))):
                grade, index = self._promote(node, scope)
                return f"(PromoteNat {grade} {index})"
        return None

    def _indexed(self, node: Node, scope: dict[str, _Parameter]) -> tuple[str, _IndexedRecord] | None:
        if node["kind"] == "group":
            return self._indexed(cast("Node", node["value"]), scope)
        if (node["kind"] == "name" and (binding := scope.get(_name(node["name"]))) is not None
                and (record := self.indexed_bindings.get(binding.index)) is not None):
            return f"(IndexedName {binding.index})", record
        if node["kind"] == "call":
            callee = cast("Node", node["callee"])
            if callee["kind"] == "name" and (name := _name(callee["name"])) in self.record_ids and name not in scope:
                record = self._indexed_record(name, callee)
                arguments = cast("list[Node]", node["arguments"])
                if len(arguments) == 2 and all(argument["label"] is None for argument in arguments):
                    length, payload = [cast("Node", argument["value"]) for argument in arguments]
                    if payload["kind"] == "name" and (binding := scope.get(_name(payload["name"]))) is not None:
                        return f"(BuildIndexed {record.shape} {self._index(length, scope)} {binding.index})", record
                raise self.protocol.error("unsupported", "indexed constructors require a natural index and a named vector", node)
        return None

    def _type_index(self, node: Node, scope: dict[str, _Parameter]) -> str:
        if node["kind"] == "group":
            return self._type_index(cast("Node", node["value"]), scope)
        if node["kind"] == "member":
            field = _name(node["name"])
            subject = cast("Node", node["value"])
            if (indexed := self._indexed(subject, scope)) is not None:
                value, record = indexed
                if field != record.length_field:
                    raise self.protocol.error("grade", f"'{field}' is not the indexed record's natural field", node)
                return f"(IndexedLength {record.shape} {value})"
            if field == "Value":
                if subject["kind"] == "name" and _name(subject["name"]) in scope:
                    return f"(BoxContents {scope[_name(subject['name'])].index})"
                grade, index = self._promote(subject, scope)
                return f"(PromotedContents {grade} {index})"
        return f"(PlainIndex {self._index(node, scope)})"

    @override
    def _type(self, node: Node, scope: dict[str, _Parameter]) -> str:
        kind = node["kind"]
        if kind in {"type_argument", "group_type"}:
            return self._type(cast("Node", node["type"]), scope)
        if kind == "type":
            name = _name(node["name"])
            arguments = cast("list[Node]", node["arguments"])
            if name == "Nat" and not arguments:
                return "NatKind"
            if self._is_box_name(name):
                return f"(BoxNat {self._box_grade(arguments, node, name)})"
            if name in self.record_ids and not arguments:
                return f"(IndexedKind {self._indexed_record(name, node).shape})"
            if name == "Vec" and len(arguments) == 2 and _plain_type(arguments[0], "Nat"):
                return f"(VecKind {self._type_index(arguments[1], scope)})"
        if (kind == "function_type" and node["mode"] == "Fn" and node["parameters"]
                and not any(node[field] for field in ("generics", "captures", "effects", "contracts"))):
            extended = scope.copy()
            parameters = self._telescope(node, extended)
            codomain = self._type(cast("Node", node["result"]), extended)
            for parameter in reversed(parameters):
                codomain = f"(ArrowKind {parameter.allowance} {parameter.domain} {codomain})"
            return codomain
        if kind == "tuple_type" and len(types := cast("list[Node]", node["types"])) == 2:
            return f"(ProductKind {self._type(types[0], scope)} {self._type(types[1], scope)})"
        raise self.protocol.error("unsupported", "modal replay supports Nat, Box<Nat, q>, indexed records, Vec<Nat, n>, pairs and pure Fn types", node)

    def _match(self, node: Node, scope: dict[str, _Parameter], declaration: Node) -> str:
        motive = cast("Node | None", node["motive"])
        cases = cast("list[Node]", node["cases"])
        if motive is None or len(cases) != 1:
            raise self.protocol.error("unsupported", "modal replay requires an explicit motive and one record arm", node)
        [case] = cases
        pattern = cast("Node", case["pattern"])
        if pattern["kind"] != "constructor_pattern":
            raise self.protocol.error("unsupported", "modal replay requires a Box or indexed record binder pattern", pattern)
        name = _name(pattern["name"])
        is_box = self._is_box_name(name)
        record = None if is_box else self._indexed_record(name, pattern)
        if is_box:
            self._box_record(pattern, name)
        arguments = cast("list[Node]", pattern["arguments"])
        if len(arguments) != (1 if is_box else 2) or any(arg["kind"] != "binding_pattern" for arg in arguments):
            raise self.protocol.error("unsupported", f"modal replay requires named {name} fields", pattern)
        subject = cast("Node", node["value"])
        motive_scope = scope.copy()
        motive_parameter = self._bind(motive, motive_scope, "", 0)
        if record is not None:
            self.indexed_bindings[motive_parameter.index] = record
        motive_type = self._type(cast("Node", motive["type"]), motive_scope)
        extended = scope.copy()
        first = self._bind(arguments[0], extended, "NatKind", 0)
        body = cast("Node", case["value"])
        if record is None:
            boxed = self._boxed(subject, scope)
            if boxed is not None:
                return f"(LetBox {first.index} {motive_parameter.index} {boxed} {motive_type} {self._term(body, extended, declaration)})"
            subject_term = self._term(subject, scope, declaration)
            return f"(LetBoxValue {first.index} {motive_parameter.index} {subject_term} {motive_type} {self._term(body, extended, declaration)})"
        payload = self._bind(arguments[1], extended, f"(payload_kind {record.shape} (IndexVar {first.index}))", 0)
        indexed = self._indexed(subject, scope)
        if indexed is None:
            raise self.protocol.error("unsupported", "modal replay matches a named or constructed indexed record", subject)
        return (f"(LetIndexed {record.shape} {first.index} {payload.index} {motive_parameter.index} {indexed[0]} {motive_type} "
                f"{self._term(body, extended, declaration)})")

    @override
    def _term(self, node: Node, scope: dict[str, _Parameter], declaration: Node) -> str:
        kind = node["kind"]
        if kind == "group":
            return self._term(cast("Node", node["value"]), scope, declaration)
        if kind in {"name", "member"}:
            if kind == "name" and (name := _name(node["name"])) in scope:
                return f"(Name {scope[name].index})"
            if (reference := self._reference(node, scope, declaration)) is not None:
                return reference
            path = _IntrinsicsMixin._dotted_member_path(node) or _name(node["name"])
            raise self.protocol.error("grade", f"unbound value '{path}'", node)
        if kind == "lambda" and node["parameters"]:
            extended = scope.copy()
            parameters = self._telescope(node, extended)
            body = self._term(cast("Node", node["body"]), extended, declaration)
            for parameter in reversed(parameters):
                body = parameter.abstract("Lambda", body)
            return body
        if kind == "tuple" and len(values := cast("list[Node]", node["values"])) == 2:
            return f"(Pair {self._term(values[0], scope, declaration)} {self._term(values[1], scope, declaration)})"
        if kind == "match_expression":
            return self._match(node, scope, declaration)
        if kind == "call":
            if (indexed := self._indexed(node, scope)) is not None:
                value, record = indexed
                return f"(IndexedValue {record.shape} {value})"
            if (boxed := self._boxed(node, scope)) is not None:
                return f"(BoxValue {boxed})"
            callee = cast("Node", node["callee"])
            while callee["kind"] == "group":
                callee = cast("Node", callee["value"])
            arguments = cast("list[Node]", node["arguments"])
            if any(argument["label"] is not None for argument in arguments):
                raise self.protocol.error("unsupported", "modal replay requires positional arguments or an earlier nullary definition", node)
            if not arguments:
                result = self._reference(callee, scope, declaration, nullary=True)
                if result is None:
                    raise self.protocol.error("unsupported", "modal replay requires an earlier or imported nullary definition", node)
                return result
            result = self._term(callee, scope, declaration)
            for argument in arguments:
                result = f"(Apply {result} {self._term(cast('Node', argument['value']), scope, declaration)})"
            return result
        return f"(NaturalValue {self._index(node, scope)})"

    @override
    def definition(self, name: str, *, closed: bool = False) -> _Definition:
        if name in self.completed:
            return self.completed[name]
        node = self._definition_node(name)
        scope: dict[str, _Parameter] = {}
        parameters = self._telescope(node, scope)
        expected = self._type(cast("Node", node["result"]), scope)
        term = self._term(cast("Node", node["value"]), scope, node)
        if closed:
            if any(f"(IndexVar {p.index})" in expected or f"(BoxContents {p.index})" in expected
                   or f"(IndexedName {p.index})" in expected for p in parameters):
                raise self.protocol.error("unsupported", "called modal definitions require non-dependent result kinds", node)
            for parameter in reversed(parameters):
                term = parameter.abstract("Lambda", term)
                expected = f"(ArrowKind {parameter.allowance} {parameter.domain} {expected})"
            context = "[]"
        else:
            context_rows = "; ".join(
                f"{{| name := {parameter.index}; domain := {parameter.domain}; allowance := {parameter.allowance} |}}"
                for parameter in reversed(parameters)
            )
            context = f"[{context_rows}]"
        result = _Definition(len(self.definitions), name, node, term, expected, context, tuple(sorted(self.records)))
        self.completed[name] = result
        self.definitions.append(result)
        return result


def _certificate(definitions: list[_Definition], source_hash: str, domain: GradeDomain,
                 provider_receipts: set[tuple[str, str]] | None = None) -> str:
    modal = definitions[-1].context is not None
    files = _MODAL_FILES if modal else _ROCQ_FILES
    modules = "GradedPure GradedModal GradedModalSource" if modal else "GradedPure GradedSource"
    check_name = "bounded_source_check" if domain == GradeDomain.BOUND else "source_check"
    lines = [
        f"(* Source SHA-256 {source_hash} *)",
        *(f"(* Graded provider {identity} receipt SHA-256 {receipt} *)"
          for identity, receipt in sorted(provider_receipts or ())),
        "From Stdlib Require Import Lists.List.",
        f"Require Import {' '.join(Path(name).stem for name in files)}.",
        f"Import ListNotations {modules}.",
    ]
    reports = []
    for definition in definitions:
        number = definition.index
        if definition.context is not None:
            lines.append(f"Definition source_context_{number} : list parameter := {definition.context}.")
            lines.append(f"Definition source_term_{number} : value := {definition.term}.")
            lines.append(f"Definition source_type_{number} : kind := {definition.expected}.")
            reports.append(f"{check_name} source_context_{number} source_term_{number} source_type_{number}")
        else:
            lines.append(f"Definition source_term_{number} : term := {definition.term}.")
            lines.append(f"Definition source_type_{number} : ty := {definition.expected}.")
            reports.append(f"{check_name} source_term_{number} source_type_{number}")
    lines.extend([
        f"Definition source_reports := [{'; '.join(reports)}].",
        "Set Printing Width 100000.",
        "Set Printing Depth 100000.",
        "Eval vm_compute in source_reports.",
        "Example source_replays : forallb accepted source_reports = true.",
        "Proof. vm_compute. reflexivity. Qed.",
    ])
    return "\n".join(lines) + "\n"


def _run_rocq(compiler: list[str], directory: Path, unit: str) -> subprocess.CompletedProcess[str]:
    command = [*compiler, "-q", unit]
    deadline = REPLAY_DEADLINE.get()
    budget = 30.0 if deadline is None else min(30.0, deadline - time.monotonic())
    if budget <= 0:
        raise subprocess.TimeoutExpired(command, 0)
    return subprocess.run(command, cwd=directory, capture_output=True,
                          text=True, encoding="utf-8", check=False, timeout=budget)


def _verdict(projection: _Projection, replay: subprocess.CompletedProcess[str]) -> list[list[list[int]]]:
    match = _REPORT.search(replay.stdout)
    if match is None:
        raise RuntimeError(f"graded source replay gave no verdict: {replay.stderr.strip()}")
    rows = cast("list[list[list[int]]]", json.loads(match[1].replace(";", ",")))
    for definition, row in zip(projection.definitions, rows, strict=True):
        if row == [[0]]:
            order = "bounded" if projection.domain == GradeDomain.BOUND else "exact"
            motive = ", modal motive specialization" if definition.context is not None else ""
            problem = f"term fails {order} computation demand{motive} or natural-index checking"
            raise projection.protocol.error("grade", problem, definition.source)
        if row == [[1]]:
            raise projection.protocol.error("grade", "inferred graded type differs from the declared dependent type", definition.source)
        if len(row) < 2 or row[0] != [2]:
            raise RuntimeError("invalid Rocq grade report")
    if replay.returncode:
        raise RuntimeError(f"graded source certificate failed: {replay.stderr.strip()}")
    return rows


def _compile_support(compiler: list[str], directory: Path, sources: dict[str, bytes]) -> None:
    for name, source in sources.items():
        (directory / name).write_bytes(source)
        compiled = _run_rocq(compiler, directory, name)
        if compiled.returncode:
            raise RuntimeError(f"graded Rocq support failed: {compiled.stderr.strip()}")


def _support_cache_root() -> Path | None:
    cache = proofenv.build_root() / "rocq-support-cache"
    kind = proofenv.filesystem(cache)
    if not kind or kind in proofenv.CROSS_OS_FILESYSTEMS | proofenv.VOLATILE_FILESYSTEMS:
        return None
    return cache


def _compiler_sha256(compiler: list[str]) -> str | None:
    executable = shutil.which(compiler[0])
    if executable is None:
        return None
    path = Path(executable)
    if not path.is_file():
        return None
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def _support_cache_hit(entry: Path, key: str, files: tuple[str, ...], sources: dict[str, bytes]) -> bool:
    receipt_path = entry / "receipt.json"
    if not receipt_path.is_file():
        return False
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, ValueError):
        return False
    if not isinstance(receipt, dict) or receipt.get("key") != key:
        return False
    vo_digests = receipt.get("vo_sha256")
    if not isinstance(vo_digests, dict):
        return False
    expected_vo = {f"{Path(name).stem}.vo" for name in files}
    if set(vo_digests) != expected_vo:
        return False
    for name in files:
        source_file = entry / name
        vo_name = f"{Path(name).stem}.vo"
        vo_file = entry / vo_name
        if not source_file.is_file() or not vo_file.is_file():
            return False
        if source_file.read_bytes() != sources[name]:
            return False
        if hashlib.sha256(vo_file.read_bytes()).hexdigest() != vo_digests[vo_name]:
            return False
    return True


def _copy_support_artifacts(source_dir: Path, target_dir: Path, files: tuple[str, ...]) -> None:
    for name in files:
        stem = Path(name).stem
        for artifact in (name, f"{stem}.vo", f"{stem}.vos", f"{stem}.glob"):
            src = source_dir / artifact
            if src.is_file():
                shutil.copyfile(src, target_dir / artifact)


def _support(root: Path, compiler: list[str], directory: Path, files: tuple[str, ...]) -> dict[str, str]:
    sources = {name: (root / "tools" / "rocq" / name).read_bytes() for name in files}
    hashes = {name: hashlib.sha256(source).hexdigest() for name, source in sources.items()}
    if not files:
        return hashes
    cache_root = _support_cache_root()
    compiler_digest = _compiler_sha256(compiler) if cache_root is not None else None
    if cache_root is None or compiler_digest is None:
        _compile_support(compiler, directory, sources)
        return hashes
    cache_root.mkdir(parents=True, exist_ok=True)
    identity = json.dumps({
        "compiler_sha256": compiler_digest,
        "compiler_args": compiler[1:],
        "files": [[name, hashes[name]] for name in files],
    }, separators=(",", ":"))
    key = hashlib.sha256(identity.encode("utf-8")).hexdigest()
    entry = cache_root / key
    with FileLock(cache_root / f"{key}.lock", timeout=120):
        if not _support_cache_hit(entry, key, files, sources):
            shutil.rmtree(entry, ignore_errors=True)
            stage = Path(tempfile.mkdtemp(prefix=f"stage-{key}-", dir=cache_root))
            try:
                _compile_support(compiler, stage, sources)
                vo_digests = {
                    f"{Path(name).stem}.vo": hashlib.sha256((stage / f"{Path(name).stem}.vo").read_bytes()).hexdigest()
                    for name in files
                }
                (stage / "receipt.json").write_text(
                    json.dumps({"key": key, "vo_sha256": vo_digests}, sort_keys=True),
                    encoding="utf-8",
                    newline="\n",
                )
                stage.replace(entry)
            except BaseException:
                shutil.rmtree(stage, ignore_errors=True)
                raise
        _copy_support_artifacts(entry, directory, files)
    return hashes


def _replay(compiler: list[str], directory: Path, projection: _Projection,
            certificate: str) -> tuple[list[list[int]], str]:
    (directory / "SourceReplay.v").write_text(certificate, encoding="utf-8", newline="\n")
    rows = _verdict(projection, _run_rocq(compiler, directory, "SourceReplay.v"))
    expected = json.dumps(rows).replace(",", ";")
    pinned_rows = (f"Example source_rows_match : source_reports = {expected}.\n"
                   "Proof. vm_compute. reflexivity. Qed.\n")
    report = directory / "SourceReport.v"
    report.write_text("From Stdlib Require Import Lists.List.\nRequire Import SourceReplay.\n"
                      "Import ListNotations.\n" + pinned_rows, encoding="utf-8", newline="\n")
    verified = _run_rocq(compiler, directory, report.name)
    if verified.returncode:
        raise RuntimeError(f"graded demand certificate failed: {verified.stderr.strip()}")
    return rows[-1], certificate + pinned_rows


def _dependency_row(parameters: list[_Parameter], counts: list[int]) -> list[dict[str, object]]:
    return [{"name": parameters[index].name, "span": parameters[index].span, "uses": uses}
            for index, uses in batched(counts, 2, strict=True)]


def _domain(protocol: _Protocol, parameter: Node) -> GradeDomain:
    annotation = cast("Node", parameter["grade"])
    if annotation["kind"] == "call":
        callee = cast("Node", annotation["callee"])
        if callee["kind"] == "name" and (name := _name(callee["name"])) in GradeDomain:
            return GradeDomain(name)
    raise protocol.error("unsupported", "graded checking requires a NatExact(n) or NatBound(n) allowance", annotation)


def _local_box(protocol: _Protocol, declarations: list[Node]) -> tuple[Node, GradeDomain] | None:
    for declaration in declarations:
        if declaration["kind"] != "record" or _name(declaration["name"]) != "Box":
            continue
        generics = cast("list[Node]", declaration["generics"])
        if not any(node["mode"] == "grade" for node in generics):
            continue
        for domain in GradeDomain:
            if _valid_box_record(declaration, domain):
                return declaration, domain
        raise protocol.error("unsupported", "graded Box requires a canonical declaration", declaration)
    return None


class ModuleReplay:
    """Replay each declaration in its resolved import context."""

    def __init__(self, root: Path, protocol: _Protocol, syntax: Node, stack: ExitStack,
                 *, resolve_box: BoxResolver | None = None) -> None:
        self.root = root
        self.protocol = protocol
        self.syntax = syntax
        self.stack = stack
        self.resolve_box = resolve_box
        declarations = cast("list[Node]", syntax["declarations"])
        self.record_names = {_name(node["name"]) for node in declarations if node["kind"] == "record"}
        box_info = _local_box(protocol, declarations)
        self.box = None if box_info is None else box_info[0]
        self.box_domain = None if box_info is None else box_info[1]
        self.compiler: list[str] = []
        self.directory: Path | None = None
        self.hashes: dict[str, str] = {}
        self.receipts: list[str] = []
        self.exports: dict[str, GradeExport] = {}
        self.modal_definitions: set[str] = set()

    def _lookup_box_domain(self, name: str | None) -> GradeDomain | None:
        if name is None:
            return None
        if name == "Box" and self.box_domain is not None:
            return self.box_domain
        if self.resolve_box is not None:
            return self.resolve_box(name)
        return None

    def check(self, declaration: Node, resolve_import: GradeResolver) -> tuple[set[int], str | None]:
        protocol = self.protocol
        if declaration is self.box:
            return ({id(cast("list[Node]", declaration["generics"])[1]),
                     id(cast("list[Node]", declaration["parameters"])[0])}, None)
        modal = False
        annotations: list[Node] = []
        box_uses: list[Node] = []
        signature = (
            [*cast("list[Node]", declaration["parameters"]), cast("Node", declaration["result"])]
            if declaration["kind"] == "definition" else []
        )
        interface_nodes = {id(node) for part in signature for node in syntax_nodes(part)}
        box_interface = False
        for node in syntax_nodes(declaration):
            if node["kind"] == "generic_parameter" and node["mode"] == "grade":
                raise protocol.error("unsupported", "grade generics require a qualified representation", node)
            if node.get("grade") is not None:
                annotations.append(node)
            if node["kind"] in {"type", "name", "member", "constructor_pattern"}:
                path = _IntrinsicsMixin._dotted_member_path(node) or (
                    _name(node["name"]) if isinstance(node.get("name"), dict) else None
                )
                if path is not None:
                    if self._lookup_box_domain(path) is not None:
                        box_uses.append(node)
                        modal = True
                        if id(node) in interface_nodes:
                            box_interface = True
                    elif (path in self.modal_definitions
                          or ((imported := resolve_import(path)) is not None and imported[1].modal)):
                        modal = True
            if (node["kind"] in {"match_expression", "tuple", "tuple_type"}
                    or (node["kind"] == "type" and _name(node["name"]) in self.record_names)):
                modal = True
        if not annotations:
            if box_uses:
                raise protocol.error("unsupported", "graded Box operations require an annotated pure definition", box_uses[0])
            return set(), None
        if declaration["kind"] != "definition":
            raise protocol.error("unsupported", "graded checking supports pure mathematical definitions", annotations[0])
        domain = _domain(protocol, annotations[0])
        callable_input = False
        for annotation in annotations:
            if _domain(protocol, annotation) != domain:
                raise protocol.error("unsupported", "a graded definition requires a single grade domain", annotation)
            if (id(annotation) in interface_nodes and annotation["kind"] == "parameter"
                and annotation["type"] is not None and any(
                node["kind"] == "function_type" for node in syntax_nodes(cast("Node", annotation["type"]))
            )):
                callable_input = True
        projection = (
            _ModalProjection(protocol, self.syntax, domain, resolve_box=self.resolve_box)
            if modal else _Projection(protocol, self.syntax, domain)
        )
        projection.resolve_import = resolve_import
        selected = projection.definition(_name(declaration["name"]))
        for annotation in annotations:
            if id(annotation) not in projection.annotations:
                raise protocol.error("unsupported", "grade annotation has no checked projection", annotation)
        self._check_projection(projection, selected)
        if modal:
            self.modal_definitions.add(selected.name)
        caller_requirement = "callback" if callable_input else ("box" if box_interface else None)
        return projection.annotations, caller_requirement

    def _check_projection(self, projection: _Projection, definition: _Definition) -> None:
        if self.directory is None:
            try:
                self.compiler = proofenv.rocq_command()
            except SystemExit as error:
                raise self.protocol.error("unsupported", "graded checking requires an available Rocq prover",
                                          definition.source) from error
            self.directory = Path(self.stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-graded-module-")))
        dependencies = _ROCQ_FILES if definition.context is None else _MODAL_FILES
        if any(name not in self.hashes for name in dependencies):
            self.hashes.update(_support(self.root, self.compiler, self.directory, dependencies))
        source_hash = hashlib.sha256(self.protocol.source).hexdigest()
        certificate = _certificate(projection.definitions, source_hash, projection.domain, projection.provider_receipts)
        _, checked = _replay(self.compiler, self.directory, projection, certificate)
        evidence = json.dumps({"certificate": checked, "support": {name: self.hashes[name] for name in dependencies}},
                              sort_keys=True, separators=(",", ":"))
        receipt = hashlib.sha256(evidence.encode()).hexdigest()
        self.receipts.append(f"(* Graded replay {definition.name} {projection.domain}: SHA256 {receipt} *)\n")
        if definition.source["modifiers"] == ["public"]:
            box_imports = projection.box_imports.copy() if isinstance(projection, _ModalProjection) else {}
            if self.box is not None and self.box_domain is not None and self.box["modifiers"] == ["public"]:
                box_imports.setdefault("Box", self.box_domain)
            self.exports[definition.name] = GradeExport(
                self.protocol, self.syntax, definition.name,
                projection.domain, receipt,
                MappingProxyType(projection.imports.copy()),
                modal=definition.context is not None,
                box_imports=MappingProxyType(box_imports),
            )


def check(root: Path, path: Path, declaration: str, *, modal: bool = False,
          domain: GradeDomain = GradeDomain.EXACT) -> dict[str, object]:
    snapshot = read_source(path)
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, snapshot.data, surface=True)
    protocol = _Protocol(snapshot.data)
    projection = (_ModalProjection if modal else _Projection)(protocol, protocol.decode(parsed), domain)
    selected = projection.definition(declaration)
    definitions = projection.definitions
    source_hash = hashlib.sha256(snapshot.data).hexdigest()
    certificate = _certificate(definitions, source_hash, domain)
    compiler = proofenv.rocq_command()
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-source-") as temporary:
        directory = Path(temporary)
        kernel_hashes = _support(root, compiler, directory, _MODAL_FILES if modal else _ROCQ_FILES)
        demand, certificate = _replay(compiler, directory, projection, certificate)
    ensure_unchanged(snapshot)
    return {
        "status": "checked",
        "scope": "pure-natural-modal-source-trial" if modal else "pure-natural-graded-source-trial",
        "domain": domain.value,
        "source_sha256": source_hash,
        "declaration": declaration,
        "span": _span(selected.source),
        "dependencies": list(selected.records) if modal else [definition.name for definition in definitions[:-1]],
        "kernel_sha256": kernel_hashes,
        "gallina": certificate,
        "binders": [
            {"name": projection.parameters[index].name, "span": projection.parameters[index].span,
             "computation": computation, "type": type_uses,
             "annotation_type_uses": _dependency_row(projection.parameters, annotation_uses)}
            for index, computation, type_uses, *annotation_uses in demand[1:-1]
        ],
        "result_type_uses": _dependency_row(projection.parameters, demand[-1]),
    }
