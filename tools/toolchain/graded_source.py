# SPDX-License-Identifier: Apache-2.0
"""Project bounded NatExact source into the pure graded Rocq checker."""

import hashlib
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from itertools import batched
from pathlib import Path
from typing import cast

from toolchain import parser, proofenv
from toolchain.elaborate_protocol import _Protocol
from toolchain.elaborate_types import Node
from toolchain.source_file import ensure_unchanged, read_source

_PRIMITIVES = frozenset({"Nat", "Vec", "NatExact"})
_ROCQ_FILES = ("graded_pure.v", "graded_source.v")
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


class _Projection:
    def __init__(self, source: bytes, parsed: object) -> None:
        self.protocol = _Protocol(source)
        syntax = self.protocol.decode(parsed)
        self.declarations: dict[str, Node] = {}
        self.parameters: list[_Parameter] = []
        self.completed: dict[str, _Definition] = {}
        for declaration in cast("list[Node]", syntax["declarations"]):
            if declaration["kind"] in {"import", "import_item"}:
                raise self.protocol.error("unsupported", "graded source replay requires a self-contained module", declaration)
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
            if callee["kind"] == "name" and _name(callee["name"]) == "NatExact" and len(arguments) == 1:
                [argument] = arguments
                if argument["label"] is None:
                    return self._literal(cast("Node", argument["value"]))
        raise self.protocol.error("unsupported", "graded binders require an explicit @ NatExact(n) allowance", node)

    def _parameter(self, node: Node, scope: dict[str, _Parameter]) -> _Parameter:
        if node["name"] is None or node["type"] is None or node.get("const") or node.get("label"):
            raise self.protocol.error("unsupported", "graded replay requires named parameters with plain types", node)
        name = _name(node["name"])
        if name in _PRIMITIVES:
            raise self.protocol.error("grade", f"graded binder shadows primitive '{name}'", node)
        if name == "_" or "." in name or name in scope:
            raise self.protocol.error("grade", f"duplicate or invalid graded binder '{name}'", node)
        domain = self._type(cast("Node", node["type"]), scope)
        allowance = self._grade(node)
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
            if name == "Vec" and len(arguments) == 2 and self._type(arguments[0], scope) == "Natural":
                return f"(Vector {self._index(arguments[1], scope)})"
        if (node["kind"] == "function_type" and node["mode"] == "Fn" and node["parameters"]
                and not any(node[field] for field in ("generics", "captures", "effects", "contracts"))):
            extended = scope.copy()
            parameters = self._telescope(node, extended)
            codomain = self._type(cast("Node", node["result"]), extended)
            for parameter in reversed(parameters):
                codomain = parameter.abstract("Pi", codomain)
            return codomain
        raise self.protocol.error("unsupported", "graded replay supports Nat, Vec<Nat, n> and pure Fn types", node)

    def _term(self, node: Node, scope: dict[str, _Parameter], declaration: Node) -> str:
        kind = node["kind"]
        if kind == "group":
            return self._term(cast("Node", node["value"]), scope, declaration)
        if kind == "name":
            name = _name(node["name"])
            if name in scope:
                return f"(Var {scope[name].index})"
            raise self.protocol.error("grade", f"unbound value '{name}'", node)
        if kind == "lambda" and node["parameters"]:
            extended = scope.copy()
            parameters = self._telescope(node, extended)
            body = self._term(cast("Node", node["body"]), extended, declaration)
            for parameter in reversed(parameters):
                body = parameter.abstract("Lambda", body)
            return body
        if kind == "call":
            callee = cast("Node", node["callee"])
            arguments = cast("list[Node]", node["arguments"])
            if not arguments and callee["kind"] == "name":
                name = _name(callee["name"])
                earlier = self.declarations.get(name)
                if (name not in scope and earlier is not None and earlier["kind"] == "definition"
                        and not earlier["parameters"] and _span(earlier)[0] < _span(declaration)[0]):
                    return f"source_term_{self.definition(name).index}"
            if arguments and all(argument["label"] is None for argument in arguments):
                result = self._term(callee, scope, declaration)
                for argument in arguments:
                    index = self._index(cast("Node", argument["value"]), scope)
                    result = f"(ApplyNat {result} {index})"
                return result
            raise self.protocol.error("unsupported", "graded replay accepts earlier nullary definitions and positional natural applications", node)
        return f"(NatValue {self._index(node, scope)})"

    def definition(self, name: str) -> _Definition:
        if name in self.completed:
            return self.completed[name]
        node = self.declarations.get(name)
        if node is None or node["kind"] != "definition":
            raise self.protocol.error("grade", f"graded definition '{name}' was not found", node)
        if node["generics"] or node["contracts"] or node["modifiers"] not in ([], ["public"]):
            raise self.protocol.error("unsupported", "graded replay requires a plain mathematical definition", node)
        scope: dict[str, _Parameter] = {}
        parameters = self._telescope(node, scope)
        expected = self._type(cast("Node", node["result"]), scope)
        term = self._term(cast("Node", node["value"]), scope, node)
        for parameter in reversed(parameters):
            term = parameter.abstract("Lambda", term)
            expected = parameter.abstract("Pi", expected)
        result = _Definition(len(self.completed), name, node, term, expected)
        self.completed[name] = result
        return result


def _certificate(definitions: list[_Definition], source_hash: str) -> str:
    lines = [
        f"(* Source SHA-256 {source_hash} *)",
        "From Stdlib Require Import Lists.List.",
        "Require Import graded_pure graded_source.",
        "Import ListNotations GradedPure GradedSource.",
    ]
    reports = []
    for definition in definitions:
        number = definition.index
        lines.append(f"Definition source_term_{number} : term := {definition.term}.")
        lines.append(f"Definition source_type_{number} : ty := {definition.expected}.")
        reports.append(f"source_check source_term_{number} source_type_{number}")
    lines.extend([
        f"Definition source_reports := [{'; '.join(reports)}].",
        "Set Printing Width 100000.",
        "Set Printing Depth 100000.",
        "Eval vm_compute in source_reports.",
        "Example source_replays : forallb accepted source_reports = true.",
        "Proof. vm_compute. reflexivity. Qed.",
    ])
    return "\n".join(lines) + "\n"


def _run_rocq(directory: Path, unit: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([*proofenv.rocq_command(), "-q", unit], cwd=directory, capture_output=True,
                          text=True, encoding="utf-8", check=False, timeout=30)


def _verdict(projection: _Projection, replay: subprocess.CompletedProcess[str]) -> list[list[list[int]]]:
    match = _REPORT.search(replay.stdout)
    if match is None:
        raise RuntimeError(f"graded source replay gave no verdict: {replay.stderr.strip()}")
    rows = cast("list[list[list[int]]]", json.loads(match[1].replace(";", ",")))
    for definition, row in zip(projection.completed.values(), rows, strict=True):
        if row == [[0]]:
            raise projection.protocol.error("grade", "term fails exact computation demand or natural-index checking", definition.source)
        if row == [[1]]:
            raise projection.protocol.error("grade", "inferred graded type differs from the declared dependent type", definition.source)
        if len(row) < 2 or row[0] != [2]:
            raise RuntimeError("invalid Rocq grade report")
    if replay.returncode:
        raise RuntimeError(f"graded source certificate failed: {replay.stderr.strip()}")
    return rows


def _replay(root: Path, projection: _Projection, certificate: str) -> tuple[dict[str, str], list[list[int]], str]:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-source-") as temporary:
        directory = Path(temporary)
        hashes = {}
        for name in _ROCQ_FILES:
            source = (root / "tools" / "rocq" / name).read_bytes()
            hashes[name] = hashlib.sha256(source).hexdigest()
            (directory / name).write_bytes(source)
            compiled = _run_rocq(directory, name)
            if compiled.returncode:
                raise RuntimeError(f"graded Rocq support failed: {compiled.stderr.strip()}")
        (directory / "SourceReplay.v").write_text(certificate, encoding="utf-8", newline="\n")
        rows = _verdict(projection, _run_rocq(directory, "SourceReplay.v"))
        expected = json.dumps(rows).replace(",", ";")
        pinned_rows = (f"Example source_rows_match : source_reports = {expected}.\n"
                       "Proof. vm_compute. reflexivity. Qed.\n")
        report = directory / "SourceReport.v"
        report.write_text("From Stdlib Require Import Lists.List.\nRequire Import SourceReplay.\n"
                          "Import ListNotations.\n" + pinned_rows, encoding="utf-8", newline="\n")
        verified = _run_rocq(directory, report.name)
        if verified.returncode:
            raise RuntimeError(f"graded demand certificate failed: {verified.stderr.strip()}")
        return hashes, rows[-1], certificate + pinned_rows


def _dependency_row(parameters: list[_Parameter], counts: list[int]) -> list[dict[str, object]]:
    return [{"name": parameters[index].name, "span": parameters[index].span, "uses": uses}
            for index, uses in batched(counts, 2, strict=True)]


def check(root: Path, path: Path, declaration: str) -> dict[str, object]:
    snapshot = read_source(path)
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, snapshot.data, surface=True)
    projection = _Projection(snapshot.data, parsed)
    selected = projection.definition(declaration)
    definitions = list(projection.completed.values())
    source_hash = hashlib.sha256(snapshot.data).hexdigest()
    certificate = _certificate(definitions, source_hash)
    kernel_hashes, demand, certificate = _replay(root, projection, certificate)
    ensure_unchanged(snapshot)
    return {
        "status": "checked",
        "scope": "pure-natural-graded-source-trial",
        "source_sha256": source_hash,
        "declaration": declaration,
        "span": _span(selected.source),
        "dependencies": [definition.name for definition in definitions[:-1]],
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
