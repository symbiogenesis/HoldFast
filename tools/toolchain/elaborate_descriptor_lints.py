# SPDX-License-Identifier: Apache-2.0
"""Lint facts implied by checked descriptor modes and stable contract operands."""

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from toolchain.elaborate_types import Node, _parse_numeric_magnitude, _Term, _term

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


type _Member = tuple[str, str, bool]


@dataclass(frozen=True)
class _Operand:
    key: _Term
    members: tuple[_Member, ...] = ()


@dataclass(frozen=True)
class _Scope:
    shadowed: frozenset[str] = frozenset()
    scalars: frozenset[str] = frozenset()

    def bind(self, names: frozenset[str], scalars: frozenset[str] = frozenset()) -> _Scope:
        return _Scope(self.shadowed | names, (self.scalars - names) | scalars)


def _offset(node: Node) -> int:
    return cast("list[int]", node["span"])[0]


class DescriptorContractLints:
    def __init__(
        self, elaborator: _Elaborator, properties: dict[str, frozenset[str]], stable_scalars: frozenset[str],
        shared: frozenset[str],
    ) -> None:
        self.elab = elaborator
        self.properties = properties
        self.stable_scalars = stable_scalars
        self.shared = shared
        self.requirements: set[_Term] = set()

    def lint(self, requires: list[Node], ensures: list[Node], restores: list[Node]) -> None:
        for clause in restores:
            target = self.elab.name(self.elab.node(clause["value"])["name"])
            if target in self.properties and target not in self.shared:
                self.elab.semantic_lints["HOLDFAST110", _offset(clause)] = (
                    f"restores clause for '{target}' repeats automatic ref descriptor restoration"
                )
        for clause in requires:
            if clause["role"] == "requires":
                self._requirements(self.elab.node(clause["value"]), _Scope())
        for clause in ensures:
            self._visit(self.elab.node(clause["value"]), _Scope(frozenset({"result"})))

    def _old_argument(self, node: Node, scope: _Scope) -> Node | None:
        if node["kind"] != "call" or "old" in self.elab.entry_env or "old" in scope.shadowed:
            return None
        callee = self.elab._unwrap_group(self.elab.node(node["callee"]))
        if callee["kind"] != "name" or self.elab.name(callee["name"]) != "old":
            return None
        args = self.elab.nodes(node["arguments"])
        if len(args) == 1 and args[0]["label"] is None:
            return self.elab._unwrap_group(self.elab.node(args[0]["value"]))
        return None

    def _descriptor(self, node: Node, scope: _Scope, *, entry: bool) -> _Member | None:
        if node["kind"] != "member":
            return None
        receiver = self.elab._unwrap_group(self.elab.node(node["value"]))
        if (old_receiver := self._old_argument(receiver, scope)) is not None:
            receiver, scope, entry = old_receiver, _Scope(), True
        if receiver["kind"] != "name":
            return None
        name, field = self.elab.name(receiver["name"]), self.elab.name(node["name"])
        if name not in scope.shadowed and field in self.properties.get(name, ()):
            return name, field, entry
        return None

    def _operand(self, node: Node, scope: _Scope, *, entry: bool = False) -> _Operand | None:
        node = self.elab._unwrap_group(node)
        if (old := self._old_argument(node, scope)) is not None:
            return self._operand(old, _Scope(), entry=True)
        if (member := self._descriptor(node, scope, entry=entry)) is not None:
            name, field, _ = member
            return _Operand(_term("descriptor", value=f"{name}.{field}"), (member,))
        if node["kind"] == "name":
            name = self.elab.name(node["name"])
            if name in scope.scalars or (name in self.stable_scalars and name not in scope.shadowed):
                return _Operand(_term("name", value=name))
        if node["kind"] == "nat":
            suffix = cast("str", node["suffix"])
            chosen = suffix or self.elab.contextual_literal_types.get(_offset(node), "")
            return _Operand(_term("number", _term("type", value=chosen),
                                  value=_parse_numeric_magnitude(cast("str", node["value"]))))
        if node["kind"] == "bool":
            return _Operand(_term("bool", value=int(cast("bool", node["value"]))))
        if node["kind"] == "unary":
            operator = node["operator"]
            if isinstance(operator, dict) and (op := operator.get("text")) in ("!", "-"):
                value = self._operand(self.elab.node(node["value"]), scope, entry=entry)
                if value is not None:
                    return _Operand(_term(cast("str", op), value.key), value.members)
        if node["kind"] == "binary":
            return self._binary_operand(node, scope, entry=entry)
        return None

    def _binary_operand(self, node: Node, scope: _Scope, *, entry: bool) -> _Operand | None:
        op = self.elab.operator(node["operator"])
        if op not in {"==", "!=", ">", ">=", "<", "<=", "+", "-", "*", "/", "%"}:
            return None
        left = self._operand(self.elab.node(node["left"]), scope, entry=entry)
        right = self._operand(self.elab.node(node["right"]), scope, entry=entry)
        if left is None or right is None:
            return None
        if op in {">", ">="}:
            left, right = right, left
            op = "<" if op == ">" else "<="
        if op in {"==", "!="}:
            if left.key.kind == "bool":
                left, right = right, left
            if right.key.kind == "bool":
                positive = bool(right.key.value) == (op == "==")
                return _Operand(left.key if positive else _term("!", left.key), left.members)
            if repr(left.key) > repr(right.key):
                left, right = right, left
        return _Operand(_term(op, left.key, right.key), left.members + right.members)

    def _pattern_names(self, pattern: Node) -> frozenset[str]:
        if pattern["kind"] == "binding_pattern":
            return frozenset({self.elab.name(pattern["name"])})
        names: set[str] = set()
        for key in ("pattern", "arguments", "elements", "patterns"):
            inner = pattern.get(key)
            if isinstance(inner, dict):
                names.update(self._pattern_names(self.elab.node(inner)))
            elif isinstance(inner, list):
                for child in self.elab.nodes(inner):
                    names.update(self._pattern_names(child))
        return frozenset(names)

    def _and_paths(self, node: Node, scope: _Scope) -> list[tuple[Node, _Scope]]:
        paths: list[tuple[Node, _Scope]] = []

        def collect(expression: Node, current: _Scope) -> _Scope:
            expression = self.elab._unwrap_group(expression)
            if expression["kind"] == "binary":
                op = self.elab.operator(expression["operator"])
                left = self.elab._unwrap_group(self.elab.node(expression["left"]))
                right = self.elab._unwrap_group(self.elab.node(expression["right"]))
                if op == "&&":
                    return collect(right, collect(left, current))
                if op in {"==", "!="}:
                    if left["kind"] == "bool":
                        left, right = right, left
                    if (right["kind"] == "bool" and bool(right["value"]) == (op == "==")
                            and left["kind"] != "bool"):
                        # Boolean comparison preserves truth and keeps inner binding scope local.
                        collect(left, current)
                        return current
            paths.append((expression, current))
            if expression["kind"] == "is":
                return current.bind(self._pattern_names(self.elab.node(expression["pattern"])))
            return current

        collect(node, scope)
        return paths

    def _true_scope(self, node: Node, scope: _Scope) -> _Scope:
        # Only direct pattern tests and authored conjunctions export bindings.
        for conjunct in self.elab._conjuncts(node):
            if conjunct["kind"] == "is":
                scope = scope.bind(self._pattern_names(self.elab.node(conjunct["pattern"])))
        return scope

    def _requirements(self, node: Node, scope: _Scope) -> None:
        for part, current_scope in self._and_paths(node, scope):
            predicate = self._operand(part, current_scope)
            if predicate is not None and predicate.members:
                self.requirements.add(predicate.key)

    def _diagnostic(self, site: Node, member: _Member, *, guard: bool = False, requires: bool = False) -> None:
        name, field, _ = member
        mode = "in" if name in self.shared else "ref"
        self.elab.semantic_lints["HOLDFAST109", _offset(site)] = (
            f"guard repeats an equivalent bound on '{name}.{field}' preserved by {mode} descriptor mode" if guard
            else f"postcondition for '{name}.{field}' follows from {mode} descriptor preservation"
                 + (" and the entry requirement" if requires else "")
        )

    def _visit(self, node: Node, scope: _Scope, *, guard: bool = False) -> None:
        seen: dict[_Term, tuple[_Member, ...]] = {}
        for part, current_scope in self._and_paths(node, scope):
            operand = self._operand(part, current_scope)
            if operand is not None and operand.members:
                if guard and operand.key in seen and seen[operand.key] != operand.members:
                    self._diagnostic(part, operand.members[0], guard=True)
                    continue
                seen.setdefault(operand.key, operand.members)
                repeats_requirement = operand.key in self.requirements
                if not guard and (repeats_requirement or self._cross_phase_equality(operand)):
                    self._diagnostic(part, operand.members[0], requires=repeats_requirement)
                    continue
            self._visit_part(part, current_scope, guard=guard)

    @staticmethod
    def _cross_phase_equality(operand: _Operand) -> bool:
        return (operand.key.kind == "==" and operand.key.args[0] == operand.key.args[1]
                and any(member[2] for member in operand.members)
                and any(not member[2] for member in operand.members))

    def _visit_part(self, node: Node, scope: _Scope, *, guard: bool) -> None:
        kind = node["kind"]
        if kind == "binary":
            op = self.elab.operator(node["operator"])
            left, right = self.elab.node(node["left"]), self.elab.node(node["right"])
            if op == "==>":
                self._visit(left, scope, guard=True)
                self._visit(right, self._true_scope(left, scope), guard=guard)
                return
        if kind == "if_expression":
            condition = self.elab.node(node["condition"])
            self._visit(condition, scope, guard=True)
            self._visit(self.elab.node(node["then"]), self._true_scope(condition, scope), guard=guard)
            self._visit(self.elab.node(node["else"]), scope, guard=guard)
            return
        if kind == "match_expression":
            self._visit_old(self.elab.node(node["value"]), scope)
            for case in self.elab.nodes(node["cases"]):
                bound = self._pattern_names(self.elab.node(case["pattern"]))
                self._visit(self.elab.node(case["value"]), scope.bind(bound), guard=guard)
            return
        if kind == "quantifier":
            bound = frozenset(self.elab.name(param["name"]) for param in self.elab.nodes(node["parameters"])
                              if param["name"] is not None)
            self._visit(self.elab.node(node["value"]), scope.bind(bound, bound - self.stable_scalars), guard=guard)
            return
        self._visit_old(node, scope)

    def _visit_old(self, node: Node, scope: _Scope) -> None:
        node = self.elab._unwrap_group(node)
        if (old := self._old_argument(node, scope)) is not None:
            entry = self._operand(old, _Scope())
            current = self._operand(old, scope)
            if entry is not None and current is not None and entry.key == current.key:
                self.elab.semantic_lints["HOLDFAST111", _offset(node)] = (
                    "old is redundant because its operand is stable"
                )
            return
        if (member := self._descriptor(node, scope, entry=False)) is not None and member[2]:
            receiver = self.elab._unwrap_group(self.elab.node(node["value"]))
            if member[0] not in scope.shadowed:
                self.elab.semantic_lints["HOLDFAST111", _offset(receiver)] = (
                    f"old is redundant for the preserved descriptor property '{member[0]}.{member[1]}'"
                )
            return
        # These expression forms introduce no local bindings in their operands.
        if node["kind"] in {"binary", "unary", "member", "index", "call", "argument", "tuple", "is"}:
            for key in ("left", "right", "value", "index", "callee", "arguments", "values"):
                child = node.get(key)
                if isinstance(child, dict):
                    self._visit_old(self.elab.node(child), scope)
                elif isinstance(child, list):
                    for item in self.elab.nodes(child):
                        self._visit_old(item, scope)
