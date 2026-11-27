# SPDX-License-Identifier: Apache-2.0
"""Advisory checks over resolved, symbolic contract terms."""

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from toolchain.elaborate_lints import lint_probe, report_lint
from toolchain.elaborate_types import (
    _BOOL,
    _CHAR,
    _INT_SPECS,
    _NAT,
    Node,
    _app,
    _apps,
    _constant,
    _int_term,
    _Term,
    _term,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator

_TRUE = _term("bool", value=1)
_FALSE = _term("bool", value=0)
_DOMAIN_EQUALITY = {"eq_nat", "eq_bool", "char_eq", "eq_unit", "Seq_Eq"}
_RELATIONS = {
    "lt": frozenset({-1}),
    "le": frozenset({-1, 0}),
    "gt": frozenset({1}),
    "ge": frozenset({0, 1}),
    "eq": frozenset({0}),
    "ne": frozenset({-1, 1}),
}
_MODEL_PROJECTIONS = {"Seq_Count", "Slots_Capacity", "Span_Length", "Span_CanWrite"}
_STABLE_DESCRIPTOR_PROJECTIONS = {
    f"{kind}_{member}"
    for kind in ("Span", "Slots")
    for member in ("Base", "Length", "Capacity", "Tag", "PermRead", "PermWrite", "CanRead", "CanWrite")
}
_SCALARS = {_BOOL, _NAT, _CHAR, *(spec.const for spec in _INT_SPECS.values())}


@dataclass(frozen=True)
class _ContractAtom:
    node: Node
    term: _Term


class _ContractLintsMixin:
    def _lint_identical_loop_invariants(self: _Elaborator, contracts: list[Node]) -> None:
        # Concrete iterations can make independent invariant terms equal.
        seen: set[bytes] = set()
        for contract in contracts:
            if contract["role"] != "invariant":
                continue
            expression = self._unwrap_group(self.node(contract["value"]))
            start, end = cast("list[int]", expression["span"])
            source = self.protocol.source[start:end]
            if source in seen:
                self._contract_lint_at("HOLDFAST113", expression, "this loop invariant repeats an earlier one")
            seen.add(source)

    def _contract_atom(self: _Elaborator, term: _Term) -> _Term:
        term = self.resolve(term)
        head, args = self.spine(term)
        if head == _constant("Eq") and len(args) == 3 and args[0] == _BOOL:
            if args[2] == _TRUE:
                return args[1]
            if args[1] == _TRUE:
                return args[2]
            if args[2] == _FALSE:
                return _app(_constant("!"), args[1])
            if args[1] == _FALSE:
                return _app(_constant("!"), args[2])
        if head in {_constant("eq_bool"), _constant("ne_bool")} and len(args) == 2:
            for value, flag in (args, args[::-1]):
                if flag in {_TRUE, _FALSE}:
                    return value if (head == _constant("eq_bool")) == (flag == _TRUE) else _app(_constant("!"), value)
        return term

    def _contract_atoms(self: _Elaborator, node: Node, term: _Term) -> list[_ContractAtom]:
        node = self._unwrap_group(node)
        term = self._contract_atom(term)
        head, args = self.spine(term)
        if (head == _constant("&&") and len(args) == 2 and node["kind"] == "binary"
                and self.operator(node["operator"]) == "&&"):
            return [
                *self._contract_atoms(self.node(node["left"]), args[0]),
                *self._contract_atoms(self.node(node["right"]), args[1]),
            ]
        return [_ContractAtom(node, term)]

    def _contract_key(self: _Elaborator, term: _Term, binders: tuple[int, ...] = ()) -> tuple[object, ...]:
        term = self.resolve(term)
        if term.kind == "var" and term.value in binders:
            return ("bound", binders.index(term.value))
        if term.kind in {"pi", "lam"}:
            domain, body = term.args
            return (
                term.kind,
                self._contract_key(domain, binders),
                self._contract_key(body, (*binders, cast("int", term.value))),
            )
        if term.kind == "app":
            head, args = self.spine(term)
            name = head.value if head.kind == "const" else ""
            if isinstance(name, str) and (
                name in {*_DOMAIN_EQUALITY, "Eq", "Span_Disjoint"} or name.startswith("int_eq_")
            ) and len(args) >= 2:
                return (
                    "symmetric", name, tuple(self._contract_key(arg, binders) for arg in args[:-2]),
                    frozenset(self._contract_key(arg, binders) for arg in args[-2:]),
                )
            if head == _constant("Slots_Disjoint") and len(args) == 5:
                return (
                    "symmetric", name, self._contract_key(args[0], binders),
                    frozenset(
                        (self._contract_key(cap, binders), self._contract_key(slot, binders))
                        for cap, slot in ((args[1], args[3]), (args[2], args[4]))
                    ),
                )
            if head.kind == "const" and head.value in {">", ">="} and len(args) == 2:
                name = "<" if head.value == ">" else "<="
                return self._contract_key(_apps(_constant(name), *reversed(args)), binders)
            if isinstance(name, str) and name.startswith(("int_gt_", "int_ge_")) and len(args) == 2:
                name = name.replace("int_gt_", "int_lt_").replace("int_ge_", "int_le_")
                return self._contract_key(_apps(_constant(name), *reversed(args)), binders)
        return (term.kind, term.value, tuple(self._contract_key(arg, binders) for arg in term.args))

    def _contract_complement(self: _Elaborator, left: _Term, right: _Term) -> bool:
        for condition, other in ((left, right), (right, left)):
            head, args = self.spine(condition)
            if (head == _constant("!") and len(args) == 1
                    and self._contract_key(args[0]) == self._contract_key(other)):
                return True
        left_shape = self._contract_outcome_test(left)
        right_shape = self._contract_outcome_test(right)
        return (
            left_shape is not None and right_shape is not None
            and left_shape[0] == right_shape[0] and left_shape[1] != right_shape[1]
        )

    def _contract_outcome_test(self: _Elaborator, term: _Term) -> tuple[_Term, bool] | None:
        if term.kind == "sum_match" and len(term.args) == 4:
            _, scrutinee, first, second = term.args
            if first.kind == second.kind == "lam" and {first.args[1], second.args[1]} == {_TRUE, _FALSE}:
                return scrutinee, first.args[1] == _TRUE
        return None

    def _contract_components(self: _Elaborator, term: _Term) -> tuple[_Term, ...]:
        head, args = self.spine(term)
        if isinstance(head.value, str) and head.kind == "const":
            prefix, _, name = head.value.partition("_")
            if (name in {"CanRead", "CanWrite"}
                    and ((prefix == "Span" and len(args) == 2) or (prefix == "Slots" and len(args) == 3))):
                return (
                    _apps(_constant(f"{prefix}_Tag"), *args),
                    _apps(_constant(f"{prefix}_Perm{name[3:]}"), *args),
                )
        components = self._slots_predicate_components(head, args)
        if components:
            elem, capacity, slots, *counts = args
            cap = self.resolve(capacity)
            conversion, operands = self.spine(cap)
            if ((cap.kind == "nat" and 0 <= cast("int", cap.value) <= _INT_SPECS["usize"].max_val)
                    or (conversion == _constant("int_to_nat_usize") and len(operands) == 1)):
                represented = _apps(_constant("Slots_Capacity"), elem, capacity, slots)
                return (*components, _apps(_constant("int_le_usize"), counts[-1], represented))
            return components
        if head == _constant("Eq") and len(args) == 3:
            for span, other in (args[1:], args[:0:-1]):
                rhs, rhs_args = self.spine(other)
                if rhs == _constant("Span_Slice") and len(rhs_args) == 4:
                    return (_apps(_constant("int_eq_usize"), _apps(_constant("Span_Length"), rhs_args[0], span),
                                  rhs_args[3]),)
                if rhs == _constant("Span_ReadOnly") and len(rhs_args) == 2:
                    return (_app(_constant("!"), _apps(_constant("Span_CanWrite"), rhs_args[0], span)),)
        return ()

    def _contract_reduced_operand(self: _Elaborator, term: _Term) -> _Term:
        term = self.resolve(term)
        head, args = self.spine(term)
        if head == _constant("Slots_Capacity") and len(args) == 3:
            return self._slots_cap_usize_term(args[1])
        if head == _constant("Seq_Count") and len(args) == 2:
            model, model_args = self.spine(args[1])
            if model == _constant("Vec_Model") and len(model_args) == 3:
                return model_args[1]
            if model == _constant("Span_Model") and len(model_args) == 2:
                return _app(_constant("int_to_nat_usize"), _apps(_constant("Span_Length"), *model_args))
        if head.kind == "const" and isinstance(head.value, str) and head.value in _MODEL_PROJECTIONS:
            return self.whnf(term)
        return term

    def _contract_range(
        self: _Elaborator, term: _Term,
    ) -> tuple[str, tuple[object, ...], int, frozenset[int]] | None:
        comparison = self._parse_cmp_fact_shape(term)
        if comparison is None:
            return None
        op, spec, left, right = comparison
        domain = spec.name if spec is not None else "Nat"
        literal_kind = "int" if spec is not None else "nat"
        if self.spine(term)[0].value in {"char_lt", "char_le", "char_gt", "char_ge", "char_eq", "char_ne"}:
            domain = "char"
            literal_kind = "char"
        relations = _RELATIONS[op]
        if right.kind == literal_kind:
            return domain, self._contract_key(left), cast("int", right.value), relations
        if left.kind == literal_kind:
            return domain, self._contract_key(right), cast("int", left.value), frozenset(-r for r in relations)
        return None

    def _contract_compare_ranges(
        self: _Elaborator, left: _Term, right: _Term, *, contradiction: bool = False,
    ) -> bool:
        first = self._contract_range(left)
        second = self._contract_range(right)
        if first is None or second is None or first[:2] != second[:2]:
            return self._contract_compare_same_operands(left, right, contradiction=contradiction)
        _, _, a, allowed_a = first
        _, _, b, allowed_b = second
        test_values = (min(a, b) - 1, a, min(a, b) + 1, b, max(a, b) + 1)
        for value in test_values:
            a_rel = (value > a) - (value < a)
            b_rel = (value > b) - (value < b)
            if a_rel in allowed_a and (b_rel in allowed_b) == contradiction:
                return False
        return True

    def _contract_compare_same_operands(
        self: _Elaborator, left: _Term, right: _Term, *, contradiction: bool,
    ) -> bool:
        first, second = self._parse_cmp_fact_shape(left), self._parse_cmp_fact_shape(right)
        if first is None or second is None or first[1] != second[1]:
            return False
        lhs = [self._contract_key(term) for term in first[2:]]
        rhs = [self._contract_key(term) for term in second[2:]]
        allowed = _RELATIONS[second[0]]
        if lhs == rhs[::-1]:
            allowed = frozenset(-relation for relation in allowed)
        elif lhs != rhs:
            return False
        actual = _RELATIONS[first[0]]
        return actual.isdisjoint(allowed) if contradiction else actual <= allowed

    def _contract_stable_entry(self: _Elaborator, term: _Term) -> bool:
        """Identify entry facts that do not depend on memory contents."""
        term = self.resolve(term)
        if term.kind == "var":
            return self.whnf(self.types[cast("int", term.value)]) in _SCALARS
        if term.kind in {"nat", "int", "bool", "char"}:
            return True
        head, args = self.spine(term)
        if head.kind != "const" or not isinstance(head.value, str):
            return False
        if head.value in _STABLE_DESCRIPTOR_PROJECTIONS:
            return bool(args) and self.resolve(args[-1]).kind == "var"
        if head.value.startswith("int_") or head.value in {
            "!", "&&", "||", "==>", "<==>", "<", "<=", ">", ">=", "eq_nat", "ne_nat", "eq_bool", "ne_bool",
            "char_eq", "char_ne", "char_ge", "char_gt", "char_le", "char_lt",
        }:
            return all(self._contract_stable_entry(arg) for arg in args)
        return False

    def _contract_type_law(self: _Elaborator, term: _Term, facts: set[tuple[object, ...]]) -> str | None:
        head, args = self.spine(term)
        if head == _constant("Span_Disjoint") and len(args) == 3:
            for span in args[1:]:
                length = _apps(_constant("Span_Length"), args[0], span)
                zero = _int_term(_INT_SPECS["usize"], 0)
                if self._contract_reduced_operand(length) == zero or self._contract_key(
                    _apps(_constant("int_eq_usize"), length, zero)
                ) in facts:
                    return "an empty span is disjoint from every span"
        if head == _constant("Slots_Disjoint") and len(args) == 5 and any(
            self.resolve(cap) == _term("nat", value=0) for cap in args[1:3]
        ):
            return "an empty slots extent is disjoint from every slots extent"
        if head.kind == "const" and isinstance(head.value, str) and (
            head.value in _DOMAIN_EQUALITY or head.value == "Eq" or head.value.startswith("int_eq_")
        ) and len(args) >= 2:
            left, right = args[-2:]
            l_value, r_value = self._contract_reduced_operand(left), self._contract_reduced_operand(right)
            if (left != l_value or right != r_value) and self._contract_key(l_value) == self._contract_key(r_value):
                return "this equality follows from the descriptor or sequence model"
        numeric = self._contract_range(term)
        if numeric is not None:
            domain, _, limit, relations = numeric
            if domain == "Nat":
                minimum, maximum = 0, None
            elif domain in _INT_SPECS:
                spec = _INT_SPECS[domain]
                minimum, maximum = spec.min_val, spec.max_val
            else:
                return None
            if ((limit < minimum or (maximum is not None and limit > maximum) or 0 in relations)
                    and ((maximum is not None and limit >= maximum) or 1 in relations)
                    and (limit <= minimum or -1 in relations)):
                return "this bound follows from the scalar type"
        return None

    def _contract_implication(self: _Elaborator, term: _Term) -> tuple[_Term, _Term] | None:
        head, args = self.spine(term)
        if head == _constant("==>") and len(args) == 2:
            return self._contract_atom(args[0]), self._contract_atom(args[1])
        if term.kind == "pi":
            domain, body = term.args
            h_domain, domain_args = self.spine(domain)
            if h_domain == _constant("Eq") and len(domain_args) == 3 and domain_args[0] == _BOOL:
                return self._contract_atom(domain), self._contract_atom(body)
        return None

    def _contract_false_by(self: _Elaborator, term: _Term, facts: list[_Term]) -> bool:
        term = self._contract_atom(term)
        if term == _FALSE:
            return True
        head, args = self.spine(term)
        if head == _constant("&&") and len(args) == 2:
            return (self._contract_complement(args[0], args[1])
                    or self._contract_compare_ranges(args[0], args[1], contradiction=True)
                    or any(self._contract_false_by(arg, facts) for arg in args))
        if self._parse_cmp_fact_shape(term) is not None and (
            self.whnf(term) == _FALSE or self._contract_type_law(self._negate_bool_term(term), set()) is not None
        ):
            return True
        return any(
            self._contract_complement(term, fact)
            or self._contract_compare_ranges(term, fact, contradiction=True)
            or self._contract_complement(term, component)
            for fact in facts for component in (fact, *self._contract_components(fact))
        )

    def _contract_vacuity(self: _Elaborator, term: _Term, facts: list[_Term]) -> str | None:
        head, args = self.spine(term)
        if head == _constant("Seq_All") and len(args) == 3:
            count = _apps(_constant("Seq_Count"), args[0], args[1])
            zero = _term("nat", value=0)
            empty = self._contract_key(_apps(_constant("eq_nat"), count, zero))
            if self._contract_reduced_operand(count) == zero or any(self._contract_key(fact) == empty for fact in facts):
                return "All holds vacuously on this empty sequence"
        quantified = False
        while term.kind == "pi" and self._contract_implication(term) is None:
            quantified = True
            term = term.args[1]
        implication = self._contract_implication(term)
        if implication is not None and self._contract_false_by(implication[0], facts):
            return "this quantified range is empty" if quantified else "this implication's antecedent is impossible"
        return None

    def _contract_tautology(self: _Elaborator, term: _Term) -> str | None:
        if term == _TRUE:
            return "this contract conjunct is always true"
        head, args = self.spine(term)
        if head == _constant("||") and len(args) == 2 and self._contract_complement(args[0], args[1]):
            return "these alternatives exhaust the possible cases"
        if (head.kind == "const" and isinstance(head.value, str)
                and (head.value in {*_DOMAIN_EQUALITY, "Eq"} or head.value.startswith("int_eq_"))
                and len(args) >= 2 and self._contract_key(args[-2]) == self._contract_key(args[-1])):
            return "this equality compares a value with itself"
        if self._parse_cmp_fact_shape(term) is not None and self.whnf(term) == _TRUE:
            return "this comparison always holds"
        implication = self._contract_implication(term)
        if implication is not None:
            antecedent, consequent = implication
            if self._contract_key(antecedent) == self._contract_key(consequent):
                return "the consequent repeats this implication's antecedent"
        if (term.kind in {"if", "bool_match"} and len(term.args) == 4
                and self._contract_key(term.args[2]) == self._contract_key(term.args[3])):
            return "both conditional branches state the same guarantee"
        if term.kind == "sum_match" and len(term.args) == 4:
            left, right = term.args[2:]
            if (left.kind == right.kind == "lam"
                    and left.value not in self.free(left.args[1]) and right.value not in self.free(right.args[1])
                    and self._contract_key(left.args[1]) == self._contract_key(right.args[1])):
                return "both possible outcomes state the same guarantee"
        return None

    _CONTRACT_SUPPRESSORS = (
        "HOLDFAST109", "HOLDFAST112", "HOLDFAST113", "HOLDFAST114", "HOLDFAST115", "HOLDFAST116",
        "HOLDFAST117",
    )

    def _contract_lint_at(self: _Elaborator, code: str, node: Node, message: str) -> None:
        report_lint(self, code, node, message, suppressed_by=self._CONTRACT_SUPPRESSORS)

    def _lint_contracts(
        self: _Elaborator,
        role: str,
        checked: list[tuple[Node, _Term]],
        *,
        type_facts: tuple[_Term, ...] = (),
        entry_facts: tuple[tuple[Node, _Term], ...] = (),
        inherited: tuple[_Term, ...] = (),
        type_inputs: tuple[_Term, ...] = (),
        result_image: tuple[_Term, _Term] | None = None,
        record_binders: tuple[_Term, ...] = (),
    ) -> None:
        if not checked:
            return
        with lint_probe(self, work_limit=12_000, reduction_limit=2_000):
            if type_inputs:
                type_facts += tuple(self._record_input_propositions(list(type_inputs)))
            if record_binders:
                checked = [
                    (node, self.substitute(term, cast("int", binder.value), record_binders[0]))
                    for (node, term), binder in zip(checked, record_binders, strict=True)
                ]
            if result_image is not None:
                checked = [(node, self._replace_images(term, [result_image])) for node, term in checked]
                inherited = tuple(self._replace_images(term, [result_image]) for term in inherited)
            self._lint_checked_contracts(role, checked, type_facts, entry_facts, inherited)

    def _lint_checked_contracts(
        self: _Elaborator, role: str, checked: list[tuple[Node, _Term]], type_facts: tuple[_Term, ...],
        entry_facts: tuple[tuple[Node, _Term], ...], inherited: tuple[_Term, ...],
    ) -> None:
        atoms = [atom for node, term in checked for atom in self._contract_atoms(self.node(node["value"]), term)]
        if len(atoms) > 96:
            return
        terms = [atom.term for atom in atoms]
        keys = [self._contract_key(term) for term in terms]
        types = {self._contract_key(self._contract_atom(term)) for term in type_facts}
        inherited_keys = {self._contract_key(self._contract_atom(term)) for term in inherited}
        entry = [
            atom.term
            for node, term in entry_facts
            for atom in self._contract_atoms(self.node(node["value"]), term)
            if self._contract_stable_entry(atom.term)
        ]
        entry_keys = {self._contract_key(term) for term in entry}
        seen: set[tuple[object, ...]] = set()
        for index, atom in enumerate(atoms):
            term, key = atom.term, keys[index]
            others = [*terms[:index], *terms[index + 1:]]
            facts_by_key = set(keys) - {key}
            components = {
                self._contract_key(component) for other in others for component in self._contract_components(other)
            }
            if role == "requires" and self._contract_false_by(term, terms[:index]):
                self._contract_lint_at("HOLDFAST116", atom.node, "this requirement makes the caller domain empty")
            elif key in seen:
                self._contract_lint_at("HOLDFAST113", atom.node, f"this {role} conjunct repeats an earlier conjunct")
            elif key in inherited_keys:
                self._contract_lint_at("HOLDFAST117", atom.node, "this contract follows from the interface method")
            elif key in types:
                self._contract_lint_at("HOLDFAST112", atom.node, "this condition follows from the nominal record invariant")
            elif key in components:
                self._contract_lint_at("HOLDFAST112", atom.node, "this condition follows from another library predicate or equality")
            elif (message := self._contract_type_law(term, facts_by_key)) is not None:
                self._contract_lint_at("HOLDFAST112", atom.node, message)
            elif (message := self._contract_vacuity(term, [*others, *entry])) is not None:
                self._contract_lint_at("HOLDFAST116", atom.node, message)
            elif (message := self._contract_tautology(term)) is not None:
                self._contract_lint_at("HOLDFAST115", atom.node, message)
            elif key in entry_keys or any(self._contract_compare_ranges(other, term) for other in entry) or any(
                other_index != index and self._contract_compare_ranges(other, term)
                and (other_index < index or not self._contract_compare_ranges(term, other))
                for other_index, other in enumerate(terms)
            ):
                self._contract_lint_at("HOLDFAST114", atom.node, "another contract condition implies this conjunct")
            elif implication := self._contract_implication(term):
                self._lint_contract_implication(atom, implication, terms[:index], facts_by_key)
            seen.add(key)

    def _lint_contract_implication(
        self: _Elaborator, atom: _ContractAtom, implication: tuple[_Term, _Term], previous: list[_Term],
        facts: set[tuple[object, ...]],
    ) -> None:
        guard, guarantee = implication
        if self._contract_key(guard) in facts:
            self._contract_lint_at("HOLDFAST114", atom.node, "another contract conjunct already establishes this antecedent")
            return
        for term in previous:
            earlier = self._contract_implication(term)
            if (earlier is not None and self._contract_complement(earlier[0], guard)
                    and self._contract_key(earlier[1]) == self._contract_key(guarantee)):
                self._contract_lint_at("HOLDFAST115", atom.node, "both possible outcomes state the same guarantee")
                return
