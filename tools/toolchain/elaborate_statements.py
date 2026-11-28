# SPDX-License-Identifier: Apache-2.0
"""Imperative statements, propagation, loops, scopes, and control-flow elaboration for HoldFast."""

from collections.abc import Callable, Collection, Generator
from contextlib import contextmanager
from dataclasses import replace
from typing import TYPE_CHECKING, Literal, cast

from toolchain.ast import HoldFastError
from toolchain.elaborate_flow_lints import branch as lint_branch
from toolchain.elaborate_flow_lints import observe, range_loop, stable_loop_fact, while_entry
from toolchain.elaborate_protocol import _ASSIGN_OPERATORS
from toolchain.elaborate_resource_lints import _walk, lint_extra_lifts
from toolchain.elaborate_types import (
    _BOOL,
    _INT_SPECS,
    _NAT,
    _PROP,
    _U8,
    _UNIT,
    _USIZE,
    Node,
    _app,
    _apps,
    _Binding,
    _constant,
    _IndexedBorrowPeer,
    _IndexedLocalBorrow,
    _int_term,
    _IntSpec,
    _Pat,
    _RecordInfo,
    _Term,
    _term,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


class _StatementsMixin:
    @contextmanager
    def _inline_proof_scope(self: _Elaborator) -> Generator[None]:
        if not self.in_executable_function or self.in_inline_proof:
            yield
            return
        # A proof sees the current values and permissions. Only its stated facts
        # may reach the next runtime statement, including when a binder name is reused.
        mutable, borrows, views = self.mutable_locals, self.local_borrows, self.slice_views
        own_updates = self.slice_view_own_updates
        indexed_borrows, peers = self.indexed_local_borrows, self.indexed_borrow_peers
        restored, uninitialized = self.restored_view_terms, self.uninitialized_out_params
        verdicts, updates, active = self.result_bindings, self.last_call_updates, self.active_facts
        exit_env, exit_facts, theorem_facts = self.final_ref_bindings, self.final_return_facts, self.final_theorem_facts
        self.mutable_locals, self.local_borrows, self.slice_views = mutable.copy(), borrows.copy(), views.copy()
        self.slice_view_own_updates = {k: set(v) for k, v in own_updates.items()}
        self.indexed_local_borrows, self.indexed_borrow_peers = indexed_borrows.copy(), peers.copy()
        self.restored_view_terms, self.uninitialized_out_params = restored.copy(), uninitialized.copy()
        self.result_bindings, self.last_call_updates, self.active_facts = {}, [], active.copy()
        self.final_ref_bindings, self.final_return_facts, self.final_theorem_facts = {}, [], ()
        self.in_inline_proof = True
        try:
            yield
        finally:
            self.in_inline_proof = False
            self.mutable_locals, self.local_borrows, self.slice_views = mutable, borrows, views
            self.slice_view_own_updates = own_updates
            self.indexed_local_borrows, self.indexed_borrow_peers = indexed_borrows, peers
            self.restored_view_terms, self.uninitialized_out_params = restored, uninitialized
            self.result_bindings, self.last_call_updates, self.active_facts = verdicts, updates, active
            self.final_ref_bindings, self.final_return_facts, self.final_theorem_facts = exit_env, exit_facts, theorem_facts

    def _statement_proof_facts(
        self: _Elaborator, statement: Node, environment: dict[str, _Binding], facts: tuple[_Binding, ...],
    ) -> list[_Binding]:
        with self._inline_proof_scope():
            environment = dict(environment)
            if statement["kind"] == "assert":
                return [self._elaborate_assert(statement, environment, facts)]
            body = self.node(statement["body"], "block")
            if statement["kind"] == "proof":
                return self._elaborate_proof_statement(body, environment, facts)
            return self._elaborate_calc_statement(body, environment, facts)

    def _branch_guard(self: _Elaborator, condition: _Term, truth: bool) -> tuple[_Binding, ...]:
        if not self.in_executable_function:
            return ()
        cond_w = self.resolve(condition)
        if cond_w.kind == "var" and self.whnf(self.types[cast("int", cond_w.value)]) == _BOOL:
            prop = _apps(_constant("Eq"), _BOOL, cond_w, _term("bool", value=int(truth)))
            return (_Binding(self.fresh(prop), prop),)
        head, _ = self.spine(cond_w)
        if head.kind != "const" or not isinstance(head.value, str):
            return ()
        cname = head.value
        if cname not in {
            "<=", "<", ">=", ">", "eq_nat", "ne_nat",
            "eq_bool", "ne_bool", "&&", "||", "!", "==>", "<==>",
        } and not cname.startswith(
            ("int_le_", "int_lt_", "int_ge_", "int_gt_", "int_eq_", "int_ne_")
        ):
            return ()
        prop = _apps(_constant("Eq"), _BOOL, cond_w, _term("bool", value=int(truth)))
        return (_Binding(self.fresh(prop), prop),)

    def _branch_value(
        self: _Elaborator, value_type: _Term, condition: _Term, yes: _Term, no: _Term,
        yes_guard: tuple[_Binding, ...], no_guard: tuple[_Binding, ...],
    ) -> _Term:
        if yes_guard and no_guard:
            positive, negative = yes_guard[0], no_guard[0]
            yes_id, no_id = cast("int", positive.term.value), cast("int", negative.term.value)
            if yes_id in self.free(yes) or no_id in self.free(no):
                # Dependent elimination supplies the equality for the selected arm.
                bit = self.fresh(_BOOL)
                premise = _apps(_constant("Eq"), _BOOL, condition, bit)
                motive = _term("lam", _BOOL, self.pi(premise, value_type), value=bit.value)
                match = _term(
                    "bool_match", motive, condition,
                    _term("lam", positive.type, yes, value=yes_id),
                    _term("lam", negative.type, no, value=no_id),
                )
                return _app(match, _apps(_constant("Refl"), _BOOL, condition))
        return _term("if", value_type, condition, yes, no)

    @staticmethod
    def _unwrap_group(node: Node) -> Node:
        while node["kind"] == "group" and isinstance(node.get("value"), dict):
            node = cast("Node", node["value"])
        return node

    def _conjuncts(self: _Elaborator, condition: Node) -> list[Node]:
        pending = [condition]
        operands: list[Node] = []
        while pending:
            operand = self._unwrap_group(pending.pop())
            if operand["kind"] == "binary" and self.operator(operand["operator"]) == "&&":
                pending.extend((self.node(operand["right"]), self.node(operand["left"])))
            else:
                operands.append(operand)
        return operands

    def _pattern_conjuncts(self: _Elaborator, condition: Node) -> list[Node]:
        """Find the positive pattern tests on a short-circuit conjunction's spine."""
        operands = self._conjuncts(condition)
        return operands if len(operands) > 1 and any(op["kind"] == "is" for op in operands) else []

    def _binding_implication(
        self: _Elaborator, node: Node, environment: dict[str, _Binding], expected: _Term,
    ) -> _Term | None:
        operands = self._conjuncts(self.node(node["left"]))
        if not any(op["kind"] == "is" and self._pattern_names(self.node(op["pattern"])) for op in operands):
            return None
        consequent = self.node(node["right"])
        fallback: Node = {"kind": "bool", "span": node["span"], "value": True}
        if expected == _PROP:
            consequent = {"kind": "guard_proposition", "span": consequent["span"], "value": consequent}
            fallback = {"kind": "guard_proposition", "span": fallback["span"], "value": fallback}
        guarded = self._guard_conditional(node, operands, consequent, fallback, environment)
        return self._check_guard_value(guarded, environment, expected).term

    @staticmethod
    def _guard_environment(scope: Node, environment: dict[str, _Binding]) -> dict[str, _Binding]:
        return {name: environment[name] for name in cast("tuple[str, ...]", scope["locals"])}

    def _leave_statement_scope(
        self: _Elaborator, visible: Collection[str], environment: dict[str, _Binding],
    ) -> dict[str, _Binding]:
        for name in environment.keys() - visible:
            self.mutable_locals.discard(name)
            self.local_borrows.pop(name, None)
            self.indexed_local_borrows.pop(name, None)
            self.slice_views.pop(name, None)
            self.slice_view_own_updates.pop(name, None)
            self.local_value_regions.pop(name, None)
        return {name: binding for name, binding in environment.items() if name in visible}

    def _guard_conditional(
        self: _Elaborator, site: Node, operands: list[Node], yes: Node, no: Node,
        environment: dict[str, _Binding],
    ) -> Node:
        # A failed test evaluates the fallback in the scope from before the guard.
        fallback: Node = {"kind": "guard_scope", "span": no["span"], "locals": tuple(environment), "value": no}
        result = yes
        for operand in reversed(operands):
            result = {"kind": "if_expression", "span": site["span"], "condition": operand, "then": result, "else": fallback}
        return result

    def _guard_block_state(
        self: _Elaborator, node: Node, environment: dict[str, _Binding],
    ) -> _Binding:
        mutable = set(self.mutable_locals)
        try:
            after, control = self._elaborate_non_returning_block(
                self.node(node["body"]), environment, cast("tuple[_Binding, ...]", node["facts"]),
            )
        finally:
            self.mutable_locals = mutable
        cast("set[str]", node["remaining"]).update(self.uninitialized_out_params)
        cast("set[str | None]", node["exits"]).add(control)
        control_code = {None: 0, "break": 1, "continue": 2}[control]
        result = _Binding(_term("nat", value=control_code), _NAT)
        return self._pack_guard_state(cast("tuple[str, ...]", node["mutable"]), after, result)

    @staticmethod
    def _pack_guard_state(names: tuple[str, ...], after: dict[str, _Binding], result: _Binding) -> _Binding:
        for name in reversed(names):
            value = after[name]
            result = _Binding(
                _term("pair", value.type, result.type, value.term, result.term),
                _term("prod", value.type, result.type),
            )
        return result

    def _unpack_guard_state(
        self: _Elaborator, names: tuple[str, ...], environment: dict[str, _Binding], result: _Binding,
    ) -> tuple[dict[str, _Binding], _Binding]:
        after = dict(environment)
        for name in names:
            value_type, tail_type = result.type.args
            after[name] = _Binding(self.whnf(_apps(_constant("Fst"), value_type, tail_type, result.term)), value_type)
            result = _Binding(self.whnf(_apps(_constant("Snd"), value_type, tail_type, result.term)), tail_type)
        return after, result

    def _guard_non_returning(
        self: _Elaborator, statement: Node, operands: list[Node], environment: dict[str, _Binding],
        facts: tuple[_Binding, ...],
    ) -> tuple[dict[str, _Binding], str | None]:
        names = tuple(name for name in environment if name in self.mutable_locals)
        remaining: set[str] = set()
        exits: set[str | None] = set()

        def state(raw: object) -> Node:
            body = [] if raw is None else [self.node(raw)]
            return {
                "kind": "guard_block_state", "span": statement["span"], "mutable": names, "facts": facts,
                "body": {"kind": "block", "span": statement["span"], "statements": body},
                "remaining": remaining, "exits": exits,
            }

        expr = self._guard_conditional(
            statement, operands, state(statement["then"]), state(statement["else"]), environment,
        )
        result = self.if_expression(expr, environment)
        self.uninitialized_out_params = remaining
        after, result = self._unpack_guard_state(names, environment, result)
        if len(exits) == 1:
            return after, next(iter(exits))
        control = self.whnf(result.term)
        if control.kind == "nat":
            return after, {0: None, 1: "break", 2: "continue"}[cast("int", control.value)]
        for code, outcome in ((0, None), (1, "break"), (2, "continue")):
            if self._prove_bool_precondition(_apps(_constant("eq_nat"), control, _term("nat", value=code)), after):
                return after, outcome
        raise self.fail("unsupported", "symbolic pattern-dependent loop control requires the full frontend", statement)

    def _guard_return(
        self: _Elaborator, statement: Node, operands: list[Node], environment: dict[str, _Binding],
        expected: _Term | None, facts: tuple[_Binding, ...],
    ) -> _Binding:
        names = tuple(name for name in self.entry_env if name in self.mutable_locals and name in environment)

        def branch(raw: object) -> Node:
            return {"kind": "guard_return", "span": statement["span"], "body": self.node(raw),
                    "mutable": names, "expected": expected, "facts": facts}

        guarded = self._guard_conditional(
            statement, operands, branch(statement["then"]), branch(statement["else"]), environment,
        )
        packed = self.if_expression(guarded, environment)
        self.final_ref_bindings, result = self._unpack_guard_state(names, environment, packed)
        self.final_return_facts = []
        return result

    def _fallible_out_hint(self: _Elaborator, result_type: _Term) -> str:
        if self._is_propagatable_union(result_type):
            return ". For a fallible constructor, return the completed value in the success case"
        return ""

    def _is_propagatable_union(self: _Elaborator, value_type: _Term) -> bool:
        resolved = self.whnf(value_type)
        head, _ = self.spine(resolved)
        if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.unions_by_type:
            return False
        union_info = self.unions_by_type[head.value]
        return union_info.propagation is not None

    @staticmethod
    def _with_node_field(node: Node, key: str, value: object) -> Node:
        copied = dict(node)
        copied[key] = value
        return copied

    @classmethod
    def _make_list_rebuilder(
        cls, node: Node, key: str, items: list[Node], idx: int, inner_rebuild: Callable[[Node], Node]
    ) -> Callable[[Node], Node]:
        return lambda repl: cls._with_node_field(
            node, key, [*items[:idx], inner_rebuild(repl), *items[idx + 1:]]
        )

    @classmethod
    def _make_nested_list_rebuilder(
        cls,
        node: Node,
        key: str,
        items: list[Node],
        idx: int,
        item_node: Node,
        child_key: str,
        inner_rebuild: Callable[[Node], Node],
    ) -> Callable[[Node], Node]:
        return lambda repl: cls._with_node_field(
            node,
            key,
            [*items[:idx], cls._with_node_field(item_node, child_key, inner_rebuild(repl)), *items[idx + 1:]],
        )

    def _has_order_sensitive_evaluation(self: _Elaborator, node: Node) -> bool:
        self.tick()
        if node.get("kind") in {"call", "block"}:
            return True
        if node.get("kind") == "unary" and self.operator(node["operator"]) in {"in", "ref", "out", "move"}:
            return True
        for value in node.values():
            if isinstance(value, dict) and self._has_order_sensitive_evaluation(value):
                return True
            if isinstance(value, list) and any(
                self._has_order_sensitive_evaluation(item) for item in value if isinstance(item, dict)
            ):
                return True
        return False

    def _require_propagation_order(
        self: _Elaborator, earlier: list[Node], propagated: Node, site: Node
    ) -> None:
        if earlier and (
            any(self._has_order_sensitive_evaluation(value) for value in earlier)
            or self._has_order_sensitive_evaluation(propagated)
        ):
            raise self.fail(
                "unsupported",
                "propagation across callable or ownership evaluation requires an explicit earlier local",
                site,
            )

    def _split_first_propagate(self: _Elaborator, node: Node) -> tuple[Node, Callable[[Node], Node]] | None:
        kind = node["kind"]
        if kind == "propagate":
            res_inner = self._split_first_propagate(self.node(node["value"]))
            if res_inner is not None:
                prop, inner_rebuild = res_inner
                return prop, lambda repl: self._with_node_field(node, "value", inner_rebuild(repl))
            return node, lambda repl: repl
        if kind in {"group", "unary", "member", "is", "generic_application", "expression_body"}:
            res = self._split_first_propagate(self.node(node["value"]))
            if res is not None:
                prop, inner_rebuild = res
                return prop, lambda repl: self._with_node_field(node, "value", inner_rebuild(repl))
            return None
        if kind == "binary":
            res_l = self._split_first_propagate(self.node(node["left"]))
            if res_l is not None:
                prop, inner_rebuild = res_l
                return prop, lambda repl: self._with_node_field(node, "left", inner_rebuild(repl))
            res_r = self._split_first_propagate(self.node(node["right"]))
            if res_r is not None:
                if self.operator(node["operator"]) in {"&&", "||"}:
                    # The RHS early exit belongs inside the Boolean guard.
                    return node, lambda repl: repl
                self._require_propagation_order([self.node(node["left"])], self.node(node["right"]), node)
                prop, inner_rebuild = res_r
                return prop, lambda repl: self._with_node_field(node, "right", inner_rebuild(repl))
            return None
        if kind == "tuple":
            vals = self.nodes(node["values"])
            for i, v in enumerate(vals):
                res = self._split_first_propagate(v)
                if res is not None:
                    self._require_propagation_order(vals[:i], v, node)
                    prop, inner_rebuild = res
                    return prop, self._make_list_rebuilder(node, "values", vals, i, inner_rebuild)
            return None
        if kind == "call":
            res_c = self._split_first_propagate(self.node(node["callee"]))
            if res_c is not None:
                prop, inner_rebuild = res_c
                return prop, lambda repl: self._with_node_field(node, "callee", inner_rebuild(repl))
            args = self.nodes(node["arguments"])
            for i, a in enumerate(args):
                res_a = self._split_first_propagate(self.node(a["value"]))
                if res_a is not None:
                    callee = self.node(node["callee"])
                    plain_callee = callee
                    while plain_callee["kind"] in {"group", "generic_application"}:
                        plain_callee = self.node(plain_callee["value"])
                    stable_callee = (plain_callee["kind"] == "name"
                                     and self.name(plain_callee["name"]) not in self.mutable_locals)
                    earlier = [] if stable_callee else [callee]
                    earlier.extend(self.node(arg["value"]) for arg in args[:i])
                    self._require_propagation_order(earlier, self.node(a["value"]), node)
                    prop, inner_rebuild = res_a
                    return prop, self._make_nested_list_rebuilder(node, "arguments", args, i, a, "value", inner_rebuild)
            return None
        if kind == "with_expression":
            res_v = self._split_first_propagate(self.node(node["value"]))
            if res_v is not None:
                prop, inner_rebuild = res_v
                return prop, lambda repl: self._with_node_field(node, "value", inner_rebuild(repl))
            upds = self.nodes(node["updates"])
            for i, u in enumerate(upds):
                res_u = self._split_first_propagate(self.node(u["value"]))
                if res_u is not None:
                    self._require_propagation_order(
                        [self.node(node["value"]), *(self.node(upd["value"]) for upd in upds[:i])],
                        self.node(u["value"]), node,
                    )
                    prop, inner_rebuild = res_u
                    return prop, self._make_nested_list_rebuilder(node, "updates", upds, i, u, "value", inner_rebuild)
            return None
        if kind == "if_expression":
            if self._pattern_conjuncts(self.node(node["condition"])):
                # Each operand's propagation is handled inside its successful guards.
                return None
            res_cond = self._split_first_propagate(self.node(node["condition"]))
            if res_cond is not None:
                prop, inner_rebuild = res_cond
                return prop, lambda repl: self._with_node_field(node, "condition", inner_rebuild(repl))
            return None
        if kind == "match_expression":
            res_val = self._split_first_propagate(self.node(node["value"]))
            if res_val is not None:
                prop, inner_rebuild = res_val
                return prop, lambda repl: self._with_node_field(node, "value", inner_rebuild(repl))
            return None
        if kind == "let_expression":
            bnode = self.node(node["binding"])
            if bnode.get("value") is not None:
                res_b = self._split_first_propagate(self.node(bnode["value"]))
                if res_b is not None:
                    prop, inner_rebuild = res_b
                    return prop, lambda repl: self._with_node_field(
                        node, "binding", self._with_node_field(bnode, "value", inner_rebuild(repl))
                    )
            return None
        if kind == "index":
            res_v = self._split_first_propagate(self.node(node["value"]))
            if res_v is not None:
                prop, inner_rebuild = res_v
                return prop, lambda repl: self._with_node_field(node, "value", inner_rebuild(repl))
            res_i = self._split_first_propagate(self.node(node["index"]))
            if res_i is not None:
                self._require_propagation_order([self.node(node["value"])], self.node(node["index"]), node)
                prop, inner_rebuild = res_i
                return prop, lambda repl: self._with_node_field(node, "index", inner_rebuild(repl))
            return None
        return None

    def _elaborate_propagate(
        self: _Elaborator,
        prop_node: Node,
        environment: dict[str, _Binding],
        target_return_type: _Term,
        continuation: Callable[[str, _Binding, dict[str, _Binding]], _Term],
    ) -> _Term:
        self.site = prop_node
        if prop_node["kind"] == "binary":
            return self._elaborate_short_circuit_propagate(
                prop_node, environment, target_return_type, continuation
            )
        if self.active_lift_scopes > 0:
            debts = sorted(f"{owner}.{clause}" for owner, clauses in self.lifted_invariants.items() for clause in clauses)
            raise self.fail(
                "type",
                "cannot propagate '?' early exit while a record invariant is lifted in an enclosing scope: "
                + ", ".join(debts),
                prop_node,
            )
        if self.uninitialized_out_params:
            names = ", ".join(repr(name) for name in sorted(self.uninitialized_out_params))
            owed = (f"'out' parameter {names} is" if len(self.uninitialized_out_params) == 1
                    else f"'out' parameters {names} are")
            raise self.fail(
                "type",
                f"cannot propagate '?' early exit before {owed} initialized"
                + self._fallible_out_hint(target_return_type),
                prop_node,
            )
        scrutinee = self.expression(self.node(prop_node["value"]), environment)
        scrut_type = self.whnf(scrutinee.type)
        scrut_head, scrut_type_args = self.spine(scrut_type)
        if (
            scrut_head.kind != "const"
            or not isinstance(scrut_head.value, str)
            or scrut_head.value not in self.unions_by_type
        ):
            raise self.fail(
                "type",
                "'?' operator requires an Option (None/Some) or Result (Err/Ok) union operand",
                prop_node,
            )
        union_info = self.unions_by_type[scrut_head.value]
        if union_info.propagation is None:
            raise self.fail(
                "type",
                "'?' operator requires the standard Option or Result declaration",
                prop_node,
            )
        ok_idx, err_idx = union_info.propagation
        ret_type = self.whnf(target_return_type)
        ret_head, ret_type_args = self.spine(ret_type)
        if (
            ret_head.kind != "const"
            or not isinstance(ret_head.value, str)
            or ret_head.value != scrut_head.value
            or not self._is_propagatable_union(ret_type)
        ):
            raise self.fail(
                "type",
                "'?' propagation requires an enclosing callable or block returning a compatible Option or Result union",
                prop_node,
            )
        inst_payload_types = [
            self._instantiate_generic_type(union_info.generic_vars, scrut_type_args, c.payload_type)
            for c in union_info.constructors
        ]
        err_ctor = union_info.constructors[err_idx]
        err_var = self.fresh(inst_payload_types[err_idx])
        if not err_ctor.fields:
            early_return_term = _apps(_constant(err_ctor.ctor_const), *ret_type_args, _term("unit"))
        else:
            ret_err_type = self._instantiate_generic_type(
                union_info.generic_vars, ret_type_args, err_ctor.payload_type
            )
            self.unify(inst_payload_types[err_idx], ret_err_type)
            early_return_term = _apps(_constant(err_ctor.ctor_const), *ret_type_args, err_var)
        ok_type = inst_payload_types[ok_idx]
        ok_var = self.fresh(ok_type)
        temp_name = f"__holdfast_prop_{ok_var.value}"
        ok_binding = _Binding(ok_var, ok_type)
        ok_env = dict(environment)
        ok_env[temp_name] = ok_binding
        ok_branch_term = continuation(temp_name, ok_binding, ok_env)
        scrut_var = self.fresh(scrut_type)
        motive_lam = _term("lam", scrut_type, target_return_type, value=scrut_var.value)
        if ok_idx == 0:
            left_lam = _term("lam", ok_type, ok_branch_term, value=ok_var.value)
            right_lam = _term("lam", inst_payload_types[1], early_return_term, value=err_var.value)
        else:
            left_lam = _term("lam", inst_payload_types[0], early_return_term, value=err_var.value)
            right_lam = _term("lam", ok_type, ok_branch_term, value=ok_var.value)
        return _term("sum_match", motive_lam, scrutinee.term, left_lam, right_lam)

    def _elaborate_short_circuit_propagate(
        self: _Elaborator,
        node: Node,
        environment: dict[str, _Binding],
        target_return_type: _Term,
        continuation: Callable[[str, _Binding, dict[str, _Binding]], _Term],
    ) -> _Term:
        if operands := self._pattern_conjuncts(node):
            if self.mutable_locals.intersection(self.entry_env):
                raise self.fail("unsupported", "propagating a pattern guard with borrowed outputs requires "
                                "an explicit control-flow branch", node)
            enclosing_guard = self.guard_value

            def resume_guard(truth: bool, branch: dict[str, _Binding]) -> _Term:
                value = _Binding(_term("bool", value=int(truth)), _BOOL)
                name = f"__holdfast_bool_{self.fresh(_BOOL).value}"
                outer = {key: branch[key] for key in environment}
                saved = self.guard_value
                self.guard_value = enclosing_guard
                try:
                    return continuation(name, value, {**outer, name: value})
                finally:
                    self.guard_value = saved

            resume_node: Node = {
                "kind": "guard_resume", "span": node["span"], "resume": resume_guard, "type": target_return_type,
            }
            guarded = self._guard_conditional(
                node, operands, {**resume_node, "truth": True}, {**resume_node, "truth": False},
                environment,
            )
            return self._check_guard_value(guarded, environment, target_return_type).term
        condition = self.check(self.node(node["left"]), _BOOL, environment)
        branch_env = dict(environment)
        self._consume_call_updates(branch_env, node)

        def resume(value: _Term, extended: dict[str, _Binding]) -> _Term:
            variable = self.fresh(_BOOL)
            name = f"__holdfast_bool_{variable.value}"
            binding = _Binding(variable, _BOOL)
            next_env = {**extended, name: binding}
            body = continuation(name, binding, next_env)
            return _term("let", _BOOL, value, body, value=variable.value)

        def evaluate_right(value_node: Node, extended: dict[str, _Binding]) -> _Term:
            split = self._split_first_propagate(value_node)
            if split is None:
                return resume(self.check(value_node, _BOOL, extended), extended)
            prop, rebuild = split
            return self._elaborate_propagate(
                prop, extended, target_return_type,
                lambda name, _binding, next_env: evaluate_right(
                    rebuild({"kind": "name", "span": prop["span"],
                             "name": {"text": name, "span": prop["span"]}}),
                    next_env,
                ),
            )

        saved_uninit = set(self.uninitialized_out_params)
        branches: list[_Term] = []
        branch_refs: list[dict[str, _Binding]] = []
        branch_uninit: list[set[str]] = []
        for truth in (True, False):
            self.uninitialized_out_params = set(saved_uninit)
            self.active_facts.append(condition if truth else _app(_constant("!"), condition))
            try:
                if truth == (self.operator(node["operator"]) == "&&"):
                    branches.append(evaluate_right(self.node(node["right"]), dict(branch_env)))
                else:
                    branches.append(resume(_term("bool", value=int(truth)), dict(branch_env)))
                branch_refs.append(dict(self.final_ref_bindings))
                branch_uninit.append(set(self.uninitialized_out_params))
            finally:
                self.active_facts.pop()
        self.uninitialized_out_params = branch_uninit[0] | branch_uninit[1]
        self.final_ref_bindings = dict(branch_env)
        for name in branch_refs[0].keys() & branch_refs[1].keys():
            yes, no = branch_refs[0][name], branch_refs[1][name]
            self.final_ref_bindings[name] = (yes if yes.term == no.term else _Binding(
                self.whnf(_term("if", yes.type, condition, yes.term, no.term)), yes.type
            ))
        return _term("if", target_return_type, condition, *branches)

    def _check_record_invariants(
        self: _Elaborator,
        record_info: _RecordInfo,
        type_args: list[_Term],
        rec_term: _Term,
        environment: dict[str, _Binding],
        site: Node | None,
        *,
        only_clauses: set[str] | None = None,
        exclude_clauses: set[str] | None = None,
    ) -> None:
        if not record_info.invariants:
            return
        for inv in record_info.invariants:
            if only_clauses is not None and inv.name not in only_clauses:
                continue
            if exclude_clauses is not None and inv.name in exclude_clauses:
                continue
            inst_term = self._instantiate_record_type(record_info, type_args, inv.term)
            inst_term = self.substitute(inst_term, cast("int", inv.self_var.value), rec_term)
            inst_type = self._instantiate_record_type(record_info, type_args, inv.type)
            inst_type = self.substitute(inst_type, cast("int", inv.self_var.value), rec_term)
            clause_label = "" if inv.name.startswith("__anon_") else f" '{inv.name}'"
            if self.whnf(inst_type) == _BOOL:
                if not self._prove_bool_precondition(inst_term, environment):
                    raise self.fail(
                        "type",
                        f"record '{record_info.name}' invariant{clause_label} could not be established",
                        site if site is not None else self.site,
                    )
            else:
                self._prove_proposition(
                    inst_term,
                    environment,
                    (),
                    site if site is not None else cast("Node", self.site),
                )

    def _restore_slice_view_to_parent(
        self: _Elaborator,
        view_name: str,
        new_view_term: _Term,
        updated: dict[str, _Binding],
        *,
        span_write_idx: _Term | None = None,
        span_write_val: _Term | None = None,
    ) -> None:
        if view_name not in self.slice_views:
            return
        parent_name = self.slice_views[view_name]
        if parent_name not in updated:
            return
        p_b = updated[parent_name]
        if span_write_idx is not None and span_write_val is not None:
            ext = self._span_extent_in_owner(new_view_term, self._root_span(p_b.term))
            if ext is not None:
                owner_idx = self._add_usize_offset(ext[0], span_write_idx)
            else:
                base_diff = _apps(
                    _constant("int_sub_usize"),
                    _apps(_constant("Span_Base"), _U8, new_view_term),
                    _apps(_constant("Span_Base"), _U8, p_b.term),
                )
                owner_idx = self._add_usize_offset(base_diff, span_write_idx)
            new_parent_term = _apps(_constant("Span_Write"), _U8, p_b.term, owner_idx, span_write_val)
        else:
            new_parent_term = _apps(_constant("Span_Restore"), _U8, p_b.term, new_view_term)
        updated[parent_name] = _Binding(new_parent_term, p_b.type)
        self.slice_view_own_updates.setdefault(view_name, set()).add(id(new_parent_term))
        if parent_name in self.slice_views:
            self._restore_slice_view_to_parent(
                parent_name,
                new_parent_term,
                updated,
                span_write_idx=span_write_idx,
                span_write_val=span_write_val,
            )

    def _build_collection_element_write(
        self: _Elaborator,
        col_b: _Binding,
        idx_node: Node,
        rhs_b_fn: Callable[[_Term], _Term],
        updated: dict[str, _Binding],
        site: Node,
    ) -> _Binding:
        cur_type = self.whnf(col_b.type)
        head, type_args = self.spine(cur_type)
        if head == _constant("Span") and len(type_args) == 1 and self.whnf(type_args[0]) == _U8:
            idx_t = self.check(idx_node, _USIZE, updated)
            self._check_span_can_write(col_b.term, updated, site)
            len_t = _apps(_constant("Span_Length"), _U8, col_b.term)
            in_bounds = _apps(_constant("int_lt_usize"), idx_t, len_t)
            if not self._prove_bool_precondition(in_bounds, updated):
                raise self.fail(
                    "type",
                    "cannot prove Span indexed write is in bounds (index < span.Length)",
                    site,
                )
            old_elem = _apps(_constant("Span_Read"), _U8, col_b.term, idx_t)
            rhs_t = rhs_b_fn(old_elem)
            return _Binding(_apps(_constant("Span_Write"), _U8, col_b.term, idx_t, rhs_t), col_b.type)
        if head == _constant("Slots") and len(type_args) == 2:
            elem_t, cap_t = type_args[0], type_args[1]
            idx_t = self._slots_usize_arg(idx_node, updated)
            can_w = _apps(_constant("Slots_CanWrite"), elem_t, cap_t, col_b.term)
            if not self._prove_bool_precondition(can_w, updated):
                raise self.fail(
                    "type",
                    "cannot prove Slots has valid tag and write permission (Slots.CanWrite)",
                    site,
                )
            live_t = _apps(_constant("Slots_LiveCount"), elem_t, cap_t, col_b.term)
            lt_live = _apps(_constant("int_lt_usize"), idx_t, live_t)
            eq_live = _apps(_constant("int_eq_usize"), idx_t, live_t)
            cap_u = self._slots_cap_usize_term(cap_t)
            lt_cap = (
                _apps(_constant("int_lt_usize"), idx_t, cap_u)
                if self.whnf(cap_u).kind == "int"
                else _apps(_constant("<"), _app(_constant("int_to_nat_usize"), idx_t), cap_t)
            )
            if not (
                self._prove_bool_precondition(lt_live, updated)
                or (
                    self._prove_bool_precondition(eq_live, updated)
                    and self._prove_bool_precondition(lt_cap, updated)
                )
            ):
                raise self.fail(
                    "type",
                    "cannot prove Slots indexed write is in bounds (index < LiveCount or (index == LiveCount and index < capacity))",
                    site,
                )
            d_val = self._sequence_lookup_default(elem_t, _apps(_constant("Slots_Model"), elem_t, cap_t, col_b.term))
            old_elem = _apps(_constant("Slots_Read"), elem_t, cap_t, d_val, col_b.term, idx_t)
            rhs_t = rhs_b_fn(old_elem)
            return _Binding(_apps(_constant("Slots_Write"), elem_t, cap_t, col_b.term, idx_t, rhs_t), col_b.type)
        if head == _constant("Seq") and len(type_args) == 1:
            elem_t = type_args[0]
            cnt_t = _apps(_constant("Seq_Count"), elem_t, col_b.term)
            idx_nat = self._nat_or_usize_index(idx_node, updated, "Seq")
            in_bounds = _apps(_constant("<"), idx_nat, cnt_t)
            if not self._prove_bool_precondition(in_bounds, updated):
                raise self.fail(
                    "type",
                    "cannot prove Seq indexed write is in bounds (index < seq.Count)",
                    site,
                )
            d_val = self._sequence_lookup_default(elem_t, col_b.term)
            old_elem = _apps(_constant("Seq_At"), elem_t, d_val, col_b.term, idx_nat)
            rhs_t = rhs_b_fn(old_elem)
            return _Binding(_apps(_constant("Seq_Update"), elem_t, col_b.term, idx_nat, rhs_t), col_b.type)
        if head == _constant("Vec") and len(type_args) == 2:
            elem_t, len_t = type_args[0], type_args[1]
            idx_nat = self._nat_or_usize_index(idx_node, updated, "Vec")
            in_bounds = _apps(_constant("<"), idx_nat, len_t)
            if not self._prove_bool_precondition(in_bounds, updated):
                raise self.fail(
                    "type",
                    "cannot prove Vec indexed write is in bounds (index < n)",
                    site,
                )
            d_val = self._default_term_for_type(elem_t)
            old_elem = _apps(_constant("Vec_At_Nat"), elem_t, len_t, d_val, idx_nat, col_b.term)
            rhs_t = rhs_b_fn(old_elem)
            return _Binding(_apps(_constant("Vec_Update"), elem_t, len_t, idx_nat, rhs_t, col_b.term), col_b.type)
        raise self.fail(
            "type",
            "indexed assignment target must have type Span<byte>, Slots<T, capacity>, Seq<T> or Vec<T, n>",
            site,
        )

    def _elaborate_assignment(self: _Elaborator, statement: Node, extended: dict[str, _Binding]) -> dict[str, _Binding]:
        self.site = statement
        target = self._unwrap_group(self.node(statement["target"]))
        self._note_runtime_write(target)
        raw_op = statement["operator"]
        if (
            not isinstance(raw_op, dict)
            or not isinstance(raw_op.get("text"), str)
            or raw_op["text"] not in _ASSIGN_OPERATORS
        ):
            raise self.fail("protocol", "expected a supported assignment operator", statement)
        op = cast("str", raw_op["text"])
        val_node = self.node(statement["value"])
        updated = dict(extended)
        if target["kind"] == "name":
            tname = self.name(target["name"])
            if tname not in updated:
                raise self.fail("name", f"unknown identifier '{tname}'", target)
            if op == "=" and self._is_reborrow_assignment(tname, val_node):
                if tname in self.frozen_collections:
                    raise self.fail("type", f"cannot mutate collection '{tname}' while iterating over it", statement)
                return self._elaborate_reborrow_assignment(tname, val_node, updated, statement)
            if tname in self.frozen_collections:
                raise self.fail("type", f"cannot mutate collection '{tname}' while iterating over it", statement)
            if tname in self.local_borrows and self.local_borrows[tname][0] not in {"ref", "shared_ref"}:
                raise self.fail(
                    "type",
                    f"cannot assign through shared 'in' borrow '{tname}' (write-through-shared)",
                    target,
                )
            if tname in self.indexed_local_borrows and self.indexed_local_borrows[tname].mode != "ref":
                raise self.fail(
                    "type",
                    f"cannot assign through shared 'in' borrow '{tname}' (write-through-shared)",
                    target,
                )
            if (
                tname not in self.mutable_locals
                and tname not in self.shared_ref_locals
                and tname not in self.prophecy_borrows
            ):
                raise self.fail(
                    "type",
                    f"cannot assign to immutable binding '{tname}'; declare it with 'var' or 'ref'",
                    target,
                )
            if tname in self.invalidated_prophecy_borrows:
                raise self.fail(
                    "type",
                    f"cannot use returned borrow '{tname}' after owner '{self.invalidated_prophecy_borrows[tname]}' was mutated (conflicting-access)",
                    target,
                )
            if tname not in self.prophecy_borrows:
                self._invalidate_prophecy_borrows_for_owner(tname)
            if tname in self.active_lambda_outer_mutables:
                raise self.fail("type", f"cannot mutate outer variable '{tname}' inside higher-ranked callback", statement)
            if tname in self.local_borrows:
                self._refresh_local_borrows(updated, target)
            elif tname in self.indexed_local_borrows:
                self._check_indexed_local_borrow_access(tname, updated, target)
            cur_b = updated[tname]
            if self._is_readonly_span(cur_b.term):
                raise self.fail("type", f"cannot mutate a read-only 'in' parameter '{tname}'", target)
            if op == "=":
                prev_assign_target = self._in_lifted_target_assignment
                self._in_lifted_target_assignment = tname
                try:
                    rhs_term = self.check(val_node, cur_b.type, updated)
                finally:
                    self._in_lifted_target_assignment = prev_assign_target
                self._consume_call_updates(updated, statement)
                self.uninitialized_out_params.discard(tname)
            else:
                if tname in self.uninitialized_out_params:
                    raise self.fail(
                        "type",
                        f"cannot apply compound assignment '{op}' to uninitialized 'out' parameter '{tname}'",
                        target,
                    )
                bin_op = op[:-1]
                bin_node: Node = {
                    "kind": "binary",
                    "span": statement["span"],
                    "operator": {"text": bin_op, "span": cast("Node", statement["operator"])["span"]},
                    "left": target,
                    "right": val_node,
                }
                rhs_term = self.check(bin_node, cur_b.type, updated)
                self._consume_call_updates(updated, statement)
            if (rhs_hr := self._term_hr_region(rhs_term, updated)) is not None:
                cur_hr = self.local_value_regions.get(tname)
                if cur_hr is None or cur_hr[1] != rhs_hr:
                    raise self.fail(
                        "type",
                        f"cannot assign value from higher-ranked callback region to outer binding '{tname}'",
                        statement,
                    )
            if tname in self.prophecy_borrows:
                self._apply_prophecy_write(tname, _Binding(rhs_term, cur_b.type), updated, statement)
                return updated
            if tname in self.local_borrows:
                self._apply_borrow_write(tname, _Binding(rhs_term, cur_b.type), updated, statement)
                return updated
            if tname in self.indexed_local_borrows:
                self._apply_indexed_borrow_write(tname, _Binding(rhs_term, cur_b.type), updated, statement)
                return updated
            rec_head, rec_targs = self.spine(self.whnf(cur_b.type))
            if (
                rec_head.kind == "const"
                and isinstance(rec_head.value, str)
                and rec_head.value in self.records_by_type
            ):
                rinfo = self.records_by_type[rec_head.value]
                lifted = self.lifted_invariants.get(tname, set())
                self._check_record_invariants(
                    rinfo, rec_targs, rhs_term, updated, statement, exclude_clauses=lifted
                )
            elif (
                rec_head.kind == "const"
                and isinstance(rec_head.value, str)
                and rec_head.value in self.unions_by_type
            ):
                uinfo = self.unions_by_type[rec_head.value]
                self._check_union_tag_preserved(tname, cur_b.term, rhs_term, uinfo, updated)
            self._clear_partial_move_on_write(tname, ())
            updated[tname] = _Binding(rhs_term, cur_b.type)
            if tname in self.shared_ref_locals:
                if not self._is_shape_stable_type(cur_b.type) and tname not in {
                    p.owner for p in self.proved_tag_preserved_places
                }:
                    raise self.fail(
                        "type",
                        f"unstable write through 'shared ref' binding '{tname}' requires a shape-stable or tag-preserved proof (unstable-shared-mut-write)",
                        statement,
                    )
                self._purge_overlapping_facts_on_shared_write(tname, (), None, updated)
                self._refresh_shared_mut_aliases(tname, updated, statement)
            else:
                self._refresh_local_borrows(updated, statement)
            return updated
        if target["kind"] == "member":
            recv_node = self._unwrap_group(self.node(target["value"]))
            fname = self.name(target["name"])
            if recv_node["kind"] == "index":
                index_chain: list[Node] = []
                cur_idx_n = recv_node
                while cur_idx_n["kind"] == "index":
                    index_chain.append(cur_idx_n)
                    cur_idx_n = self._unwrap_group(self.node(cur_idx_n["value"]))
                index_chain.reverse()
                if cur_idx_n["kind"] != "name":
                    raise self.fail("type", "member assignment requires a named record variable target", target)
                rname = self.name(cur_idx_n["name"])
                if rname not in updated:
                    raise self.fail("name", f"unknown identifier '{rname}'", cur_idx_n)
                if rname in self.frozen_collections:
                    raise self.fail("type", f"cannot mutate collection '{rname}' while iterating over it", statement)
                if rname in self.uninitialized_out_params:
                    raise self.fail(
                        "type",
                        f"cannot mutate field '{fname}' of uninitialized 'out' parameter '{rname}'; initialize the whole value first",
                        target,
                    )
                if rname in self.local_borrows and self.local_borrows[rname][0] != "ref":
                    raise self.fail(
                        "type",
                        f"cannot mutate field '{fname}' through shared 'in' borrow '{rname}' (write-through-shared)",
                        target,
                    )
                if rname in self.indexed_local_borrows and self.indexed_local_borrows[rname].mode != "ref":
                    raise self.fail(
                        "type",
                        f"cannot mutate field '{fname}' through shared 'in' borrow '{rname}' (write-through-shared)",
                        target,
                    )
                if rname not in self.mutable_locals:
                    raise self.fail(
                        "type",
                        f"cannot mutate field '{fname}' of immutable record '{rname}'; declare it with 'var' or 'ref'",
                        target,
                    )
                if rname in self.local_borrows:
                    self._refresh_local_borrows(updated, target)
                elif rname in self.indexed_local_borrows:
                    self._check_indexed_local_borrow_access(rname, updated, target)
                cur_b = updated[rname]
                if self._is_readonly_span(cur_b.term):
                    raise self.fail("type", f"cannot mutate a read-only 'in' parameter '{rname}'", target)
                rhs_expr_m: Node = (
                    val_node
                    if op == "="
                    else {
                        "kind": "binary",
                        "span": statement["span"],
                        "operator": {"text": op[:-1], "span": cast("Node", statement["operator"])["span"]},
                        "left": target,
                        "right": val_node,
                    }
                )
                rhs_b_val = self.expression(rhs_expr_m, updated)
                self._consume_call_updates(updated, statement)

                def apply_member_at_chain(col_b: _Binding, chain_idx: int) -> _Binding:
                    if chain_idx == len(index_chain):
                        rec_type_m = self.whnf(col_b.type)
                        m_head, m_targs = self.spine(rec_type_m)
                        if (
                            m_head.kind != "const"
                            or not isinstance(m_head.value, str)
                            or m_head.value not in self.records_by_type
                        ):
                            raise self.fail("type", f"member assignment target '{rname}' must be a record", target)
                        record_info_m = self.records_by_type[m_head.value]
                        f_index = next((idx for idx, rf in enumerate(record_info_m.fields) if rf.name == fname), None)
                        if f_index is None:
                            raise self.fail("name", f"record '{record_info_m.name}' has no mutable field '{fname}'", target)
                        final_fields_m: list[_Term] = []
                        for idx, rf in enumerate(record_info_m.fields):
                            ftype = self._instantiate_record_type(record_info_m, m_targs, rf.type)
                            for j in range(idx):
                                ftype = self.substitute(ftype, cast("int", record_info_m.fields[j].var.value), final_fields_m[j])
                            if idx == f_index:
                                self.unify(rhs_b_val.type, ftype)
                                final_fields_m.append(rhs_b_val.term)
                            else:
                                old_ftype = self._instantiate_record_field_type(record_info_m, m_targs, idx, col_b.term)
                                if not self._try_unify(old_ftype, ftype):
                                    raise self.fail(
                                        "type",
                                        f"field assignment changes an index that field '{rf.name}' depends on; use 'with' to update dependent fields together",
                                        statement,
                                    )
                                final_fields_m.append(_apps(_constant(rf.proj_const), *m_targs, col_b.term))
                        new_rec = _apps(_constant(record_info_m.ctor_const), *m_targs, *final_fields_m)
                        self._check_record_invariants(record_info_m, m_targs, new_rec, updated, statement)
                        return _Binding(new_rec, col_b.type)
                    idx_node_cur = self.node(index_chain[chain_idx]["index"])
                    cur_head, cur_targs = self.spine(self.whnf(col_b.type))
                    if (
                        (cur_head == _constant("Vec") and len(cur_targs) == 2)
                        or (cur_head == _constant("Seq") and len(cur_targs) == 1)
                        or (cur_head == _constant("Slots") and len(cur_targs) == 2)
                    ):
                        sub_ty = cur_targs[0]
                    else:
                        raise self.fail("type", "indexed record assignment requires Vec, Seq, or Slots", target)
                    return self._build_collection_element_write(
                        col_b,
                        idx_node_cur,
                        lambda old_elem: apply_member_at_chain(_Binding(old_elem, sub_ty), chain_idx + 1).term,
                        updated,
                        statement,
                    )

                new_col_m = apply_member_at_chain(cur_b, 0)
                if rname in self.local_borrows:
                    self._apply_borrow_write(rname, new_col_m, updated, statement)
                    return updated
                if rname in self.indexed_local_borrows:
                    self._apply_indexed_borrow_write(rname, new_col_m, updated, statement)
                    return updated
                updated[rname] = new_col_m
                self._refresh_local_borrows(updated, statement)
                return updated
            if recv_node["kind"] != "name":
                raise self.fail("type", "member assignment requires a named record variable target", target)
            rname = self.name(recv_node["name"])
            if rname not in updated:
                raise self.fail("name", f"unknown identifier '{rname}'", recv_node)
            if rname in self.frozen_collections:
                raise self.fail("type", f"cannot mutate collection '{rname}' while iterating over it", statement)
            if rname in self.uninitialized_out_params:
                raise self.fail(
                    "type",
                    f"cannot mutate field '{fname}' of uninitialized 'out' parameter '{rname}'; initialize the whole value first",
                    target,
                )
            if rname in self.local_borrows and self.local_borrows[rname][0] not in {"ref", "shared_ref"}:
                raise self.fail(
                    "type",
                    f"cannot mutate field '{fname}' through shared 'in' borrow '{rname}' (write-through-shared)",
                    target,
                )
            if rname in self.indexed_local_borrows and self.indexed_local_borrows[rname].mode != "ref":
                raise self.fail(
                    "type",
                    f"cannot mutate field '{fname}' through shared 'in' borrow '{rname}' (write-through-shared)",
                    target,
                )
            if rname not in self.mutable_locals and rname not in self.shared_ref_locals:
                raise self.fail(
                    "type",
                    f"cannot mutate field '{fname}' of immutable record '{rname}'; declare it with 'var' or 'ref'",
                    target,
                )
            if rname in self.local_borrows:
                self._refresh_local_borrows(updated, target)
            elif rname in self.indexed_local_borrows:
                self._check_indexed_local_borrow_access(rname, updated, target)
            cur_b = updated[rname]
            if self._is_readonly_span(cur_b.term):
                raise self.fail("type", f"cannot mutate a read-only 'in' parameter '{rname}'", target)
            rec_type = self.whnf(cur_b.type)
            head, type_args = self.spine(rec_type)
            if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.records_by_type:
                raise self.fail("type", f"member assignment target '{rname}' must be a record", target)
            record_info = self.records_by_type[head.value]
            field_index = next((idx for idx, rf in enumerate(record_info.fields) if rf.name == fname), None)
            if field_index is None:
                raise self.fail("name", f"record '{record_info.name}' has no mutable field '{fname}'", target)
            rhs_expr: Node = (
                val_node
                if op == "="
                else {
                    "kind": "binary",
                    "span": statement["span"],
                    "operator": {"text": op[:-1], "span": cast("Node", statement["operator"])["span"]},
                    "left": target,
                    "right": val_node,
                }
            )
            final_fields: list[_Term] = []
            for idx, rf in enumerate(record_info.fields):
                ftype = self._instantiate_record_type(record_info, type_args, rf.type)
                for j in range(idx):
                    ftype = self.substitute(ftype, cast("int", record_info.fields[j].var.value), final_fields[j])
                if idx == field_index:
                    final_fields.append(self.check(rhs_expr, ftype, updated))
                else:
                    old_ftype = self._instantiate_record_field_type(record_info, type_args, idx, cur_b.term)
                    if not self._try_unify(old_ftype, ftype):
                        raise self.fail(
                            "type",
                            f"field assignment changes an index that field '{rf.name}' depends on; use 'with' to update dependent fields together",
                            statement,
                        )
                    final_fields.append(_apps(_constant(rf.proj_const), *type_args, cur_b.term))
            self._consume_call_updates(updated, statement)
            new_rec_term = _apps(_constant(record_info.ctor_const), *type_args, *final_fields)
            if rname in self.local_borrows:
                self._apply_borrow_write(rname, _Binding(new_rec_term, cur_b.type), updated, statement)
                return updated
            if rname in self.indexed_local_borrows:
                self._apply_indexed_borrow_write(rname, _Binding(new_rec_term, cur_b.type), updated, statement)
                return updated
            lifted = self.lifted_invariants.get(rname, set())
            self._check_record_invariants(
                record_info, type_args, new_rec_term, updated, statement, exclude_clauses=lifted
            )
            self._clear_partial_move_on_write(rname, (fname,))
            self._invalidate_prophecy_borrows_for_owner(rname)
            updated[rname] = _Binding(new_rec_term, cur_b.type)
            if rname in self.shared_ref_locals:
                self._purge_overlapping_facts_on_shared_write(rname, (fname,), None, updated)
                self._refresh_shared_mut_aliases(rname, updated, statement)
            else:
                self._refresh_local_borrows(updated, statement)
            return updated
        if target["kind"] == "index":
            recv_node = self._unwrap_group(self.node(target["value"]))
            idx_node = self.node(target["index"])
            if recv_node["kind"] == "index":
                index_chain_i: list[Node] = [target]
                cur_in = recv_node
                while cur_in["kind"] == "index":
                    index_chain_i.append(cur_in)
                    cur_in = self._unwrap_group(self.node(cur_in["value"]))
                index_chain_i.reverse()
                if cur_in["kind"] != "name":
                    raise self.fail("type", "indexed assignment requires a named mutable variable target", target)
                rname = self.name(cur_in["name"])
                if rname not in updated:
                    raise self.fail("name", f"unknown identifier '{rname}'", cur_in)
                if rname in self.frozen_collections:
                    raise self.fail("type", f"cannot mutate collection '{rname}' while iterating over it", statement)
                if rname in self.uninitialized_out_params:
                    raise self.fail(
                        "type",
                        f"cannot mutate indexed element of uninitialized 'out' parameter '{rname}'; initialize the whole value first",
                        target,
                    )
                if rname in self.indexed_local_borrows:
                    if self.indexed_local_borrows[rname].mode != "ref":
                        raise self.fail(
                            "type",
                            f"cannot mutate indexed element through shared 'in' borrow '{rname}' (write-through-shared)",
                            target,
                        )
                    self._check_indexed_local_borrow_access(rname, updated, target)
                if rname not in self.mutable_locals:
                    raise self.fail(
                        "type",
                        f"cannot mutate indexed element of immutable binding '{rname}'; declare it with 'var' or 'ref'",
                        target,
                    )
                cur_b = updated[rname]
                if self._is_readonly_span(cur_b.term):
                    raise self.fail("type", f"cannot mutate a read-only 'in' parameter '{rname}'", target)
                rhs_expr_i: Node = (
                    val_node
                    if op == "="
                    else {
                        "kind": "binary",
                        "span": statement["span"],
                        "operator": {"text": op[:-1], "span": cast("Node", statement["operator"])["span"]},
                        "left": target,
                        "right": val_node,
                    }
                )
                rhs_b_i = self.expression(rhs_expr_i, updated)
                self._consume_call_updates(updated, statement)

                def apply_nested_write(col_b: _Binding, chain_idx: int) -> _Binding:
                    idx_cur = self.node(index_chain_i[chain_idx]["index"])
                    if chain_idx == len(index_chain_i) - 1:
                        cur_h, cur_ta = self.spine(self.whnf(col_b.type))
                        expected_elem = _U8 if cur_h == _constant("Span") else cur_ta[0]
                        self.unify(rhs_b_i.type, expected_elem)
                        return self._build_collection_element_write(
                            col_b, idx_cur, lambda _old: rhs_b_i.term, updated, statement
                        )
                    cur_h, cur_ta = self.spine(self.whnf(col_b.type))
                    if cur_h not in {_constant("Vec"), _constant("Seq"), _constant("Slots")}:
                        raise self.fail(
                            "type",
                            "nested indexed assignment target must have outer type Vec, Seq, or Slots",
                            target,
                        )
                    sub_ty = cur_ta[0]
                    return self._build_collection_element_write(
                        col_b,
                        idx_cur,
                        lambda old_elem: apply_nested_write(_Binding(old_elem, sub_ty), chain_idx + 1).term,
                        updated,
                        statement,
                    )

                new_nested = apply_nested_write(cur_b, 0)
                if rname in self.indexed_local_borrows:
                    self._apply_indexed_borrow_write(rname, new_nested, updated, statement)
                    return updated
                if rname in self.local_borrows:
                    self._apply_borrow_write(rname, new_nested, updated, statement)
                    return updated
                updated[rname] = new_nested
                return updated
            if recv_node["kind"] != "name":
                raise self.fail("type", "indexed assignment requires a named mutable variable target", target)
            rname = self.name(recv_node["name"])
            if rname not in updated:
                raise self.fail("name", f"unknown identifier '{rname}'", recv_node)
            if rname in self.frozen_collections:
                raise self.fail("type", f"cannot mutate collection '{rname}' while iterating over it", statement)
            if rname in self.uninitialized_out_params:
                raise self.fail(
                    "type",
                    f"cannot mutate indexed element of uninitialized 'out' parameter '{rname}'; initialize the whole value first",
                    target,
                )
            if rname in self.indexed_local_borrows:
                if self.indexed_local_borrows[rname].mode != "ref":
                    raise self.fail(
                        "type",
                        f"cannot mutate indexed element through shared 'in' borrow '{rname}' (write-through-shared)",
                        target,
                    )
                self._check_indexed_local_borrow_access(rname, updated, target)
            if rname not in self.mutable_locals:
                raise self.fail(
                    "type",
                    f"cannot mutate indexed element of immutable binding '{rname}'; declare it with 'var' or 'ref'",
                    target,
                )
            cur_b = updated[rname]
            if self._is_readonly_span(cur_b.term):
                raise self.fail("type", f"cannot mutate a read-only 'in' parameter '{rname}'", target)
            rhs_expr = (
                val_node
                if op == "="
                else {
                    "kind": "binary",
                    "span": statement["span"],
                    "operator": {"text": op[:-1], "span": cast("Node", statement["operator"])["span"]},
                    "left": target,
                    "right": val_node,
                }
            )
            cur_type = self.whnf(cur_b.type)
            head, type_args = self.spine(cur_type)
            span_idx_t: _Term | None = None
            span_rhs_t: _Term | None = None
            if head == _constant("Span") and len(type_args) == 1 and self.whnf(type_args[0]) == _U8:
                span_idx_t = self.check(idx_node, _USIZE, updated)
                span_rhs_t = self.check(rhs_expr, _U8, updated)
                self._check_span_can_write(cur_b.term, updated, statement)
                len_t = _apps(_constant("Span_Length"), _U8, cur_b.term)
                in_bounds = _apps(_constant("int_lt_usize"), span_idx_t, len_t)
                if not self._prove_bool_precondition(in_bounds, updated):
                    raise self.fail(
                        "type",
                        "cannot prove Span indexed write is in bounds (index < span.Length)",
                        statement,
                    )
                new_col_b = _Binding(
                    _apps(_constant("Span_Write"), _U8, cur_b.term, span_idx_t, span_rhs_t), cur_b.type
                )
            elif head == _constant("Slots") and len(type_args) == 2:
                elem_t, cap_t = type_args[0], type_args[1]
                idx_t = self._slots_usize_arg(idx_node, updated)
                rhs_t = self.check(rhs_expr, elem_t, updated)
                can_w = _apps(_constant("Slots_CanWrite"), elem_t, cap_t, cur_b.term)
                if not self._prove_bool_precondition(can_w, updated):
                    raise self.fail(
                        "type",
                        "cannot prove Slots has valid tag and write permission (Slots.CanWrite)",
                        statement,
                    )
                live_t = _apps(_constant("Slots_LiveCount"), elem_t, cap_t, cur_b.term)
                lt_live = _apps(_constant("int_lt_usize"), idx_t, live_t)
                eq_live = _apps(_constant("int_eq_usize"), idx_t, live_t)
                cap_u = self._slots_cap_usize_term(cap_t)
                lt_cap = (
                    _apps(_constant("int_lt_usize"), idx_t, cap_u)
                    if self.whnf(cap_u).kind == "int"
                    else _apps(_constant("<"), _app(_constant("int_to_nat_usize"), idx_t), cap_t)
                )
                if not (
                    self._prove_bool_precondition(lt_live, updated)
                    or (
                        self._prove_bool_precondition(eq_live, updated)
                        and self._prove_bool_precondition(lt_cap, updated)
                    )
                ):
                    raise self.fail(
                        "type",
                        "cannot prove Slots indexed write is in bounds (index < LiveCount or (index == LiveCount and index < capacity))",
                        statement,
                    )
                new_col_b = _Binding(
                    _apps(_constant("Slots_Write"), elem_t, cap_t, cur_b.term, idx_t, rhs_t), cur_b.type
                )
            elif head == _constant("Seq") and len(type_args) == 1:
                elem_t = type_args[0]
                cnt_t = _apps(_constant("Seq_Count"), elem_t, cur_b.term)
                idx_nat = self._nat_or_usize_index(idx_node, updated, "Seq")
                rhs_t = self.check(rhs_expr, elem_t, updated)
                in_bounds = _apps(_constant("<"), idx_nat, cnt_t)
                if not self._prove_bool_precondition(in_bounds, updated):
                    raise self.fail(
                        "type",
                        "cannot prove Seq indexed write is in bounds (index < seq.Count)",
                        statement,
                    )
                new_col_b = _Binding(
                    _apps(_constant("Seq_Update"), elem_t, cur_b.term, idx_nat, rhs_t), cur_b.type
                )
            elif head == _constant("Vec") and len(type_args) == 2:
                elem_t, len_t = type_args[0], type_args[1]
                idx_nat = self._nat_or_usize_index(idx_node, updated, "Vec")
                rhs_t = self.check(rhs_expr, elem_t, updated)
                in_bounds = _apps(_constant("<"), idx_nat, len_t)
                if not self._prove_bool_precondition(in_bounds, updated):
                    raise self.fail(
                        "type",
                        "cannot prove Vec indexed write is in bounds (index < n)",
                        statement,
                    )
                new_col_b = _Binding(
                    _apps(_constant("Vec_Update"), elem_t, len_t, idx_nat, rhs_t, cur_b.term), cur_b.type
                )
            else:
                raise self.fail(
                    "type",
                    "indexed assignment target must have type Span<byte>, Slots<T, capacity>, Seq<T> or Vec<T, n>",
                    target,
                )
            if rname in self.indexed_local_borrows:
                self._apply_indexed_borrow_write(rname, new_col_b, updated, statement)
                return updated
            updated[rname] = new_col_b
            if head == _constant("Span") and rname in self.slice_views:
                self._restore_slice_view_to_parent(
                    rname, new_col_b.term, updated, span_write_idx=span_idx_t, span_write_val=span_rhs_t
                )
            return updated
        raise self.fail("type", "assignment target must be a mutable local variable or record field", target)

    @staticmethod
    def _extract_ref_or_var_name(arg_node: Node) -> tuple[str | None, bool]:
        val = arg_node.get("value") if arg_node.get("kind") == "argument" else arg_node
        while isinstance(val, dict) and val.get("kind") == "group":
            val = val.get("value")
        if not isinstance(val, dict):
            return None, False
        if (
            val.get("kind") == "unary"
            and isinstance(val.get("operator"), dict)
            and cast("Node", val["operator"]).get("text") == "ref"
        ):
            inner = val.get("value")
            while isinstance(inner, dict) and inner.get("kind") == "group":
                inner = inner.get("value")
            if isinstance(inner, dict) and inner.get("kind") == "name" and isinstance(inner.get("name"), dict):
                return cast("str", cast("Node", inner["name"]).get("text")), True
            return None, True
        if val.get("kind") == "name" and isinstance(val.get("name"), dict):
            return cast("str", cast("Node", val["name"]).get("text")), False
        return None, False

    def _apply_borrow_write(
        self: _Elaborator,
        bname: str,
        new_binding: _Binding,
        updated: dict[str, _Binding],
        site_node: Node,
    ) -> None:
        bmode, owner_name, field_path = self.local_borrows[bname]
        if bmode not in {"ref", "shared_ref"}:
            raise self.fail(
                "type",
                f"cannot mutate through shared 'in' borrow '{bname}' (write-through-shared)",
                site_node,
            )
        if owner_name not in updated:
            raise self.fail("name", f"unknown identifier '{owner_name}'", site_node)
        if not field_path:
            rec_head, rec_targs = self.spine(self.whnf(new_binding.type))
            if (
                rec_head.kind == "const"
                and isinstance(rec_head.value, str)
                and rec_head.value in self.records_by_type
            ):
                rinfo = self.records_by_type[rec_head.value]
                lifted = self.lifted_invariants.get(owner_name, set()) | self.lifted_invariants.get(bname, set())
                self._check_record_invariants(
                    rinfo, rec_targs, new_binding.term, updated, site_node, exclude_clauses=lifted
                )
            updated[owner_name] = new_binding
            if owner_name in self.slice_views:
                parent_name = self.slice_views[owner_name]
                if parent_name in updated:
                    p_b = updated[parent_name]
                    updated[parent_name] = _Binding(
                        _apps(_constant("Span_Restore"), _U8, p_b.term, new_binding.term), p_b.type
                    )
        else:
            owner_b = updated[owner_name]
            lifted = self.lifted_invariants.get(owner_name, set()) | self.lifted_invariants.get(bname, set())
            new_rec_term = self._update_record_field_path(
                owner_b.term,
                owner_b.type,
                field_path,
                new_binding.term,
                updated,
                site_node,
                exclude_clauses=lifted,
            )
            updated[owner_name] = _Binding(new_rec_term, owner_b.type)
        self._clear_partial_move_on_write(owner_name, field_path)
        if bmode == "shared_ref" or owner_name in self.shared_ref_locals:
            written_ty = updated[owner_name].type if not field_path else new_binding.type
            if not self._is_shape_stable_type(written_ty) and owner_name not in {
                p.owner for p in self.proved_tag_preserved_places
            }:
                raise self.fail(
                    "type",
                    f"unstable write through 'shared ref' binding '{bname}' requires a shape-stable or tag-preserved proof (unstable-shared-mut-write)",
                    site_node,
                )
            self._purge_overlapping_facts_on_shared_write(owner_name, field_path, None, updated)
            self._refresh_shared_mut_aliases(owner_name, updated, site_node)
        else:
            self._refresh_local_borrows(updated, site_node)

    def _apply_indexed_borrow_write(
        self: _Elaborator,
        bname: str,
        new_binding: _Binding,
        updated: dict[str, _Binding],
        site_node: Node,
    ) -> None:
        info = self.indexed_local_borrows[bname]
        if info.mode != "ref":
            raise self.fail(
                "type",
                f"cannot mutate through shared 'in' borrow '{bname}' (write-through-shared)",
                site_node,
            )
        if info.owner not in updated:
            raise self.fail("name", f"unknown identifier '{info.owner}'", site_node)
        self._check_indexed_local_borrow_access(bname, updated, site_node)
        owner_b = updated[info.owner]

        def read_collection_at(
            ckind: Literal["vec", "seq", "span", "slots"],
            targs: tuple[_Term, ...],
            col_term: _Term,
            idx_t: _Term,
        ) -> _Term:
            if ckind == "vec":
                d_val = self._default_term_for_type(targs[0])
                return _apps(_constant("Vec_At_Nat"), targs[0], targs[1], d_val, idx_t, col_term)
            if ckind == "seq":
                d_val = self._sequence_lookup_default(targs[0], col_term)
                return _apps(_constant("Seq_At"), targs[0], d_val, col_term, idx_t)
            if ckind == "span":
                return _apps(_constant("Span_Read"), _U8, col_term, idx_t)
            d_val = self._sequence_lookup_default(
                targs[0], _apps(_constant("Slots_Model"), targs[0], targs[1], col_term)
            )
            return _apps(_constant("Slots_Read"), targs[0], targs[1], d_val, col_term, idx_t)

        def write_collection_at(
            ckind: Literal["vec", "seq", "span", "slots"],
            targs: tuple[_Term, ...],
            col_term: _Term,
            idx_t: _Term,
            val_t: _Term,
        ) -> _Term:
            if ckind == "vec":
                return _apps(_constant("Vec_Update"), *targs, idx_t, val_t, col_term)
            if ckind == "seq":
                return _apps(_constant("Seq_Update"), *targs, col_term, idx_t, val_t)
            if ckind == "span":
                return _apps(_constant("Span_Write"), *targs, col_term, idx_t, val_t)
            return _apps(_constant("Slots_Write"), *targs, col_term, idx_t, val_t)

        def build_updated_leaf(cur_elem: _Term, cur_ty: _Term, fpath: tuple[str, ...]) -> _Term:
            if not fpath:
                return new_binding.term
            r_head, r_targs = self.spine(self.whnf(cur_ty))
            if r_head.kind != "const" or not isinstance(r_head.value, str) or r_head.value not in self.records_by_type:
                raise self.fail("type", f"borrowed element of '{info.owner}' is not a record", site_node)
            record_info = self.records_by_type[r_head.value]
            f_idx = next((k for k, rf in enumerate(record_info.fields) if rf.name == fpath[0]), None)
            if f_idx is None:
                raise self.fail("name", f"record '{record_info.name}' has no field '{fpath[0]}'", site_node)
            final_fields: list[_Term] = []
            for k, rf in enumerate(record_info.fields):
                proj = _apps(_constant(rf.proj_const), *r_targs, cur_elem)
                if k == f_idx:
                    ft = self._instantiate_record_field_type(record_info, r_targs, k, cur_elem)
                    final_fields.append(build_updated_leaf(proj, ft, fpath[1:]))
                else:
                    final_fields.append(proj)
            new_rec = _apps(_constant(record_info.ctor_const), *r_targs, *final_fields)
            self._check_record_invariants(record_info, r_targs, new_rec, updated, site_node)
            return new_rec

        def build_nested(
            col_term: _Term,
            levels: tuple[tuple[Literal["vec", "seq", "span", "slots"], _Term, _Term, tuple[_Term, ...], _Term], ...],
        ) -> _Term:
            ckind, idx_t, _, targs, elem_ty = levels[0]
            if len(levels) == 1:
                if info.field_path:
                    old_leaf = read_collection_at(ckind, targs, col_term, idx_t)
                    leaf_val = build_updated_leaf(old_leaf, elem_ty, info.field_path)
                else:
                    leaf_val = new_binding.term
                return write_collection_at(ckind, targs, col_term, idx_t, leaf_val)
            sub_col = read_collection_at(ckind, targs, col_term, idx_t)
            updated_sub = build_nested(sub_col, levels[1:])
            return write_collection_at(ckind, targs, col_term, idx_t, updated_sub)

        all_levels = (
            (info.collection_kind, info.index_term, info.index_type, info.type_args, info.elem_type),
            *info.nested_indices,
        )
        new_owner_term = build_nested(owner_b.term, all_levels)
        new_owner_b = _Binding(new_owner_term, owner_b.type)
        if info.owner in self.indexed_local_borrows:
            self._apply_indexed_borrow_write(info.owner, new_owner_b, updated, site_node)
        elif info.owner in self.local_borrows:
            self._apply_borrow_write(info.owner, new_owner_b, updated, site_node)
        else:
            updated[info.owner] = new_owner_b
            if info.collection_kind == "span" and info.owner in self.slice_views:
                self._restore_slice_view_to_parent(
                    info.owner,
                    new_owner_term,
                    updated,
                    span_write_idx=info.index_term if not info.nested_indices and not info.field_path else None,
                    span_write_val=new_binding.term if not info.nested_indices and not info.field_path else None,
                )
            self._refresh_local_borrows(updated, site_node)
        updated[bname] = new_binding
        self.indexed_local_borrows[bname] = replace(info, owner_term=self.whnf(updated[info.owner].term))
        if not self.in_inline_proof:
            self.runtime_writes.add(self.slice_views.get(info.owner, info.owner))

    def _note_runtime_access(self: _Elaborator, target: Node, footprint: set[str]) -> None:
        if self.in_inline_proof:
            return
        place = self._unwrap_group(target)
        while place["kind"] in {"member", "index", "argument", "unary"}:
            place = self._unwrap_group(self.node(place["value"]))
        if place["kind"] == "name":
            name = self.name(place["name"])
            if name in self.indexed_local_borrows:
                name = self.indexed_local_borrows[name].owner
            if name in self.local_borrows:
                name = self.local_borrows[name][1]
            footprint.add(self.slice_views.get(name, name))

    def _note_runtime_write(self: _Elaborator, target: Node) -> None:
        if self.in_inline_proof:
            raise self.fail("type", "an erased proof cannot write through a runtime place", target)
        self._note_runtime_access(target, self.runtime_writes)

    def _record_call_update(
        self: _Elaborator, target: Node, value: _Binding, *, writes: bool = True, index: _Term | None = None
    ) -> None:
        if self.in_inline_proof:
            raise self.fail("type", "an erased proof cannot update a runtime loan", target)
        if writes:
            self._note_runtime_write(target)
        if self.guard_value:
            raise self.fail("unsupported", "a pattern guard used as a value cannot model a mutable loan update; "
                            "use an if statement", target)
        if writes:
            self.last_call_updates.append((target, value, index))

    def _consume_call_updates(
        self: _Elaborator, updated: dict[str, _Binding], site: Node
    ) -> None:
        if not self.last_call_updates:
            return
        pending = self.last_call_updates
        self.last_call_updates = []
        self._apply_call_updates(updated, site, pending)

    def _apply_call_updates(
        self: _Elaborator, updated: dict[str, _Binding], site: Node,
        pending: list[tuple[Node, _Binding, _Term | None]],
    ) -> None:
        for arg_node, new_b, position in pending:
            if position is not None:
                owner = self._unwrap_group(self.node(arg_node["value"]))
                collection = updated[self.name(owner["name"])]
                head, targs = self.spine(self.whnf(collection.type))
                if head == _constant("Vec"):
                    term = _apps(_constant("Vec_Update"), *targs, position, new_b.term, collection.term)
                else:
                    update = {"Span": "Span_Write", "Slots": "Slots_Write", "Seq": "Seq_Update"}[str(head.value)]
                    term = _apps(_constant(update), *targs, collection.term, position, new_b.term)
                self._apply_ref_target_update(owner, _Binding(term, collection.type), updated, site)
            elif not self._apply_ref_target_update(arg_node, new_b, updated, site):
                raise self.fail("unsupported", "cannot restore this call's exclusive loan target", arg_node)

    def _apply_ref_target_update(
        self: _Elaborator, arg_node: Node, new_binding: _Binding, updated: dict[str, _Binding], site: Node
    ) -> bool:
        val = arg_node.get("value") if arg_node.get("kind") == "argument" else arg_node
        while isinstance(val, dict) and val.get("kind") == "group":
            val = val.get("value")
        if (
            isinstance(val, dict)
            and val.get("kind") == "unary"
            and isinstance(val.get("operator"), dict)
            and cast("Node", val["operator"]).get("text") in {"ref", "in", "out"}
        ):
            val = val.get("value")
            while isinstance(val, dict) and val.get("kind") == "group":
                val = val.get("value")
        if not isinstance(val, dict):
            return False
        if val.get("kind") == "out_variable":
            vname = self.name(val["name"])
            self.bind_local(updated, vname, new_binding)
            self.mutable_locals.add(vname)
            return True
        if val.get("kind") == "name" and isinstance(val.get("name"), dict):
            vname = cast("str", cast("Node", val["name"]).get("text"))
            if vname in updated:
                if vname in self.frozen_collections:
                    raise self.fail("type", f"cannot mutate frozen collection '{vname}'", site)
                if vname in self.indexed_local_borrows:
                    self._apply_indexed_borrow_write(vname, new_binding, updated, site)
                    return True
                if vname in self.local_borrows:
                    self._apply_borrow_write(vname, new_binding, updated, site)
                    return True
                self.uninitialized_out_params.discard(vname)
                updated[vname] = new_binding
                if vname in self.slice_views:
                    self._restore_slice_view_to_parent(vname, new_binding.term, updated)
                self._refresh_local_borrows(updated, site)
                return True
            return False
        if val.get("kind") == "member" and isinstance(val.get("name"), dict) and isinstance(val.get("value"), dict):
            recv = self._unwrap_group(cast("Node", val["value"]))
            fname = cast("str", cast("Node", val["name"]).get("text"))
            if recv.get("kind") == "name" and isinstance(recv.get("name"), dict):
                rname = cast("str", cast("Node", recv["name"]).get("text"))
                if rname in updated:
                    if rname in self.uninitialized_out_params:
                        raise self.fail(
                            "type",
                            f"cannot partially initialize 'out' parameter '{rname}' before whole-value assignment",
                            site,
                        )
                    if rname in self.frozen_collections:
                        raise self.fail("type", f"cannot mutate frozen collection '{rname}'", site)
                    if rname not in self.mutable_locals:
                        raise self.fail(
                            "type",
                            f"cannot mutate field '{fname}' of immutable record '{rname}'; declare it with 'var' or 'ref'",
                            site,
                        )
                    cur_b = updated[rname]
                    rec_type = self.whnf(cur_b.type)
                    head, type_args = self.spine(rec_type)
                    if (
                        head.kind == "const"
                        and isinstance(head.value, str)
                        and head.value in self.records_by_type
                    ):
                        record_info = self.records_by_type[head.value]
                        field_index = next(
                            (idx for idx, rf in enumerate(record_info.fields) if rf.name == fname), None
                        )
                        if field_index is not None:
                            final_fields: list[_Term] = []
                            for idx, rf in enumerate(record_info.fields):
                                if idx == field_index:
                                    final_fields.append(new_binding.term)
                                else:
                                    final_fields.append(_apps(_constant(rf.proj_const), *type_args, cur_b.term))
                            new_rec_term = _apps(_constant(record_info.ctor_const), *type_args, *final_fields)
                            if rname in self.local_borrows:
                                self._apply_borrow_write(rname, _Binding(new_rec_term, cur_b.type), updated, site)
                                return True
                            lifted = self.lifted_invariants.get(rname, set())
                            self._check_record_invariants(
                                record_info, type_args, new_rec_term, updated, site, exclude_clauses=lifted
                            )
                            updated[rname] = _Binding(new_rec_term, cur_b.type)
                            self._refresh_local_borrows(updated, site)
                            return True
        return False

    def _elaborate_expression_statement(
        self: _Elaborator, statement: Node, extended: dict[str, _Binding]
    ) -> dict[str, _Binding]:
        self.site = statement
        expr_node = self._unwrap_group(self.node(statement["value"]))
        updated = dict(extended)
        if expr_node["kind"] == "call":
            callee = self._unwrap_group(self.node(expr_node["callee"]))
            call_args = self.nodes(expr_node["arguments"])
            outputs = [target for arg in call_args if (target := self.node(arg["value"]))["kind"] == "out_variable"]
            if outputs:
                result = self.expression(expr_node, updated, standalone_call=True)
                if self.whnf(result.type) != _UNIT:
                    raise self.fail("type", "a standalone 'out var' call must return Unit", expr_node)
                self._consume_call_updates(updated, statement)
                for target in outputs:
                    if self.name(target["name"]) not in updated:
                        raise self.fail("type", "'out var' requires an 'out' parameter", target)
                return updated
            path = self._dotted_member_path(callee)
            if path is None and callee["kind"] == "generic_application":
                path = self._dotted_member_path(self.node(callee["value"]))
            if path in {"TransferType", "Slots.TransferType"} and len(call_args) == 3:
                res_b = self.expression(expr_node, updated)
                prod_ty = self.whnf(res_b.type)
                if prod_ty.kind == "prod":
                    src_ty, dst_ty = prod_ty.args
                    src_b = _Binding(
                        self.whnf(_apps(_constant("Fst"), src_ty, dst_ty, res_b.term)), src_ty
                    )
                    dst_b = _Binding(
                        self.whnf(_apps(_constant("Snd"), src_ty, dst_ty, res_b.term)), dst_ty
                    )
                    self._note_runtime_write(call_args[0])
                    self._note_runtime_write(call_args[1])
                    self._apply_ref_target_update(call_args[0], src_b, updated, statement)
                    self._apply_ref_target_update(call_args[1], dst_b, updated, statement)
                    return updated
            if path in {"CopyRepresentation", "Slots.CopyRepresentation"} and len(call_args) == 3:
                res_b = self.expression(expr_node, updated)
                self._note_runtime_write(call_args[1])
                if self._apply_ref_target_update(call_args[1], res_b, updated, statement):
                    return updated
            if path == "Slots.Write" and len(call_args) == 3:
                self._note_runtime_write(call_args[0])
                res_b = self.expression(expr_node, updated)
                if self._apply_ref_target_update(call_args[0], res_b, updated, statement):
                    return updated
            if path in {"Span.Write", "Span.Fill", "Span.CopyPrefix", "Span.Restore"} and len(call_args) >= 2:
                self._note_runtime_write(call_args[0])
                res_b = self.expression(expr_node, updated)
                if self._apply_ref_target_update(call_args[0], res_b, updated, statement):
                    return updated
            if path == "Format.Write" and len(call_args) == 2:
                self._note_runtime_write(call_args[0])
                b_name, _ = self._extract_ref_or_var_name(call_args[0])
                res_b = self.expression(expr_node, updated)
                if b_name is not None and b_name in updated:
                    updated[b_name] = res_b
                    return updated
        value = self.expression(expr_node, updated)
        if self.in_executable_function and self._result_paths("", value.type):
            raise self.fail("type", "unexamined Result: match it, propagate it with '?' or return it", expr_node)
        self._consume_call_updates(updated, statement)
        return updated

    def _elaborate_scope_statement(
        self: _Elaborator,
        statement: Node,
        extended: dict[str, _Binding],
        facts: tuple[_Binding, ...],
    ) -> dict[str, _Binding]:
        self.site = statement
        loan_nodes = self.nodes(statement["resources"])
        lift_raw = statement.get("lifts")
        if lift_raw is not None and not isinstance(lift_raw, list):
            raise self.fail("protocol", "expected a syntax list", statement)
        lift_names = [] if lift_raw is None else [self.name(ln) for ln in lift_raw]
        if len(lift_names) != len(set(lift_names)):
            raise self.fail("name", "duplicate record invariant clause in open lifts list", statement)
        loaned_records: list[tuple[str, _RecordInfo, list[_Term]]] = []
        seen_targets: set[str] = set()
        for loan_node in loan_nodes:
            self.node(loan_node, "unary")
            tname, is_ref = self._extract_ref_or_var_name(loan_node)
            if not is_ref or tname is None:
                raise self.fail("type", "open header requires 'ref <variable>' loan targets", loan_node)
            if tname in seen_targets:
                raise self.fail("type", f"duplicate 'ref {tname}' loan in open header", loan_node)
            seen_targets.add(tname)
            if tname not in extended:
                raise self.fail("name", f"unknown identifier '{tname}' in open header", loan_node)
            if tname in self.uninitialized_out_params:
                raise self.fail(
                    "type",
                    f"cannot take mutable 'ref' loan of uninitialized 'out' parameter '{tname}'",
                    loan_node,
                )
            if tname in self.frozen_collections:
                raise self.fail("type", f"cannot mutably loan frozen collection '{tname}'", loan_node)
            if tname not in self.mutable_locals:
                raise self.fail("type", f"cannot open an invariant through immutable binding '{tname}'; "
                                "a mutable place or exclusive loan is required", loan_node)
            cur_b = extended[tname]
            if self._is_readonly_span(cur_b.term):
                raise self.fail(
                    "type", f"cannot take mutable 'ref' loan of read-only 'in' parameter '{tname}'", loan_node
                )
            rec_type = self.whnf(cur_b.type)
            head, type_args = self.spine(rec_type)
            if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.records_by_type:
                raise self.fail(
                    "type", f"open invariant lifting requires a record target, got '{tname}'", loan_node
                )
            rinfo = self.records_by_type[head.value]
            loaned_records.append((tname, rinfo, type_args))
        for cname in lift_names:
            matching = [
                tname
                for tname, rinfo, _ in loaned_records
                if any(inv.name == cname and not inv.name.startswith("__anon_") for inv in rinfo.invariants)
            ]
            if not matching:
                raise self.fail(
                    "name",
                    f"none of the loaned records in open declare named invariant clause '{cname}'",
                    statement,
                )
        saved_mutable = set(self.mutable_locals)
        saved_lifted = {k: set(v) for k, v in self.lifted_invariants.items()}
        saved_active_facts = list(self.active_facts)
        # Remove facts originating from the lifted invariant clauses during the scope body,
        # while retaining pre-scope Slots_LivePrefix / Slots_VacantRange facts on the entry record term.
        lifted_by_target: dict[str, set[str]] = {}
        lifted_fact_terms: set[_Term] = set()
        pre_scope_slot_facts: list[_Term] = []
        for tname, rinfo, type_args in loaned_records:
            clauses_for_t = {
                inv.name
                for inv in rinfo.invariants
                if inv.name in lift_names
            }
            lifted_by_target[tname] = clauses_for_t
            self.lifted_invariants.setdefault(tname, set()).update(clauses_for_t)
            for inv in rinfo.invariants:
                if inv.name in clauses_for_t:
                    inst_t = self._instantiate_record_type(rinfo, type_args, inv.term)
                    inst_t = self.substitute(inst_t, cast("int", inv.self_var.value), extended[tname].term)
                    w_inst = self.whnf(inst_t)
                    lifted_fact_terms.add(w_inst)
                    w_head, _ = self.spine(w_inst)
                    if w_head in {_constant("Slots_LivePrefix"), _constant("Slots_VacantRange")}:
                        pre_scope_slot_facts.append(inst_t)
        self.active_facts = [
            *(f for f in self.active_facts if self.whnf(f) not in lifted_fact_terms),
            *pre_scope_slot_facts,
        ]
        self.active_lift_scopes += 1
        try:
            body_block = self.node(statement["body"], "block")
            after_env, _ = self._elaborate_non_returning_block(body_block, extended, facts)
        finally:
            self.active_lift_scopes -= 1
            self.mutable_locals = saved_mutable
            self.lifted_invariants = saved_lifted
            self.active_facts = saved_active_facts
        for tname, rinfo, type_args in loaned_records:
            self._check_record_invariants(
                rinfo,
                type_args,
                after_env[tname].term,
                after_env,
                statement,
                only_clauses=lifted_by_target[tname],
            )
            for inv in rinfo.invariants:
                inst_ty = self._instantiate_record_type(rinfo, type_args, inv.type)
                inst_ty = self.substitute(inst_ty, cast("int", inv.self_var.value), after_env[tname].term)
                if self.whnf(inst_ty) == _BOOL:
                    inst_t = self._instantiate_record_type(rinfo, type_args, inv.term)
                    inst_t = self.substitute(inst_t, cast("int", inv.self_var.value), after_env[tname].term)
                    self.active_facts.append(inst_t)
        if len(loaned_records) == 1:
            target, record, _ = loaned_records[0]
            lint_extra_lifts(self, statement, target, record)
        return after_env

    def _check_loop_invariants(
        self: _Elaborator,
        contracts: list[Node],
        env: dict[str, _Binding],
        _site: Node,
        phase: str,
    ) -> list[_Term]:
        proved_bools: list[_Term] = []
        for contract in contracts:
            self.node(contract, "contract")
            if contract["role"] == "decreases":
                continue
            if contract["role"] != "invariant":
                raise self.fail("unsupported", f"loop contract '{contract['role']}' is not supported", contract)
            c_val_node = self.node(contract["value"])
            c_val = self.expression(c_val_node, env)
            c_label = f" '{self.name(contract['name'])}'" if contract.get("name") is not None else ""
            if self.whnf(c_val.type) == _BOOL:
                if not self._prove_bool_precondition(c_val.term, env):
                    raise self.fail(
                        "type",
                        f"loop invariant{c_label} could not be established on loop {phase}",
                        contract,
                    )
                proved_bools.append(c_val.term)
            else:
                prop_t = self.proposition(c_val_node, env)
                self._prove_proposition(prop_t, env, (), contract)
        if phase == "entry":
            self._lint_identical_loop_invariants(contracts)
        return proved_bools

    def _assume_loop_invariants(
        self: _Elaborator,
        contracts: list[Node],
        env: dict[str, _Binding],
    ) -> list[_Term]:
        assumed_bools: list[_Term] = []
        inherited = list(self.active_facts)
        for contract in contracts:
            self.node(contract, "contract")
            if contract["role"] == "decreases":
                continue
            if contract["role"] != "invariant":
                raise self.fail("unsupported", f"loop contract '{contract['role']}' is not supported", contract)
            c_val_node = self.node(contract["value"])
            self.active_facts.extend(assumed_bools)
            try:
                c_val = self.expression(c_val_node, env)
            finally:
                for _ in assumed_bools:
                    self.active_facts.pop()
            if self.whnf(c_val.type) == _BOOL:
                stable_loop_fact(self, contract, c_val.term, inherited)
                assumed_bools.append(c_val.term)
            else:
                prop_t = self.proposition(c_val_node, env)
                extracted = self._extract_equality(prop_t)
                if extracted is not None:
                    eq_ty, u, v = extracted
                    eq_ty_w = self.whnf(eq_ty)
                    if eq_ty_w == _BOOL and self.whnf(v) == _term("bool", value=1):
                        assumed_bools.append(u)
                    elif self._int_spec(eq_ty_w) is not None or eq_ty_w == _NAT:
                        spec = self._int_spec(eq_ty_w)
                        eq_const = f"int_eq_{spec.name}" if spec is not None else "eq_nat"
                        assumed_bools.append(_apps(_constant(eq_const), u, v))
        return assumed_bools

    def _eval_loop_decreases(
        self: _Elaborator,
        contracts: list[Node],
        env: dict[str, _Binding],
    ) -> list[tuple[Node, _Term, _IntSpec | None]]:
        measures: list[tuple[Node, _Term, _IntSpec | None]] = []
        for contract in contracts:
            self.node(contract, "contract")
            if contract["role"] != "decreases":
                continue
            m_b = self.expression(self.node(contract["value"]), env)
            m_w = self.whnf(m_b.type)
            m_spec = self._int_spec(m_w)
            if m_w != _NAT and m_spec is None:
                raise self.fail(
                    "type",
                    "loop 'decreases' termination measure must have type Nat or a fixed-width integer",
                    contract,
                )
            if m_spec is not None and m_spec.signed:
                nonneg = _apps(_constant(f"int_ge_{m_spec.name}"), m_b.term, _int_term(m_spec, 0))
                if not self._prove_bool_precondition(nonneg, env):
                    raise self.fail(
                        "type",
                        "signed loop 'decreases' termination measure could not be proved non-negative",
                        contract,
                    )
            measures.append((contract, m_b.term, m_spec))
        return measures

    def _check_loop_decreases(
        self: _Elaborator,
        before_measures: list[tuple[Node, _Term, _IntSpec | None]],
        after_env: dict[str, _Binding],
        phase: str,
    ) -> None:
        if not before_measures:
            return
        after_measures = self._eval_loop_decreases([c for c, _, _ in before_measures], after_env)
        for j in range(len(before_measures)):
            prefix_eq = True
            for i in range(j):
                _, b_term, b_spec = before_measures[i]
                _, a_term, _ = after_measures[i]
                eq_op = f"int_eq_{b_spec.name}" if b_spec is not None else "eq_nat"
                if not self._prove_bool_precondition(_apps(_constant(eq_op), a_term, b_term), after_env):
                    prefix_eq = False
                    break
            if not prefix_eq:
                continue
            _, bj_term, bj_spec = before_measures[j]
            _, aj_term, _ = after_measures[j]
            lt_op = f"int_lt_{bj_spec.name}" if bj_spec is not None else "<"
            if self._prove_bool_precondition(_apps(_constant(lt_op), aj_term, bj_term), after_env):
                return
        raise self.fail(
            "type",
            f"loop 'decreases' termination measure could not be proved to strictly decrease on {phase}",
            before_measures[0][0],
        )

    def _elaborate_non_returning_block(
        self: _Elaborator,
        block_node: Node,
        environment: dict[str, _Binding],
        facts: tuple[_Binding, ...],
        *,
        terminal_break: list[_Term] | None = None,
    ) -> tuple[dict[str, _Binding], str | None]:
        after, control = self._non_returning_statements(block_node, environment, facts, terminal_break=terminal_break)
        return self._leave_statement_scope(environment.keys(), after), control

    def _non_returning_statements(
        self: _Elaborator,
        block_node: Node,
        environment: dict[str, _Binding],
        facts: tuple[_Binding, ...],
        *,
        terminal_break: list[_Term] | None = None,
    ) -> tuple[dict[str, _Binding], str | None]:
        self.node(block_node, "block")
        statements = self.nodes(block_node["statements"])
        extended = dict(environment)
        statement_facts: list[_Binding] = []
        saved_active_len = len(self.active_facts)
        try:
            for statement in statements:
                self.site = statement
                kind = cast("str", statement["kind"])
                if kind in {"let", "typed_local", "let_pattern", "constant_local", "var", "var_pattern"}:
                    extended = self._local_with_facts(
                        statement, extended, statement_facts, record_active=True
                    )
                    continue
                if kind in {"let_else", "var_else"}:
                    scrut = self.expression(self.node(statement["value"]), extended)
                    pat = self._parse_pattern(self.node(statement["pattern"]), set())
                    self._typecheck_pattern(pat, scrut.type, extended)
                    else_block = self.node(statement["else"], "block")
                    if self._pattern_matches_concretely(pat, scrut.term):
                        self._bind_concrete_pattern(
                            pat, scrut, extended, is_var=(kind == "var_else")
                        )
                        continue
                    if self._pattern_refuted_concretely(pat, scrut.term):
                        else_env, ctrl = self._elaborate_non_returning_block(
                            else_block, extended, (*facts, *statement_facts)
                        )
                        if ctrl not in {"break", "continue"}:
                            raise self.fail(
                                "type",
                                f"{kind.replace('_', '-')} else block must exit with return, break or continue",
                                statement,
                            )
                        return else_env, ctrl
                    raise self.fail("unsupported", "a symbolic guard with a loop exit needs an explicit control-flow result", statement)
                if kind == "assignment":
                    extended = self._elaborate_assignment(statement, extended)
                    continue
                if kind == "expression_statement":
                    extended = self._elaborate_expression_statement(statement, extended)
                    continue
                if kind in {"assert", "proof", "calc"}:
                    sub_facts = self._statement_proof_facts(statement, extended, (*facts, *statement_facts))
                    if kind == "assert" and statement["by"] is None:
                        observe(self, "HOLDFAST128", statement, "assertion repeats a proof fact already in scope"
                                if sub_facts[0] in statement_facts else None)
                    statement_facts.extend(sub_facts)
                    self.active_facts.extend(self._fact_bool_terms(sub_facts, extended))
                    continue
                if kind == "open_invariant":
                    extended = self._elaborate_scope_statement(
                        statement, extended, (*facts, *statement_facts)
                    )
                    continue
                if kind == "foreach":
                    extended = self._elaborate_foreach_statement(
                        statement, extended, (*facts, *statement_facts)
                    )
                    continue
                if kind == "foreach_collection":
                    extended = self._elaborate_foreach_collection_statement(
                        statement, extended, (*facts, *statement_facts)
                    )
                    continue
                if kind == "while":
                    extended = self._elaborate_while_statement(
                        statement, extended, (*facts, *statement_facts)
                    )
                    continue
                if kind in {"break", "continue"}:
                    if self.in_loop_depth <= 0:
                        raise self.fail("type", f"'{kind}' statement is only permitted inside a loop", statement)
                    if self.active_lift_scopes > 0:
                        raise self.fail(
                            "type",
                            f"cannot '{kind}' out of a loop while a record invariant is lifted",
                            statement,
                        )
                    return extended, cast("str", kind)
                if kind == "if":
                    cond_raw = self.node(statement["condition"])
                    if operands := self._pattern_conjuncts(cond_raw):
                        extended, ctrl = self._guard_non_returning(
                            statement, operands, extended, (*facts, *statement_facts),
                        )
                        if ctrl is not None:
                            return extended, ctrl
                        continue
                    condition = self.check(cond_raw, _BOOL, extended)
                    self._consume_call_updates(extended, cond_raw)
                    lint_branch(self, cond_raw, condition, extended)
                    cond_w = self.whnf(condition)
                    then_node = self.node(statement["then"])
                    then_block = (
                        then_node
                        if then_node["kind"] == "block"
                        else {"kind": "block", "span": then_node["span"], "statements": [then_node]}
                    )
                    else_raw = statement["else"]
                    else_block = (
                        None
                        if else_raw is None
                        else (
                            self.node(else_raw)
                            if self.node(else_raw)["kind"] == "block"
                            else {
                                "kind": "block",
                                "span": self.node(else_raw)["span"],
                                "statements": [self.node(else_raw)],
                            }
                        )
                    )
                    if cond_w.kind == "bool":
                        if cond_w.value == 1:
                            extended, ctrl = self._elaborate_non_returning_block(
                                then_block, extended, (*facts, *statement_facts)
                            )
                            if ctrl is not None:
                                return extended, ctrl
                        elif else_block is not None:
                            extended, ctrl = self._elaborate_non_returning_block(
                                else_block, extended, (*facts, *statement_facts)
                            )
                            if ctrl is not None:
                                return extended, ctrl
                        continue
                    saved_uninit = set(self.uninitialized_out_params)
                    saved_indexed: dict[str, _IndexedLocalBorrow] = dict(self.indexed_local_borrows)
                    saved_peer_len = len(self.indexed_borrow_peers)
                    yes_guard = self._branch_guard(condition, True)
                    no_guard = self._branch_guard(condition, False)
                    self.active_facts.append(condition)
                    try:
                        then_env, then_ctrl = self._elaborate_non_returning_block(
                            then_block, dict(extended), (*facts, *statement_facts, *yes_guard)
                        )
                        then_uninit = set(self.uninitialized_out_params)
                        then_indexed: dict[str, _IndexedLocalBorrow] = dict(self.indexed_local_borrows)
                        then_peers: list[_IndexedBorrowPeer] = self.indexed_borrow_peers[saved_peer_len:]
                    finally:
                        self.active_facts.pop()
                    self.uninitialized_out_params = set(saved_uninit)
                    self.indexed_local_borrows = dict(saved_indexed)
                    del self.indexed_borrow_peers[saved_peer_len:]
                    if else_block is not None:
                        self.active_facts.append(_app(_constant("!"), condition))
                        try:
                            else_env, else_ctrl = self._elaborate_non_returning_block(
                                else_block, dict(extended), (*facts, *statement_facts, *no_guard)
                            )
                            else_uninit = set(self.uninitialized_out_params)
                            else_indexed: dict[str, _IndexedLocalBorrow] = dict(self.indexed_local_borrows)
                            else_peers: list[_IndexedBorrowPeer] = self.indexed_borrow_peers[saved_peer_len:]
                        finally:
                            self.active_facts.pop()
                    else:
                        else_env, else_ctrl = dict(extended), None
                        else_uninit = set(saved_uninit)
                        else_indexed = dict(saved_indexed)
                        else_peers = []
                    self.indexed_borrow_peers = [
                        *self.indexed_borrow_peers[:saved_peer_len],
                        *(then_peers if then_ctrl is None else []),
                        *(else_peers if else_ctrl is None else []),
                    ]
                    restored_indexed: dict[str, _IndexedLocalBorrow] = {}
                    for bk, orig_info in saved_indexed.items():
                        if bk not in extended:
                            continue
                        t_info = then_indexed.get(bk, orig_info)
                        e_info = else_indexed.get(bk, orig_info)
                        if t_info.owner_term != e_info.owner_term and orig_info.owner in extended:
                            joined_owner = self.whnf(self._branch_value(
                                extended[orig_info.owner].type,
                                condition,
                                self.whnf(t_info.owner_term),
                                self.whnf(e_info.owner_term),
                                yes_guard,
                                no_guard,
                            ))
                            restored_indexed[bk] = replace(orig_info, owner_term=joined_owner)
                        else:
                            restored_indexed[bk] = orig_info
                    self.indexed_local_borrows = restored_indexed
                    if then_ctrl != else_ctrl:
                        if (terminal_break is None or statement is not statements[-1]
                                or {then_ctrl, else_ctrl} != {None, "break"}):
                            raise self.fail("unsupported", "a conditional loop exit needs an explicit control-flow result", statement)
                        terminal_break.append(condition if then_ctrl == "break" else self._negate_bool_term(condition))
                    self.uninitialized_out_params = then_uninit | else_uninit
                    for k, orig_b in list(extended.items()):
                        tb = then_env.get(k, orig_b)
                        eb = else_env.get(k, orig_b)
                        if tb.term != eb.term:
                            extended[k] = _Binding(
                                self.whnf(self._branch_value(
                                    orig_b.type, condition, self.whnf(tb.term), self.whnf(eb.term), yes_guard, no_guard,
                                )),
                                orig_b.type,
                            )
                    if then_ctrl is not None and then_ctrl == else_ctrl:
                        return extended, then_ctrl
                    continue
                if kind == "block":
                    extended, ctrl = self._elaborate_non_returning_block(
                        statement, extended, (*facts, *statement_facts)
                    )
                    if ctrl is not None:
                        return extended, ctrl
                    continue
                if kind == "return":
                    if self.active_lift_scopes > 0:
                        raise self.fail(
                            "type",
                            "cannot return from a callable while a record invariant is lifted in an enclosing scope",
                            statement,
                        )
                    raise self.fail("unsupported", "early return inside a loop or open block is not supported", statement)
                raise self.fail("unsupported", f"statement '{kind}' requires the full frontend", statement)
            return extended, None
        finally:
            del self.active_facts[saved_active_len:]

    def _pattern_matches_concretely(self: _Elaborator, pat: _Pat, term: _Term) -> bool:
        w = self.whnf(term)
        if pat.kind == "wild":
            return True
        if pat.kind == "bool":
            return w.kind == "bool" and bool(w.value) == pat.value
        if pat.kind == "zero":
            return w.kind == "nat" and w.value == 0
        if pat.kind == "succ":
            return w.kind == "nat" and cast("int", w.value) > 0
        if pat.kind == "int_lit":
            return w.kind == "int" and w.value == pat.value
        if pat.kind == "char":
            return w.kind == "char" and w.value == pat.value
        if pat.kind == "union":
            uinfo, uctor = self.union_ctors[cast("str", pat.value)]
            head, args = self.spine(w)
            if head == _constant(uctor.ctor_const):
                payload_args = args[len(uinfo.generic_vars) :]
                if not uctor.fields:
                    return True
                return all(
                    self._pattern_matches_concretely(sp, pa)
                    for sp, pa in zip(pat.args, payload_args, strict=True)
                )
        return False

    def _pattern_refuted_concretely(self: _Elaborator, pat: _Pat, term: _Term) -> bool:
        w = self.whnf(term)
        if pat.kind == "bool" and w.kind == "bool":
            return bool(w.value) != pat.value
        if pat.kind == "zero" and w.kind == "nat":
            return cast("int", w.value) != 0
        if pat.kind == "succ" and w.kind == "nat":
            return cast("int", w.value) == 0
        if pat.kind == "int_lit" and w.kind == "int":
            return w.value != pat.value
        if pat.kind == "char" and w.kind == "char":
            return w.value != pat.value
        if pat.kind == "union":
            uinfo, uctor = self.union_ctors[cast("str", pat.value)]
            head, _ = self.spine(w)
            if head.kind == "const" and any(head == _constant(c.ctor_const) for c in uinfo.constructors):
                return head != _constant(uctor.ctor_const)
        return False

    def _bind_concrete_pattern(
        self: _Elaborator, pat: _Pat, current: _Binding, extended: dict[str, _Binding], *, is_var: bool
    ) -> None:
        for name in pat.names:
            if is_var:
                self.mutable_locals.add(name)
            else:
                self.mutable_locals.discard(name)
            extended[name] = current
        w = self.whnf(current.term)
        if pat.kind == "succ" and w.kind == "nat":
            pred_b = _Binding(_term("nat", value=cast("int", w.value) - 1), _NAT)
            self._bind_concrete_pattern(pat.args[0], pred_b, extended, is_var=is_var)
        elif pat.kind == "union":
            uinfo, uctor = self.union_ctors[cast("str", pat.value)]
            _, type_args = self.spine(self.whnf(current.type))
            _, args = self.spine(w)
            payload_args = args[len(uinfo.generic_vars) :]
            for idx, (sp, pa) in enumerate(zip(pat.args, payload_args, strict=False)):
                fty = self._instantiate_generic_type(uinfo.generic_vars, type_args, uctor.fields[idx].type)
                self._bind_concrete_pattern(sp, _Binding(pa, fty), extended, is_var=is_var)

    def _bind_symbolic_pattern(
        self: _Elaborator, pat: _Pat, current: _Binding, extended: dict[str, _Binding], *, is_var: bool
    ) -> None:
        for name in pat.names:
            if is_var:
                self.mutable_locals.add(name)
            else:
                self.mutable_locals.discard(name)
            extended[name] = current
        if pat.kind == "succ":
            pred_v = self.fresh(_NAT)
            self._bind_symbolic_pattern(pat.args[0], _Binding(pred_v, _NAT), extended, is_var=is_var)
        elif pat.kind == "union":
            uinfo, uctor = self.union_ctors[cast("str", pat.value)]
            _, type_args = self.spine(self.whnf(current.type))
            for idx, sp in enumerate(pat.args):
                fty = self._instantiate_generic_type(uinfo.generic_vars, type_args, uctor.fields[idx].type)
                fv = self.fresh(fty)
                self._bind_symbolic_pattern(sp, _Binding(fv, fty), extended, is_var=is_var)

    def _sum_match_result(
        self: _Elaborator,
        status_term: _Term,
        status_type: _Term,
        result_type: _Term,
        on_left: Callable[[_Term], _Term],
        on_right: Callable[[_Term], _Term],
    ) -> _Term:
        left_type, right_type = status_type.args
        scrut_var = self.fresh(status_type)
        motive_lam = _term("lam", status_type, result_type, value=scrut_var.value)
        left_var = self.fresh(left_type)
        right_var = self.fresh(right_type)
        left_lam = _term("lam", left_type, on_left(left_var), value=left_var.value)
        right_lam = _term("lam", right_type, on_right(right_var), value=right_var.value)
        return _term("sum_match", motive_lam, status_term, left_lam, right_lam)

    def _parse_foreach_range(
        self: _Elaborator, statement: Node, extended: dict[str, _Binding],
    ) -> tuple[_Term, _Term, _Term, _IntSpec | None, str, list[Node], Node]:
        range_node = self.node(statement["range"], "range")
        start_node = self.node(range_node["start"])
        end_node = self.node(range_node["end"])
        if statement.get("type") is not None:
            elem_type = self.type(self.node(statement["type"]), extended)
            start_term = self.check(start_node, elem_type, extended)
            end_term = self.check(end_node, elem_type, extended)
        elif self._is_unsuffixed_int_expr(start_node) and not self._is_unsuffixed_int_expr(end_node):
            end_b = self.expression(end_node, extended)
            elem_type = end_b.type
            end_term = end_b.term
            start_term = self.check(start_node, elem_type, extended)
        else:
            start_b = self.expression(start_node, extended)
            elem_type = start_b.type
            start_term = start_b.term
            end_term = self.check(end_node, elem_type, extended)
        elem_w = self.whnf(elem_type)
        elem_spec = self._int_spec(elem_w)
        if elem_w != _NAT and elem_spec is None:
            raise self.fail(
                "type", "foreach range loop variable must have type Nat or a fixed-width integer", statement
            )
        var_name = self.name(statement["name"])
        if var_name in self.frozen_collections:
            raise self.fail("type", f"cannot shadow frozen collection '{var_name}'", statement)
        return start_term, end_term, elem_type, elem_spec, var_name, self.nodes(statement["contracts"]), self.node(statement["body"], "block")

    def _split_range_foreach_return(
        self: _Elaborator, body_node: Node,
    ) -> tuple[list[Node], Node, list[Node], Node, list[Node]] | None:
        statements = self.nodes(body_node["statements"])
        ret_idx: int | None = None
        for idx, stmt in enumerate(statements):
            if stmt["kind"] == "if" and stmt["else"] is None:
                then_node = self.node(stmt["then"])
                then_stmts = self.nodes(then_node["statements"]) if then_node["kind"] == "block" else [then_node]
                if then_stmts and then_stmts[-1]["kind"] == "return":
                    if ret_idx is not None:
                        return None
                    ret_idx = idx
        if ret_idx is None:
            return None
        prefix = statements[:ret_idx]
        if_stmt = statements[ret_idx]
        then_node = self.node(if_stmt["then"])
        then_stmts = self.nodes(then_node["statements"]) if then_node["kind"] == "block" else [then_node]
        suffix = statements[ret_idx + 1:]

        def has_control_exit(node: object) -> bool:
            if isinstance(node, list):
                return any(has_control_exit(item) for item in node)
            if isinstance(node, dict):
                if node.get("kind") in {"return", "break", "continue"}:
                    return True
                return any(has_control_exit(val) for val in node.values())
            return False

        if any(has_control_exit(part) for part in (prefix, then_stmts[:-1], suffix)):
            return None
        return prefix, if_stmt, then_stmts[:-1], then_stmts[-1], suffix

    def _elaborate_returning_foreach_statement(
        self: _Elaborator,
        statement: Node,
        rest_statements: list[Node],
        extended: dict[str, _Binding],
        expected: _Term | None,
        facts: tuple[_Binding, ...],
    ) -> _Binding:
        self.site = statement
        split = self._split_range_foreach_return(self.node(statement["body"], "block"))
        if split is None:
            raise self.fail("unsupported", "early return inside a loop or open block is not supported", statement)
        prefix_stmts, if_stmt, then_prefix, ret_stmt, suffix_stmts = split
        ret_type = expected if expected is not None else self.current_return_type
        if ret_type is None:
            raise self.fail("type", "returning range loop requires a known return type", statement)
        start_term, end_term, elem_type, elem_spec, var_name, contracts, body_node = self._parse_foreach_range(
            statement, extended
        )
        if elem_spec is not None and elem_spec.signed:
            raise self.fail("unsupported", "symbolic signed ranges need a signed distance representation", statement)
        saved_mutable = set(self.mutable_locals)
        self.mutable_locals.discard(var_name)
        self.in_loop_depth += 1
        try:
            entry_env = dict(extended)
            entry_env[var_name] = _Binding(start_term, elem_type)
            self._check_loop_invariants(contracts, entry_env, statement, "entry")
            self._eval_loop_decreases(contracts, entry_env)
            range_loop(self, statement, contracts, extended, start_term, end_term, elem_spec)
            saved_uninit = set(self.uninitialized_out_params)
            sym_env = dict(extended)
            for mname in list(self.mutable_locals):
                if mname in sym_env and mname != var_name:
                    m_ty = sym_env[mname].type
                    sym_env[mname] = _Binding(self.fresh(m_ty), m_ty)
            i_var = self.fresh(elem_type)
            sym_env[var_name] = _Binding(i_var, elem_type)
            ge_op = f"int_ge_{elem_spec.name}" if elem_spec is not None else ">="
            lt_op = f"int_lt_{elem_spec.name}" if elem_spec is not None else "<"
            add_op = f"int_add_{elem_spec.name}" if elem_spec is not None else "+"
            one_term = _int_term(elem_spec, 1) if elem_spec is not None else _term("nat", value=1)
            next_i = _apps(_constant(add_op), i_var, one_term)
            saved_facts_len = len(self.active_facts)
            self.active_facts.append(_apps(_constant(ge_op), i_var, start_term))
            self.active_facts.append(_apps(_constant(lt_op), i_var, end_term))
            assumed = self._assume_loop_invariants(contracts, sym_env)
            self.active_facts.extend(assumed)
            try:
                before_sym_m = self._eval_loop_decreases(contracts, sym_env)
                pre_env, _ = self._non_returning_statements(
                    {"kind": "block", "span": body_node["span"], "statements": prefix_stmts}, sym_env, facts
                )
                pre_mutable = set(self.mutable_locals)
                pre_uninit = set(self.uninitialized_out_params)
                pre_indexed = dict(self.indexed_local_borrows)
                pre_peer_len = len(self.indexed_borrow_peers)
                pre_slice_views = dict(self.slice_views)
                pre_own_updates = {k: set(v) for k, v in self.slice_view_own_updates.items()}
                cond_raw = self.node(if_stmt["condition"])
                condition = self.check(cond_raw, _BOOL, pre_env)
                self._consume_call_updates(pre_env, cond_raw)
                lint_branch(self, cond_raw, condition, pre_env)
                self.active_facts.append(condition)
                ret_term: _Term | None = None
                try:
                    then_env, _ = self._non_returning_statements(
                        {"kind": "block", "span": if_stmt["span"], "statements": then_prefix},
                        dict(pre_env),
                        (*facts, *self._branch_guard(condition, True)),
                    )
                    if self.active_lift_scopes > 0:
                        raise self.fail(
                            "type",
                            "cannot return from a callable while a record invariant is lifted in an enclosing scope",
                            ret_stmt,
                        )
                    if ret_stmt["value"] is None:
                        if self.uninitialized_out_params:
                            uninit_list = ", ".join(sorted(self.uninitialized_out_params))
                            raise self.fail(
                                "type",
                                f"cannot return before 'out' parameter '{uninit_list}' is initialized",
                                ret_stmt,
                            )
                        ret_b = _Binding(_term("unit"), _UNIT)
                        self.unify(ret_b.type, ret_type)
                    else:
                        ret_term = self.check(self.node(ret_stmt["value"]), ret_type, then_env)
                        self._consume_call_updates(then_env, ret_stmt)
                        if self._term_hr_region(ret_term, then_env) is not None:
                            raise self.fail(
                                "type",
                                "cannot return value borrowing higher-ranked callback region outside its invocation",
                                ret_stmt,
                            )
                        self._check_span_view_use(ret_term, then_env, ret_stmt, use="return", baseline=sym_env)
                        ret_b = _Binding(ret_term, ret_type)
                    then_env = self._leave_statement_scope(pre_env.keys(), then_env)
                finally:
                    self.active_facts.pop()
                    self.mutable_locals = set(pre_mutable)
                    self.uninitialized_out_params = set(pre_uninit)
                    self.indexed_local_borrows = dict(pre_indexed)
                    del self.indexed_borrow_peers[pre_peer_len:]
                    self.slice_views = dict(pre_slice_views)
                    self.slice_view_own_updates = {k: set(v) for k, v in pre_own_updates.items()}
                self.active_facts.append(self._negate_bool_term(condition))
                try:
                    cont_env, _ = self._elaborate_non_returning_block(
                        {"kind": "block", "span": body_node["span"], "statements": suffix_stmts},
                        dict(pre_env),
                        (*facts, *self._branch_guard(condition, False)),
                    )
                    cont_env = self._leave_statement_scope(sym_env.keys(), cont_env)
                    if ret_term is not None:
                        span_u8 = _app(_constant("Span"), _U8)
                        j_var = self.fresh(elem_type)
                        iter_check_env = dict(extended)
                        changed_in_step = False
                        for k_name, k_ext in extended.items():
                            if (
                                k_name in self.entry_env
                                and self.entry_env[k_name].term.kind == "var"
                                and self.entry_env[k_name].term.value in self.ref_parameters
                                and self.whnf(k_ext.type) == span_u8
                                and k_name in cont_env
                                and k_name in sym_env
                                and cont_env[k_name].term != sym_env[k_name].term
                            ):
                                changed_in_step = True
                                step_t = cont_env[k_name].term
                                if sym_env[k_name].term.kind == "var":
                                    step_t = self.substitute(step_t, cast("int", sym_env[k_name].term.value), k_ext.term)
                                step_t = self.substitute(step_t, cast("int", i_var.value), j_var)
                                iter_check_env[k_name] = _Binding(step_t, k_ext.type)
                        if changed_in_step:
                            saved_j_facts = len(self.active_facts)
                            self.active_facts.append(_apps(_constant(ge_op), j_var, start_term))
                            self.active_facts.append(_apps(_constant(lt_op), j_var, i_var))
                            try:
                                self._check_span_view_use(
                                    ret_term, iter_check_env, ret_stmt, use="return", baseline=extended
                                )
                            finally:
                                del self.active_facts[saved_j_facts:]
                    step_env = dict(sym_env)
                    for k in list(sym_env):
                        if k != var_name and k in cont_env and k in self.mutable_locals:
                            step_env[k] = cont_env[k]
                    step_env[var_name] = _Binding(next_i, elem_type)
                    self._check_loop_invariants(contracts, step_env, statement, "inductive step")
                    self._check_loop_decreases(before_sym_m, step_env, "inductive step")
                finally:
                    self.active_facts.pop()
            finally:
                self.uninitialized_out_params = saved_uninit
                del self.active_facts[saved_facts_len:]
            changed = [
                name for name in extended
                if name in saved_mutable and name != var_name
                and (sym_env[name].term != cont_env[name].term or sym_env[name].term != then_env[name].term)
            ]
            ordinal = self.fresh(_NAT)
            start_nat = self._loop_nat(start_term, elem_spec)
            count = _apps(_constant("-"), self._loop_nat(end_term, elem_spec), start_nat)
            index = _apps(_constant("+"), start_nat, ordinal)
            if elem_spec is not None:
                index = _app(_constant("nat_to_usize"), index)
                if elem_type != _USIZE:
                    index = _app(_constant(f"int_from_usize_{elem_spec.name}"), index)
            step_cond = self.substitute(condition, cast("int", i_var.value), index)
            step_ret = self.substitute(ret_b.term, cast("int", i_var.value), index)
            then_sub = dict(then_env)
            cont_sub = dict(cont_env)
            for name in changed:
                then_sub[name] = _Binding(
                    self.substitute(then_env[name].term, cast("int", i_var.value), index), then_env[name].type
                )
                cont_sub[name] = _Binding(
                    self.substitute(cont_env[name].term, cast("int", i_var.value), index), cont_env[name].type
                )
            names = tuple(changed)
            status_type = _term("sum", _UNIT, ret_type)
            init_status = _Binding(_term("inl", _UNIT, ret_type, _term("unit")), status_type)
            initial = self._pack_guard_state(names, extended, init_status)
            state = self.fresh(initial.type)
            current, st_status = self._unpack_guard_state(names, extended, _Binding(state, initial.type))
            ret_state = self._pack_guard_state(
                names, then_sub, _Binding(_term("inr", _UNIT, ret_type, step_ret), status_type)
            ).term
            cont_state = self._pack_guard_state(names, cont_sub, init_status).term
            branch_state = self._at_loop_entry(_term("if", initial.type, step_cond, ret_state, cont_state), sym_env, current)
            step_body = self._sum_match_result(
                st_status.term, status_type, initial.type, lambda _u: branch_state, lambda _r: state
            )
            folded = _apps(
                _constant("NatFold"), initial.type, self.wrap("lam", [ordinal, state], step_body), initial.term, count
            )
            loop_env, final_status = self._unpack_guard_state(names, extended, _Binding(folded, initial.type))
            span_u8 = _app(_constant("Span"), _U8)
            for name in changed:
                if self.whnf(extended[name].type) == span_u8 and all(
                    self.convertible(
                        _apps(_constant(f"Span_{ftag}"), _U8, branch_env[name].term),
                        _apps(_constant(f"Span_{ftag}"), _U8, sym_env[name].term),
                    )
                    for branch_env in (then_env, cont_env)
                    for ftag in ("Base", "Length", "Tag", "PermRead", "PermWrite")
                ):
                    restored_span = _apps(_constant("Span_ReplaceStore"), _U8, extended[name].term, loop_env[name].term)
                    loop_env[name] = _Binding(restored_span, extended[name].type)
        finally:
            self.in_loop_depth -= 1
            self.mutable_locals = saved_mutable
        post_env = dict(loop_env)
        post_env[var_name] = _Binding(end_term, elem_type)
        post_assumed = self._assume_loop_invariants(contracts, post_env)
        saved_post_facts = len(self.active_facts)
        self.active_facts.extend(post_assumed)
        try:
            fallthrough = self.block(
                {"kind": "block", "span": statement["span"], "statements": rest_statements},
                post_env,
                ret_type,
                facts=facts,
            )
            fallthrough_refs = dict(self.final_ref_bindings)
        finally:
            del self.active_facts[saved_post_facts:]
        combined_term = self._sum_match_result(
            final_status.term, status_type, ret_type, lambda _u: fallthrough.term, lambda r: r
        )
        merged_refs = dict(loop_env)
        for rk in set(loop_env) & set(fallthrough_refs):
            lb = loop_env[rk]
            fb = fallthrough_refs[rk]
            if lb.term != fb.term:
                merged_refs[rk] = _Binding(
                    self._sum_match_result(
                        final_status.term,
                        status_type,
                        lb.type,
                        lambda _u, f_term=fb.term: f_term,
                        lambda _r, l_term=lb.term: l_term,
                    ),
                    lb.type,
                )
            else:
                merged_refs[rk] = fb
        self.final_ref_bindings = merged_refs
        return _Binding(combined_term, ret_type)

    def _elaborate_foreach_statement(
        self: _Elaborator,
        statement: Node,
        extended: dict[str, _Binding],
        facts: tuple[_Binding, ...],
    ) -> dict[str, _Binding]:
        self.site = statement
        start_term, end_term, elem_type, elem_spec, var_name, contracts, body_node = self._parse_foreach_range(
            statement, extended
        )
        start_w = self.whnf(start_term)
        end_w = self.whnf(end_term)
        saved_mutable = set(self.mutable_locals)
        self.mutable_locals.discard(var_name)
        self.in_loop_depth += 1
        try:
            # Check the loop invariants with the iteration variable at the lower bound.
            entry_env = dict(extended)
            entry_env[var_name] = _Binding(start_term, elem_type)
            self._check_loop_invariants(contracts, entry_env, statement, "entry")
            self._eval_loop_decreases(contracts, entry_env)
            range_loop(self, statement, contracts, extended, start_term, end_term, elem_spec)
            if (
                start_w.kind in {"nat", "int"}
                and end_w.kind in {"nat", "int"}
                and cast("int", end_w.value) - cast("int", start_w.value) <= 64
            ):
                s_val = cast("int", start_w.value)
                e_val = cast("int", end_w.value)
                cur_env = dict(extended)
                broke = False
                for i_val in range(s_val, e_val):
                    i_term = (
                        _int_term(elem_spec, i_val)
                        if elem_spec is not None
                        else _term("nat", value=i_val)
                    )
                    next_term = (
                        _int_term(elem_spec, i_val + 1)
                        if elem_spec is not None
                        else _term("nat", value=i_val + 1)
                    )
                    iter_env = dict(cur_env)
                    iter_env[var_name] = _Binding(i_term, elem_type)
                    before_m = self._eval_loop_decreases(contracts, iter_env)
                    self.mutable_locals.discard(var_name)
                    after_iter, ctrl = self._elaborate_non_returning_block(body_node, iter_env, facts)
                    for k in list(cur_env):
                        if k != var_name and k in after_iter and k in self.mutable_locals:
                            cur_env[k] = after_iter[k]
                    if ctrl == "break":
                        check_env = dict(cur_env)
                        check_env[var_name] = _Binding(i_term, elem_type)
                        self._check_loop_invariants(contracts, check_env, statement, "break")
                        broke = True
                        break
                    check_env = dict(cur_env)
                    check_env[var_name] = _Binding(next_term, elem_type)
                    self._check_loop_invariants(contracts, check_env, statement, "step")
                    self._check_loop_decreases(before_m, check_env, "step")
                if not broke:
                    end_env = dict(cur_env)
                    end_env[var_name] = _Binding(end_term, elem_type)
                    proved = self._check_loop_invariants(contracts, end_env, statement, "exit")
                    self.active_facts.extend(proved)
                return cur_env

            # Symbolic range induction
            saved_uninit = set(self.uninitialized_out_params)
            sym_env = dict(extended)
            for mname in list(self.mutable_locals):
                if mname in sym_env and mname != var_name:
                    m_ty = sym_env[mname].type
                    sym_env[mname] = _Binding(self.fresh(m_ty), m_ty)
            i_var = self.fresh(elem_type)
            sym_env[var_name] = _Binding(i_var, elem_type)
            ge_op = f"int_ge_{elem_spec.name}" if elem_spec is not None else ">="
            lt_op = f"int_lt_{elem_spec.name}" if elem_spec is not None else "<"
            add_op = f"int_add_{elem_spec.name}" if elem_spec is not None else "+"
            one_term = _int_term(elem_spec, 1) if elem_spec is not None else _term("nat", value=1)
            next_i = _apps(_constant(add_op), i_var, one_term)
            saved_facts_len = len(self.active_facts)
            self.active_facts.append(_apps(_constant(ge_op), i_var, start_term))
            self.active_facts.append(_apps(_constant(lt_op), i_var, end_term))
            assumed = self._assume_loop_invariants(contracts, sym_env)
            self.active_facts.extend(assumed)
            try:
                before_sym_m = self._eval_loop_decreases(contracts, sym_env)
                after_sym, _ = self._elaborate_non_returning_block(body_node, sym_env, facts)
                step_env = dict(sym_env)
                for k in list(sym_env):
                    if k != var_name and k in after_sym and k in self.mutable_locals:
                        step_env[k] = after_sym[k]
                step_env[var_name] = _Binding(next_i, elem_type)
                self._check_loop_invariants(contracts, step_env, statement, "inductive step")
                self._check_loop_decreases(before_sym_m, step_env, "inductive step")
            finally:
                self.uninitialized_out_params = saved_uninit
                del self.active_facts[saved_facts_len:]
            if self._contains_break_statement(body_node):
                raise self.fail("unsupported", "symbolic range break needs a represented early-exit state", statement)
            if elem_spec is not None and elem_spec.signed:
                raise self.fail("unsupported", "symbolic signed ranges need a signed distance representation", statement)
            changed = [name for name in extended if name in self.mutable_locals and name != var_name
                       and sym_env[name].term != step_env[name].term]
            post_env = dict(extended)
            zero = _int_term(elem_spec, 0) if elem_spec else _term("nat", value=0)
            if len(changed) == 1 and self.whnf(start_term) == zero:
                name = changed[0]
                before = sym_env[name].term
                step = self.whnf(step_env[name].term)
                head, args = self.spine(step)
                if self.whnf(post_env[name].term) == zero and step == self.whnf(_apps(_constant(add_op), before, one_term)):
                    post_env[name] = _Binding(end_term, elem_type)
                    changed.clear()
                elif (elem_type == _USIZE and head == _constant("Span_Write") and len(args) == 4
                      and args[1] == before and args[2] == i_var
                      and not self.free(args[3]).intersection(self.free(i_var) | self.free(before))):
                    value = self._at_loop_entry(args[3], sym_env, extended)
                    filled = _apps(_constant("Span_Fill"), _U8, extended[name].term, zero, end_term, value)
                    post_env[name] = _Binding(filled, extended[name].type)
                    changed.clear()
            if changed:
                ordinal = self.fresh(_NAT)
                start_nat = self._loop_nat(start_term, elem_spec)
                count = _apps(_constant("-"), self._loop_nat(end_term, elem_spec), start_nat)
                index = _apps(_constant("+"), start_nat, ordinal)
                if elem_spec is not None:
                    index = _app(_constant("nat_to_usize"), index)
                    if elem_type != _USIZE:
                        index = _app(_constant(f"int_from_usize_{elem_spec.name}"), index)
                for name in changed:
                    step_env[name] = _Binding(self.substitute(step_env[name].term, cast("int", i_var.value), index),
                                              step_env[name].type)
                post_env = self._fold_loop(extended, sym_env, step_env, changed, count, ordinal)
            post_env_with_idx = dict(post_env)
            post_env_with_idx[var_name] = _Binding(end_term, elem_type)
            post_assumed = self._assume_loop_invariants(contracts, post_env_with_idx)
            self.active_facts.extend(post_assumed)
            return post_env
        finally:
            self.in_loop_depth -= 1
            self.mutable_locals = saved_mutable

    @staticmethod
    def _loop_nat(value: _Term, spec: _IntSpec | None) -> _Term:
        return value if spec is None else _app(_constant(f"int_to_nat_{spec.name}"), value)

    def _at_loop_entry(
        self: _Elaborator, term: _Term, symbolic: dict[str, _Binding], entry: dict[str, _Binding],
    ) -> _Term:
        for name, original in entry.items():
            variable = symbolic[name].term
            if variable.kind == "var" and variable != original.term:
                term = self.substitute(term, cast("int", variable.value), original.term)
        return term

    def _fold_loop(
        self: _Elaborator, entry: dict[str, _Binding], symbolic: dict[str, _Binding],
        after: dict[str, _Binding], changed: list[str], count: _Term, ordinal: _Term,
        condition: _Term | None = None,
        *,
        stop_after: _Term | None = None,
    ) -> dict[str, _Binding]:
        names = tuple(changed)
        status = _Binding(_term("unit"), _UNIT) if stop_after is None else _Binding(_term("bool", value=0), _BOOL)
        initial = self._pack_guard_state(names, entry, status)
        state = self.fresh(initial.type)
        current, stopped = self._unpack_guard_state(names, entry, _Binding(state, initial.type))
        step_status = status if stop_after is None else _Binding(stop_after, _BOOL)
        step = self._pack_guard_state(names, after, step_status).term
        if condition is not None:
            step = _term("if", initial.type, condition, step, state)
        if stop_after is not None:
            # Write back the element on its breaking step before freezing the loop state.
            step = _term("if", initial.type, stopped.term, state, step)
        step = self._at_loop_entry(step, symbolic, current)
        function = self.wrap("lam", [ordinal, state], step)
        folded = _apps(_constant("NatFold"), initial.type, function, initial.term, count)
        result, _ = self._unpack_guard_state(names, entry, _Binding(folded, initial.type))
        return result

    def _symbolic_span_aliases(self: _Elaborator, owner: str, environment: dict[str, _Binding]) -> set[str]:
        root = self._root_span(environment[owner].term)
        backing_variables = self.free(root)
        return {
            name for name, binding in environment.items()
            if name != owner and self._static_scalar_kind(self.whnf(binding.type)) is None
            and (self._root_span(binding.term) == root or self.free(binding.term) & backing_variables)
        }

    def _elaborate_foreach_collection_statement(
        self: _Elaborator,
        statement: Node,
        extended: dict[str, _Binding],
        facts: tuple[_Binding, ...],
    ) -> dict[str, _Binding]:
        self.site = statement
        mode = cast("str", statement["mode"])
        var_name = self.name(statement["name"])
        coll_node = self._unwrap_group(self.node(statement["collection"]))
        if coll_node["kind"] == "range":
            if mode != "value":
                raise self.fail("type", "range iteration only supports 'let' value elements", statement)
            return self._elaborate_foreach_statement(
                {
                    "kind": "foreach",
                    "span": statement["span"],
                    "name": statement["name"],
                    "type": statement["type"],
                    "range": coll_node,
                    "contracts": statement["contracts"],
                    "body": statement["body"],
                },
                extended,
                facts,
            )
        coll_name = self.name(coll_node["name"]) if coll_node["kind"] == "name" else None
        if coll_name is not None and coll_name in self.frozen_collections:
            raise self.fail("type", f"collection '{coll_name}' is already being iterated", coll_node)
        coll_b = self.expression(coll_node, extended)
        if mode == "ref":
            if coll_name is None or coll_name not in self.mutable_locals:
                raise self.fail(
                    "type",
                    "foreach 'ref' element iteration requires a mutable 'var' or 'ref' collection variable",
                    coll_node,
                )
            if self._is_readonly_span(coll_b.term):
                raise self.fail(
                    "type",
                    f"cannot iterate with 'ref' over read-only 'in' parameter '{coll_name}'",
                    coll_node,
                )
        coll_ty = self.whnf(coll_b.type)
        c_head, c_args = self.spine(coll_ty)
        kind_tag = ""
        if c_head == _constant("Span") and len(c_args) == 1 and self.whnf(c_args[0]) == _U8:
            kind_tag = "span"
            elem_type = _U8
            self._check_span_can_read(coll_b.term, extended, coll_node)
            self._check_span_view_use(coll_b.term, extended, coll_node, use="read")
            if mode == "ref":
                self._check_span_can_write(coll_b.term, extended, coll_node)
            len_t = self.whnf(_apps(_constant("Span_Length"), _U8, coll_b.term))
            concrete_len = cast("int", len_t.value) if len_t.kind == "int" else None
        elif c_head == _constant("Slots") and len(c_args) == 2:
            kind_tag = "slots"
            elem_type = c_args[0]
            slots_cap = c_args[1]
            can_r = _apps(_constant("Slots_CanRead"), elem_type, slots_cap, coll_b.term)
            if not self._prove_bool_precondition(can_r, extended):
                raise self.fail("type", "cannot prove Slots.CanRead for collection iteration", coll_node)
            if mode == "ref":
                can_w = _apps(_constant("Slots_CanWrite"), elem_type, slots_cap, coll_b.term)
                if not self._prove_bool_precondition(can_w, extended):
                    raise self.fail("type", "cannot prove Slots.CanWrite for 'ref' collection iteration", coll_node)
            live_t = self.whnf(_apps(_constant("Slots_LiveCount"), elem_type, slots_cap, coll_b.term))
            concrete_len = cast("int", live_t.value) if live_t.kind == "int" else None
        elif c_head == _constant("Vec") and len(c_args) == 2:
            kind_tag = "vec"
            elem_type = c_args[0]
            len_t = self.whnf(c_args[1])
            concrete_len = cast("int", len_t.value) if len_t.kind == "nat" else None
        elif c_head == _constant("Seq") and len(c_args) == 1:
            if mode == "ref":
                raise self.fail(
                    "type", "pure sequence 'Seq<T>' does not support mutable 'ref' element iteration", statement
                )
            kind_tag = "seq"
            elem_type = c_args[0]
            cnt_t = self.whnf(_apps(_constant("Seq_Count"), elem_type, coll_b.term))
            concrete_len = cast("int", cnt_t.value) if cnt_t.kind == "nat" else None
        else:
            raise self.fail(
                "type",
                "foreach collection must have type Vec<T, n>, Span<byte>, Slots<T, capacity> or Seq<T>",
                coll_node,
            )
        if statement["type"] is not None:
            ann_type = self.type(self.node(statement["type"]), extended)
            self.unify(elem_type, ann_type)
        contracts = self.nodes(statement["contracts"])
        body_node = self.node(statement["body"], "block")
        saved_mutable = set(self.mutable_locals)
        saved_readonly = set(self.readonly_span_vars)
        if coll_name is not None:
            self.frozen_collections.add(coll_name)
        self.in_loop_depth += 1
        try:
            self._check_loop_invariants(contracts, extended, statement, "entry")
            self._eval_loop_decreases(contracts, extended)
            cur_env = dict(extended)
            if concrete_len is not None and 0 <= concrete_len <= 64:
                cur_coll_term = coll_b.term
                for idx in range(concrete_len):
                    if kind_tag == "span":
                        idx_u = _int_term(_INT_SPECS["usize"], idx)
                        elem_term = self.whnf(_apps(_constant("Span_Read"), _U8, cur_coll_term, idx_u))
                    elif kind_tag == "slots":
                        idx_u = _int_term(_INT_SPECS["usize"], idx)
                        model = _apps(_constant("Slots_Model"), elem_type, c_args[1], cur_coll_term)
                        d_val = self._sequence_lookup_default(elem_type, model)
                        elem_term = self.whnf(
                            _apps(_constant("Slots_Read"), elem_type, c_args[1], d_val, cur_coll_term, idx_u)
                        )
                    else:
                        seq_m = (
                            self.whnf(_apps(_constant("Vec_Model"), elem_type, c_args[1], cur_coll_term))
                            if kind_tag == "vec"
                            else cur_coll_term
                        )
                        d_val = self._sequence_lookup_default(elem_type, seq_m)
                        elem_term = self.whnf(
                            _apps(_constant("Seq_At"), elem_type, d_val, seq_m, _term("nat", value=idx))
                        )
                    iter_env = dict(cur_env)
                    if mode == "ref":
                        self.mutable_locals.add(var_name)
                        iter_env[var_name] = _Binding(elem_term, elem_type)
                    else:
                        self.mutable_locals.discard(var_name)
                        if mode == "in":
                            v_fresh = self.fresh(elem_type)
                            self.readonly_span_vars.add(cast("int", v_fresh.value))
                            iter_env[var_name] = _Binding(elem_term, elem_type)
                        else:
                            iter_env[var_name] = _Binding(elem_term, elem_type)
                    before_m = self._eval_loop_decreases(contracts, iter_env)
                    after_iter, ctrl = self._elaborate_non_returning_block(body_node, iter_env, facts)
                    for k in list(cur_env):
                        if k != var_name and k in after_iter and k in self.mutable_locals:
                            cur_env[k] = after_iter[k]
                    if mode == "ref" and coll_name is not None:
                        new_elem = after_iter[var_name].term
                        if kind_tag == "span":
                            idx_u = _int_term(_INT_SPECS["usize"], idx)
                            cur_coll_term = _apps(_constant("Span_Write"), _U8, cur_coll_term, idx_u, new_elem)
                            cur_env[coll_name] = _Binding(cur_coll_term, coll_b.type)
                        elif kind_tag == "slots":
                            idx_u = _int_term(_INT_SPECS["usize"], idx)
                            cur_coll_term = _apps(
                                _constant("Slots_Write"), elem_type, c_args[1], cur_coll_term, idx_u, new_elem
                            )
                            cur_env[coll_name] = _Binding(cur_coll_term, coll_b.type)
                        elif kind_tag == "vec":
                            cur_coll_term = self._update_vec_at(elem_type, cur_coll_term, idx, new_elem)
                            cur_env[coll_name] = _Binding(cur_coll_term, coll_b.type)
                    if ctrl == "break":
                        self._check_loop_invariants(contracts, cur_env, statement, "break")
                        break
                    self._check_loop_invariants(contracts, cur_env, statement, "step")
                    self._check_loop_decreases(before_m, cur_env, "step")
                return cur_env

            # Symbolic collection iteration
            saved_uninit = set(self.uninitialized_out_params)
            sym_env = dict(extended)
            for mname in list(self.mutable_locals):
                if mname in sym_env and mname not in {var_name, coll_name}:
                    m_ty = sym_env[mname].type
                    sym_env[mname] = _Binding(self.fresh(m_ty), m_ty)
            lends_span = mode == "ref" and kind_tag == "span"
            span_owner = None
            owner_access = None
            aliases: set[str] = set()
            ordinal = self.fresh(_NAT)
            index = _app(_constant("nat_to_usize"), ordinal)
            if (lends_span and coll_name is not None and coll_name != var_name
                    and coll_name not in self.local_borrows and coll_name not in self.slice_views):
                # The model writes through the element at the scope exit. Any
                # other access would require checked alias liveness and restoration.
                aliases = self._symbolic_span_aliases(coll_name, extended)
                suspended = aliases | {coll_name}
                owner_access = next(
                    (node for node in _walk(body_node)
                     if node["kind"] == "name" and self.name(node["name"]) in suspended), None,
                )
                if owner_access is None and not aliases:
                    span_owner = coll_name
                    sym_env[span_owner] = _Binding(self.fresh(coll_b.type), coll_b.type)
            elem_var = self.fresh(elem_type)
            if mode == "ref":
                self.mutable_locals.add(var_name)
            else:
                self.mutable_locals.discard(var_name)
                if mode == "in":
                    self.readonly_span_vars.add(cast("int", elem_var.value))
            sym_env[var_name] = _Binding(elem_var, elem_type)
            saved_facts_len = len(self.active_facts)
            if span_owner is not None:
                current = sym_env[span_owner].term
                length = _apps(_constant("Span_Length"), _U8, current)
                entry_length = _apps(_constant("Span_Length"), _U8, coll_b.term)
                self.active_facts.extend((
                    _apps(_constant("Span_CanRead"), _U8, current),
                    _apps(_constant("Span_CanWrite"), _U8, current),
                    _apps(_constant("int_eq_usize"), length, entry_length),
                ))
            if kind_tag == "span":
                coll_model = self.whnf(_apps(_constant("Span_Model"), _U8, coll_b.term))
            elif kind_tag == "slots":
                coll_model = self.whnf(_apps(_constant("Slots_Model"), elem_type, c_args[1], coll_b.term))
            elif kind_tag == "vec":
                coll_model = self.whnf(_apps(_constant("Vec_Model"), elem_type, c_args[1], coll_b.term))
            else:
                coll_model = self.whnf(coll_b.term)
            for f_term in self._expand_bool_facts([*self.active_facts, *self._fact_bool_terms(facts, extended)]):
                f_head, f_args = self.spine(f_term)
                if f_head == _constant("Seq_All") and len(f_args) == 3 and self.convertible(f_args[1], coll_model):
                    self.active_facts.append(self.whnf(_app(f_args[2], elem_var)))
            assumed = self._assume_loop_invariants(contracts, sym_env)
            self.active_facts.extend(assumed)
            prior_element_write = lends_span and var_name in self.runtime_writes
            if lends_span:
                self.runtime_writes.discard(var_name)
            terminal_break: list[_Term] | None = [] if lends_span else None
            stop_after = None
            try:
                before_sym_m = self._eval_loop_decreases(contracts, sym_env)
                after_sym, control = self._elaborate_non_returning_block(
                    body_node, sym_env, facts, terminal_break=terminal_break,
                )
                if span_owner is not None:
                    if control == "break":
                        stop_after = _term("bool", value=1)
                    elif terminal_break is not None and terminal_break:
                        stop_after = terminal_break[0]
                writes_element = after_sym[var_name].term != elem_var or (
                    lends_span and var_name in self.runtime_writes
                )
                step_env = dict(sym_env)
                for k in list(sym_env):
                    if k != var_name and k in after_sym and k in self.mutable_locals:
                        step_env[k] = after_sym[k]
                if span_owner is not None and writes_element:
                    current = sym_env[span_owner]
                    if step_env[span_owner] != current:
                        raise self.fail("type", f"cannot mutate suspended Span owner '{span_owner}' during element iteration",
                                        statement)
                    step_env[span_owner] = _Binding(
                        _apps(_constant("Span_Write"), _U8, current.term, index, after_sym[var_name].term), current.type,
                    )
                    self._note_runtime_write(coll_node)
                if stop_after is not None:
                    self.active_facts.append(stop_after)
                    try:
                        self._check_loop_invariants(contracts, step_env, statement, "break")
                    finally:
                        self.active_facts.pop()
                if stop_after != _term("bool", value=1):
                    if stop_after is not None:
                        self.active_facts.append(self._negate_bool_term(stop_after))
                    self._check_loop_invariants(contracts, step_env, statement, "inductive step")
                    self._check_loop_decreases(before_sym_m, step_env, "inductive step")
            finally:
                if prior_element_write:
                    self.runtime_writes.add(var_name)
                self.uninitialized_out_params = saved_uninit
                del self.active_facts[saved_facts_len:]
            if mode == "ref" and span_owner is None and writes_element:
                if owner_access is not None:
                    raise self.fail("type", f"cannot access suspended Span owner '{coll_name}' during element iteration",
                                    owner_access)
                if aliases:
                    names = ", ".join(sorted(aliases))
                    raise self.fail("type", f"cannot establish exclusive iteration of '{coll_name}' with retained "
                                    f"Span views or aliases ({names})", statement)
                raise self.fail("unsupported", "symbolic mutable element iteration needs represented writeback", statement)
            if stop_after is None and self._contains_break_statement(body_node):
                raise self.fail("unsupported", "symbolic collection break needs a represented early-exit state", statement)
            changed = [name for name in extended if name in self.mutable_locals and name != var_name
                       and sym_env[name].term != step_env[name].term]
            if changed:
                if span_owner is not None:
                    element = _apps(_constant("Span_Read"), _U8, sym_env[span_owner].term, index)
                    count = _app(_constant("int_to_nat_usize"), _apps(_constant("Span_Length"), _U8, coll_b.term))
                else:
                    default = self._sequence_lookup_default(elem_type, coll_model)
                    element = _apps(_constant("Seq_At"), elem_type, default, coll_model, ordinal)
                    count = _apps(_constant("Seq_Count"), elem_type, coll_model)
                for name in changed:
                    step_env[name] = _Binding(self.substitute(step_env[name].term, cast("int", elem_var.value), element),
                                              step_env[name].type)
                if stop_after is not None:
                    stop_after = self.substitute(stop_after, cast("int", elem_var.value), element)
                cur_env = self._fold_loop(extended, sym_env, step_env, changed, count, ordinal, stop_after=stop_after)
                if span_owner is not None and span_owner in changed:
                    restored = _apps(_constant("Span_ReplaceStore"), _U8, coll_b.term, cur_env[span_owner].term)
                    cur_env[span_owner] = _Binding(restored, coll_b.type)
            post_assumed = self._assume_loop_invariants(contracts, cur_env)
            self.active_facts.extend(post_assumed)
            return cur_env
        finally:
            self.in_loop_depth -= 1
            if coll_name is not None:
                self.frozen_collections.discard(coll_name)
            self.mutable_locals = saved_mutable
            self.readonly_span_vars = saved_readonly

    def _elaborate_while_statement(
        self: _Elaborator,
        statement: Node,
        extended: dict[str, _Binding],
        facts: tuple[_Binding, ...],
    ) -> dict[str, _Binding]:
        self.site = statement
        contracts = self.nodes(statement["contracts"])
        cond_node = self.node(statement["condition"])
        body_node = self.node(statement["body"], "block")
        for contract in contracts:
            self.node(contract, "contract")
            if contract["role"] not in {"invariant", "decreases"}:
                raise self.fail("unsupported", f"loop contract '{contract['role']}' is not supported", contract)
        if not any(c["role"] == "decreases" for c in contracts):
            raise self.fail(
                "type",
                "while loop requires at least one 'decreases' termination contract",
                statement,
            )
        saved_mutable = set(self.mutable_locals)
        self.in_loop_depth += 1
        try:
            self._check_loop_invariants(contracts, extended, statement, "entry")
            self._eval_loop_decreases(contracts, extended)
            cur_env = dict(extended)
            unrolled_concretely = False
            concrete_steps = 0
            for _ in range(64):
                cond_t = self.check(cond_node, _BOOL, cur_env)
                if not concrete_steps:
                    while_entry(self, statement, cond_t, cur_env)
                cond_w = self.whnf(cond_t)
                if cond_w.kind != "bool":
                    break
                if cond_w.value == 0:
                    unrolled_concretely = True
                    break
                concrete_steps += 1
                before_m = self._eval_loop_decreases(contracts, cur_env)
                after_iter, ctrl = self._elaborate_non_returning_block(body_node, dict(cur_env), facts)
                next_env = dict(cur_env)
                for k in list(cur_env):
                    if k in after_iter and k in self.mutable_locals:
                        next_env[k] = after_iter[k]
                if ctrl == "break":
                    self._check_loop_invariants(contracts, next_env, statement, "break")
                    return next_env
                self._check_loop_invariants(contracts, next_env, statement, "step")
                self._check_loop_decreases(before_m, next_env, "step")
                cur_env = next_env
            else:
                cond_t = self.check(cond_node, _BOOL, cur_env)
                if self.whnf(cond_t) == _term("bool", value=0):
                    unrolled_concretely = True
            if unrolled_concretely and concrete_steps > 0:
                proved = self._check_loop_invariants(contracts, cur_env, statement, "exit")
                self.active_facts.extend(proved)
                return cur_env

            # Check the symbolic induction step even for a concrete zero-trip loop.
            saved_uninit = set(self.uninitialized_out_params)
            sym_env = dict(extended)
            for mname in list(self.mutable_locals):
                if mname in sym_env:
                    m_ty = sym_env[mname].type
                    sym_env[mname] = _Binding(self.fresh(m_ty), m_ty)
            sym_cond = self.check(cond_node, _BOOL, sym_env)
            saved_facts_len = len(self.active_facts)
            self.active_facts.append(sym_cond)
            assumed = self._assume_loop_invariants(contracts, sym_env)
            self.active_facts.extend(assumed)
            try:
                before_sym_m = self._eval_loop_decreases(contracts, sym_env)
                after_sym, sym_ctrl = self._elaborate_non_returning_block(body_node, sym_env, facts)
                step_env = dict(sym_env)
                for k in list(sym_env):
                    if k in after_sym and k in self.mutable_locals:
                        step_env[k] = after_sym[k]
                if sym_ctrl != "break":
                    self._check_loop_invariants(contracts, step_env, statement, "inductive step")
                    self._check_loop_decreases(before_sym_m, step_env, "inductive step")
            finally:
                self.uninitialized_out_params = saved_uninit
                del self.active_facts[saved_facts_len:]
            if unrolled_concretely:
                return cur_env
            if self._contains_break_statement(body_node):
                raise self.fail("unsupported", "symbolic while break needs a represented early-exit state", statement)
            changed = [name for name in extended if name in self.mutable_locals and sym_env[name].term != step_env[name].term]
            post_env = dict(extended)
            if len(changed) == 1:
                name = changed[0]
                initial = extended[name]
                spec = self._int_spec(initial.type)
                before = sym_env[name].term
                lt = _constant(f"int_lt_{spec.name}" if spec else "<")
                add = _constant(f"int_add_{spec.name}" if spec else "+")
                zero = _int_term(spec, 0) if spec else _term("nat", value=0)
                one = _int_term(spec, 1) if spec else _term("nat", value=1)
                head, args = self.spine(self.resolve(sym_cond))
                if (head == lt and len(args) == 2 and args[0] == before and (spec is None or not spec.signed)
                    and cast("int", before.value) not in self.free(args[1]) and self.whnf(initial.term) == zero
                    and self.whnf(step_env[name].term) == self.whnf(_apps(add, before, one))):
                    post_env[name] = _Binding(self._at_loop_entry(args[1], sym_env, extended), initial.type)
                    changed.clear()
            if changed:
                measures = self._eval_loop_decreases(contracts, extended)
                if len(measures) != 1:
                    raise self.fail("unsupported", "symbolic while execution needs a single natural-valued bound", statement)
                _, measure, spec = measures[0]
                post_env = self._fold_loop(extended, sym_env, step_env, changed, self._loop_nat(measure, spec),
                                           self.fresh(_NAT), sym_cond)
            post_assumed = self._assume_loop_invariants(contracts, post_env)
            self.active_facts.extend(post_assumed)
            post_cond = self.check(cond_node, _BOOL, post_env)
            self.active_facts.append(self._negate_bool_term(post_cond))
            return post_env
        finally:
            self.in_loop_depth -= 1
            self.mutable_locals = saved_mutable

    def _contains_break_statement(self: _Elaborator, node: Node) -> bool:
        kind = node.get("kind")
        if kind == "break":
            return True
        if kind in {"while", "foreach", "foreach_collection"}:
            return False
        if kind == "block":
            return any(self._contains_break_statement(st) for st in self.nodes(node["statements"]))
        if kind == "if":
            then_b = self._contains_break_statement(self.node(node["then"]))
            else_b = self._contains_break_statement(self.node(node["else"])) if node.get("else") is not None else False
            return then_b or else_b
        if kind in {"let_else", "var_else"}:
            return self._contains_break_statement(self.node(node["else"]))
        if kind == "open_invariant":
            return self._contains_break_statement(self.node(node["body"]))
        return False

    def _update_vec_at(self: _Elaborator, elem_type: _Term, vec_term: _Term, target_idx: int, new_val: _Term) -> _Term:
        v_w = self.whnf(vec_term)
        head, args = self.spine(v_w)
        if head == _constant("VCons") and len(args) == 4:
            if target_idx == 0:
                return _apps(_constant("VCons"), args[0], args[1], new_val, args[3])
            return _apps(
                _constant("VCons"),
                args[0],
                args[1],
                args[2],
                self._update_vec_at(elem_type, args[3], target_idx - 1, new_val),
            )
        return vec_term

    def block(self: _Elaborator, node: Node, environment: dict[str, _Binding], expected: _Term | None = None,
              *, facts: tuple[_Binding, ...] = ()) -> _Binding:
        self.node(node, "block")
        statements = self.nodes(node["statements"])
        extended = dict(environment)
        active_facts: list[_Binding] = list(facts)
        statement_facts: list[_Binding] = []
        peeled_vars: list[_Term] = []
        returns_lambda = False
        final_assert_value: Node | None = None
        if statements:
            last = statements[-1]
            if last["kind"] == "return" and isinstance(last.get("value"), dict):
                unwrapped = self._unwrap_group(cast("Node", last["value"]))
                returns_lambda = unwrapped["kind"] in {"lambda", "typed_lambda"}
            elif last["kind"] == "assert" and isinstance(last.get("value"), dict):
                final_assert_value = self._unwrap_group(cast("Node", last["value"]))
        if not returns_lambda:
            while expected is not None and self._is_prop_type(expected):
                resolved_expected = self.whnf(expected)
                if (resolved_expected.kind != "pi"
                        or cast("int", resolved_expected.value) in self.nullary_parameters):
                    break
                var_id = cast("int", resolved_expected.value)
                if var_id in self.parameter_names:
                    if final_assert_value is not None and final_assert_value["kind"] == "quantifier":
                        break
                    param_name = self.parameter_names[var_id]
                    if param_name in extended:
                        break
                    var = self.fresh(resolved_expected.args[0])
                    self.parameter_names[cast("int", var.value)] = param_name
                    self.bind_local(extended, param_name, _Binding(var, resolved_expected.args[0]))
                    if self._is_prop_type(resolved_expected.args[0]):
                        active_facts.append(_Binding(var, resolved_expected.args[0]))
                else:
                    if (final_assert_value is not None
                            and final_assert_value["kind"] == "binary"
                            and isinstance(final_assert_value.get("operator"), dict)
                            and cast("Node", final_assert_value["operator"]).get("text") == "==>"):
                        break
                    var = self.fresh(resolved_expected.args[0])
                    active_facts.append(_Binding(var, resolved_expected.args[0]))
                peeled_vars.append(var)
                expected = self.substitute(resolved_expected.args[1], var_id, var)

        def finish(result: _Binding) -> _Binding:
            if not peeled_vars:
                return result
            return _Binding(
                self.wrap("lam", peeled_vars, result.term),
                self.wrap("pi", peeled_vars, result.type),
            )

        def lift_stmt_propagate(
            stmt: Node, field_key: str, idx_stmt: int
        ) -> _Binding | None:
            raw_field = stmt.get(field_key)
            if raw_field is None:
                return None
            split_res = self._split_first_propagate(self.node(raw_field))
            if split_res is None:
                return None
            prop_node, rebuild = split_res
            target_ret = expected if expected is not None else self.current_return_type
            if target_ret is None:
                raise self.fail(
                    "type",
                    "'?' propagation requires an enclosing callable or block returning an Option or Result union",
                    prop_node,
                )
            combined_f = (*active_facts, *statement_facts)
            term = self._elaborate_propagate(
                prop_node,
                extended,
                target_ret,
                lambda temp_name, _ok_b, ok_env: self.block(
                    {
                        "kind": "block",
                        "span": node["span"],
                        "statements": [
                            {
                                **stmt,
                                field_key: rebuild(
                                    {
                                        "kind": "name",
                                        "span": prop_node["span"],
                                        "name": {"text": temp_name, "span": prop_node["span"]},
                                    }
                                ),
                            },
                            *statements[idx_stmt + 1:],
                        ],
                    },
                    ok_env,
                    target_ret,
                    facts=combined_f,
                ).term,
            )
            return finish(_Binding(term, target_ret))

        saved_active_len = len(self.active_facts)
        self.active_facts.extend(self._fact_bool_terms(active_facts, extended))
        try:
            for index, statement in enumerate(statements):
                self.site = statement
                kind = cast("str", statement["kind"])
                if kind == "guard_scope":
                    extended = self._leave_statement_scope(cast("tuple[str, ...]", statement["locals"]), extended)
                    continue
                if kind == "block" and index < len(statements) - 1:
                    extended, _ = self._elaborate_non_returning_block(
                        statement, extended, (*active_facts, *statement_facts),
                    )
                    continue
                if kind in {"let", "typed_local", "let_pattern", "constant_local", "var", "var_pattern"}:
                    if kind != "constant_local":
                        lifted = lift_stmt_propagate(statement, "value", index)
                        if lifted is not None:
                            return lifted
                    extended = self._local_with_facts(
                        statement, extended, statement_facts, record_active=True
                    )
                    continue
                if kind == "assignment":
                    lifted = lift_stmt_propagate(statement, "value", index)
                    if lifted is not None:
                        return lifted
                    extended = self._elaborate_assignment(statement, extended)
                    continue
                if kind == "expression_statement":
                    lifted = lift_stmt_propagate(statement, "value", index)
                    if lifted is not None:
                        return lifted
                    extended = self._elaborate_expression_statement(statement, extended)
                    continue
                if kind == "open_invariant":
                    extended = self._elaborate_scope_statement(
                        statement, extended, (*active_facts, *statement_facts)
                    )
                    continue
                if kind == "foreach":
                    if index < len(statements) - 1 and self._stmt_may_return(self.node(statement["body"], "block")):
                        if self._split_range_foreach_return(self.node(statement["body"], "block")) is not None:
                            return finish(
                                self._elaborate_returning_foreach_statement(
                                    statement, statements[index + 1:], extended, expected, (*active_facts, *statement_facts)
                                )
                            )
                        return finish(
                            self._elaborate_general_returning_loop(
                                statement, statements[index + 1:], extended, expected, (*active_facts, *statement_facts)
                            )
                        )
                    extended = self._elaborate_foreach_statement(
                        statement, extended, (*active_facts, *statement_facts)
                    )
                    continue
                if kind == "foreach_collection":
                    coll_node = self._unwrap_group(self.node(statement["collection"]))
                    if (
                        coll_node["kind"] == "range"
                        and statement["mode"] == "value"
                        and index < len(statements) - 1
                        and self._stmt_may_return(self.node(statement["body"], "block"))
                    ):
                        range_stmt: Node = {
                            "kind": "foreach",
                            "span": statement["span"],
                            "name": statement["name"],
                            "type": statement["type"],
                            "range": coll_node,
                            "contracts": statement["contracts"],
                            "body": statement["body"],
                        }
                        if self._split_range_foreach_return(self.node(statement["body"], "block")) is not None:
                            return finish(
                                self._elaborate_returning_foreach_statement(
                                    range_stmt, statements[index + 1:], extended, expected, (*active_facts, *statement_facts)
                                )
                            )
                        return finish(
                            self._elaborate_general_returning_loop(
                                range_stmt, statements[index + 1:], extended, expected, (*active_facts, *statement_facts)
                            )
                        )
                    extended = self._elaborate_foreach_collection_statement(
                        statement, extended, (*active_facts, *statement_facts)
                    )
                    continue
                if kind == "while":
                    if index < len(statements) - 1 and self._stmt_may_return(self.node(statement["body"], "block")):
                        return finish(
                            self._elaborate_general_returning_loop(
                                statement, statements[index + 1:], extended, expected, (*active_facts, *statement_facts)
                            )
                        )
                    extended = self._elaborate_while_statement(
                        statement, extended, (*active_facts, *statement_facts)
                    )
                    continue
                if kind in {"break", "continue"}:
                    raise self.fail("type", f"'{kind}' statement is only permitted inside a loop", statement)
                if kind in {"assert", "proof", "calc"}:
                    step_facts = self._statement_proof_facts(statement, extended, (*active_facts, *statement_facts))
                    if kind == "assert" and statement["by"] is None and index + 1 < len(statements):
                        observe(self, "HOLDFAST128", statement, "assertion repeats a proof fact already in scope"
                                if step_facts[0] in statement_facts else None)
                    statement_facts.extend(step_facts)
                    self.active_facts.extend(self._fact_bool_terms(tuple(step_facts), extended))
                    if index == len(statements) - 1:
                        self.final_ref_bindings = dict(extended)
                        self.final_return_facts = list(self.active_facts[saved_active_len:])
                        self.final_theorem_facts = tuple(statement_facts)
                        if self.in_post_env_theorem and expected is None:
                            return finish(statement_facts[-1] if statement_facts else _Binding(_constant("Tt"), _UNIT))
                        if expected is not None and self._is_prop_type(expected):
                            try:
                                term = self._prove_proposition(
                                    expected,
                                    extended,
                                    tuple(statement_facts),
                                    statement,
                                    allow_refl=False,
                                    include_env=False,
                                )
                                return finish(_Binding(term, expected))
                            except HoldFastError:
                                if self._entailed_by_theorem_facts(expected, extended):
                                    self.used_domain_solver_in_proof = True
                                    return finish(_Binding(_apps(_constant("Refl"), _BOOL, _term("bool", value=1)), expected))
                                raise
                    continue
                if kind in {"let_else", "var_else"}:
                    if index == len(statements) - 1:
                        raise self.fail(
                            "type",
                            f"a pure block requires an explicit terminal return after {kind.replace('_', '-')}",
                            statement,
                        )
                    lifted = lift_stmt_propagate(statement, "value", index)
                    if lifted is not None:
                        return lifted
                    else_block = self.node(statement["else"], "block")
                    else_statements = self.nodes(else_block["statements"])
                    rest_statements = statements[index + 1:]
                    combined_facts = (*active_facts, *statement_facts)
                    visited_arms: set[int] = set()
                    saved_mut = set(self.mutable_locals)
                    if kind == "var_else":
                        pat_preview = self._parse_pattern(self.node(statement["pattern"]), set())
                        pnames: set[str] = set()
                        self._collect_pat_names(pat_preview, pnames)
                        self.mutable_locals.update(pnames)
                    synthetic_match: Node = {
                        "kind": "match",
                        "span": node["span"],
                        "value": statement["value"],
                        "motive": None,
                        "cases": [
                            {
                                "kind": "case",
                                "span": node["span"],
                                "pattern": statement["pattern"],
                                "statements": rest_statements,
                            },
                            {
                                "kind": "case",
                                "span": else_block["span"],
                                "pattern": {"kind": "wildcard_pattern", "span": else_block["span"]},
                                "statements": else_statements,
                            },
                        ],
                    }
                    try:
                        saved_uninit_match = set(self.uninitialized_out_params)
                        result = self.match(
                            synthetic_match,
                            extended,
                            expected,
                            expression_arms=False,
                            facts=combined_facts,
                            refine_scrutinee=True,
                            visited_arms=visited_arms,
                            synthetic=True,
                        )
                        after_match_uninit = set(self.uninitialized_out_params)
                        if 1 not in visited_arms:
                            self.uninitialized_out_params = saved_uninit_match
                            self.block(else_block, extended, result.type, facts=combined_facts)
                            self.uninitialized_out_params = after_match_uninit
                    finally:
                        self.mutable_locals = saved_mut
                    return finish(result)
                if kind == "if" and index < len(statements) - 1:
                    operands = self._pattern_conjuncts(self.node(statement["condition"]))
                    if not operands:
                        lifted = lift_stmt_propagate(statement, "condition", index)
                        if lifted is not None:
                            return lifted
                    then_node = self.node(statement["then"])
                    then_stmts = (
                        self.nodes(then_node["statements"])
                        if then_node["kind"] == "block"
                        else [then_node]
                    )
                    else_raw = statement["else"]
                    else_stmts = (
                        None
                        if else_raw is None
                        else (
                            self.nodes(self.node(else_raw)["statements"])
                            if self.node(else_raw)["kind"] == "block"
                            else [self.node(else_raw)]
                        )
                    )
                    then_returns = bool(then_stmts and then_stmts[-1]["kind"] == "return")
                    else_returns = bool(else_stmts and else_stmts[-1]["kind"] == "return")
                    if not then_returns and not else_returns:
                        if self._stmt_may_return(statement):
                            target_ret = expected if expected is not None else self.current_return_type
                            if target_ret is None:
                                raise self.fail("type", "returning conditional requires a known return type", statement)
                            ref_names = tuple(n for n in sorted(self.entry_env) if n in self.mutable_locals and n in extended)
                            state_names = tuple(n for n in extended if n in self.mutable_locals)
                            acc_term, _, _ = self._elaborate_returning_block(
                                statements[index:], extended, target_ret, (*active_facts, *statement_facts),
                                snap_names=ref_names, state_names=state_names,
                            )
                            acc_t = self.infer(acc_term)
                            m_v = self.fresh(acc_t)
                            ret_pk_t = acc_t.args[0]
                            st_pk_t = acc_t.args[1]
                            rp = self.fresh(ret_pk_t)
                            rv, _ = self._unpack_names_with_head(ref_names, extended, _Binding(rp, ret_pk_t), target_ret)
                            sv = self.fresh(st_pk_t)
                            res_t = _term(
                                "sum_match",
                                _term("lam", acc_t, target_ret, value=m_v.value),
                                acc_term,
                                _term("lam", ret_pk_t, rv, value=rp.value),
                                _term("lam", st_pk_t, self._default_term_for_type(target_ret), value=sv.value),
                            )
                            self.final_ref_bindings = dict(extended)
                            self.final_return_facts = list(self.active_facts[saved_active_len:])
                            return finish(_Binding(res_t, target_ret))
                        extended, _ = self._elaborate_non_returning_block(
                            {"kind": "block", "span": statement["span"], "statements": [statement]},
                            extended,
                            (*active_facts, *statement_facts),
                        )
                        continue
                    rest_statements = statements[index + 1:]
                    leave_scope: Node = {"kind": "guard_scope", "span": statement["span"], "locals": tuple(extended)}
                    if then_returns and else_stmts is None:
                        cur_stmt: Node = {
                            **statement,
                            "else": {
                                "kind": "block",
                                "span": node["span"],
                                "statements": rest_statements,
                            },
                        }
                    elif then_returns and not else_returns and else_stmts is not None:
                        cur_stmt = {
                            **statement,
                            "else": {
                                "kind": "block",
                                "span": node["span"],
                                "statements": [*else_stmts, leave_scope, *rest_statements],
                            },
                        }
                    elif not then_returns and else_returns:
                        cur_stmt = {
                            **statement,
                            "then": {
                                "kind": "block",
                                "span": node["span"],
                                "statements": [*then_stmts, leave_scope, *rest_statements],
                            },
                        }
                    else:
                        raise self.fail("unsupported", "a returning terminal must be the final statement")
                elif kind == "match" and index < len(statements) - 1:
                    lifted = lift_stmt_propagate(statement, "value", index)
                    if lifted is not None:
                        return lifted
                    rest_statements = statements[index + 1:]
                    leave_scope = {"kind": "guard_scope", "span": statement["span"], "locals": tuple(extended)}
                    new_cases: list[Node] = []
                    for arm in self.nodes(statement["cases"]):
                        arm_stmts = self.nodes(arm["statements"])
                        if len(arm_stmts) == 1 and arm_stmts[0]["kind"] == "block":
                            arm_stmts = self.nodes(arm_stmts[0]["statements"])
                        if arm_stmts and arm_stmts[-1]["kind"] == "return":
                            new_cases.append(arm)
                        else:
                            new_cases.append({**arm, "statements": [*arm_stmts, leave_scope, *rest_statements]})
                    cur_stmt = {**statement, "cases": new_cases}
                elif index != len(statements) - 1:
                    raise self.fail("unsupported", "a returning terminal must be the final statement")
                else:
                    cur_stmt = statement
                if kind == "return":
                    if self.active_lift_scopes > 0:
                        raise self.fail(
                            "type",
                            "cannot return from a callable while a record invariant is lifted in an enclosing scope",
                            cur_stmt,
                        )
                    if cur_stmt["value"] is None:
                        if self.uninitialized_out_params:
                            uninit_list = ", ".join(sorted(self.uninitialized_out_params))
                            raise self.fail(
                                "type",
                                f"cannot return before 'out' parameter '{uninit_list}' is initialized",
                                cur_stmt,
                            )
                        value = _Binding(_term("unit"), _UNIT)
                        if expected is not None:
                            self.unify(value.type, expected)
                        self.final_ref_bindings = dict(extended)
                        self.final_return_facts = list(self.active_facts[saved_active_len:])
                        return finish(value)
                    lifted = lift_stmt_propagate(cur_stmt, "value", index)
                    if lifted is not None:
                        return lifted
                    value_node = self.node(cur_stmt["value"])
                    result = (
                        self.expression(value_node, extended)
                        if expected is None
                        else _Binding(self.check(value_node, expected, extended), expected)
                    )
                    self._consume_call_updates(extended, cur_stmt)
                    if self._term_hr_region(result.term, extended) is not None:
                        raise self.fail(
                            "type",
                            "cannot return value borrowing higher-ranked callback region outside its invocation",
                            cur_stmt,
                        )
                    if self._term_contains_restored_view(result.term):
                        raise self.fail(
                            "type",
                            "cannot return a view borrowed from a span that was already restored",
                            cur_stmt,
                        )
                    self._check_span_view_use(result.term, extended, cur_stmt, use="return")
                    self._check_return_region(value_node, extended, cur_stmt)
                    if self.uninitialized_out_params:
                        uninit_list = ", ".join(sorted(self.uninitialized_out_params))
                        raise self.fail(
                            "type",
                            f"cannot return before 'out' parameter '{uninit_list}' is initialized"
                            + self._fallible_out_hint(result.type),
                            cur_stmt,
                        )
                    self.final_ref_bindings = dict(extended)
                    self.final_return_facts = list(self.active_facts[saved_active_len:])
                    return finish(result)
                if kind == "if":
                    cond_raw = self.node(cur_stmt["condition"])
                    combined_facts = (*active_facts, *statement_facts)
                    if operands := self._pattern_conjuncts(cond_raw):
                        if cur_stmt["else"] is None and expected is not None and self.whnf(expected) == _UNIT:
                            cur_stmt = {**cur_stmt, "else": {"kind": "return", "span": cur_stmt["span"], "value": None}}
                        if cur_stmt["else"] is not None:
                            return finish(self._guard_return(cur_stmt, operands, extended, expected, combined_facts))
                    if cur_stmt["else"] is None:
                        raise self.fail("type", "every conditional branch must return")
                    lifted = lift_stmt_propagate(cur_stmt, "condition", index)
                    if lifted is not None:
                        return lifted
                    cond_unwrapped = self._unwrap_group(cond_raw)
                    if cond_unwrapped["kind"] == "is":
                        return finish(
                            self._if_is(
                                cond_unwrapped,
                                self.node(cur_stmt["then"]),
                                self.node(cur_stmt["else"]),
                                extended,
                                expected,
                                expression_branches=False,
                                facts=combined_facts,
                                site_node=cur_stmt,
                            )
                        )
                    condition = self.check(cond_raw, _BOOL, extended)
                    self._consume_call_updates(extended, cond_raw)
                    lint_branch(self, cond_raw, condition, extended)
                    saved_uninit = set(self.uninitialized_out_params)
                    saved_indexed = dict(self.indexed_local_borrows)
                    saved_peer_len = len(self.indexed_borrow_peers)
                    yes_guard = self._branch_guard(condition, True)
                    no_guard = self._branch_guard(condition, False)
                    self.active_facts.append(condition)
                    try:
                        yes = self.branch(
                            self.node(cur_stmt["then"]), extended, expected, facts=(*combined_facts, *yes_guard),
                        )
                        yes_refs = dict(self.final_ref_bindings)
                        yes_uninit = set(self.uninitialized_out_params)
                    finally:
                        self.active_facts.pop()
                    self.uninitialized_out_params = set(saved_uninit)
                    self.indexed_local_borrows = dict(saved_indexed)
                    del self.indexed_borrow_peers[saved_peer_len:]
                    self.active_facts.append(_app(_constant("!"), condition))
                    try:
                        no = self.branch(
                            self.node(cur_stmt["else"]), extended, yes.type, facts=(*combined_facts, *no_guard),
                        )
                        no_refs = dict(self.final_ref_bindings)
                        no_uninit = set(self.uninitialized_out_params)
                    finally:
                        self.active_facts.pop()
                    self.indexed_local_borrows = dict(saved_indexed)
                    del self.indexed_borrow_peers[saved_peer_len:]
                    self.uninitialized_out_params = yes_uninit | no_uninit
                    merged_refs = dict(extended)
                    for rk in set(yes_refs) & set(no_refs):
                        yb = yes_refs[rk]
                        nb = no_refs[rk]
                        if yb.term != nb.term:
                            merged_refs[rk] = _Binding(
                                self.whnf(self._branch_value(yb.type, condition, yb.term, nb.term, yes_guard, no_guard)),
                                yb.type,
                            )
                        else:
                            merged_refs[rk] = yb
                    self.final_ref_bindings = merged_refs
                    return finish(_Binding(
                        self._branch_value(yes.type, condition, yes.term, no.term, yes_guard, no_guard), yes.type,
                    ))
                if kind == "match":
                    lifted = lift_stmt_propagate(cur_stmt, "value", index)
                    if lifted is not None:
                        return lifted
                    return finish(
                        self.match(
                            cur_stmt,
                            extended,
                            expected,
                            expression_arms=False,
                            facts=(*active_facts, *statement_facts),
                        )
                    )
                if kind == "block":
                    return finish(
                        self.block(statement, extended, expected, facts=(*active_facts, *statement_facts))
                    )
                raise self.fail("unsupported", f"statement '{kind}' requires the full frontend")
            if (
                statements
                and statements[-1]["kind"]
                in {"assignment", "expression_statement", "open_invariant", "foreach", "foreach_collection", "while"}
                and expected is not None
                and self.whnf(expected) == _UNIT
            ):
                if self.uninitialized_out_params:
                    uninit_list = ", ".join(sorted(self.uninitialized_out_params))
                    raise self.fail(
                        "type",
                        f"cannot return before 'out' parameter '{uninit_list}' is initialized",
                        node,
                    )
                self.final_ref_bindings = dict(extended)
                return finish(_Binding(_term("unit"), _UNIT))
            raise self.fail("type", "a pure block requires an explicit terminal return", node)
        finally:
            del self.active_facts[saved_active_len:]

    def branch(self: _Elaborator, node: Node, environment: dict[str, _Binding], expected: _Term | None,
               *, facts: tuple[_Binding, ...] = ()) -> _Binding:
        if node["kind"] == "block":
            return self.block(node, environment, expected, facts=facts)
        return self.block(
            {"kind": "block", "span": node["span"], "statements": [node]},
            environment,
            expected,
            facts=facts,
        )

    def _if_is(
        self: _Elaborator,
        is_node: Node,
        then_node: Node,
        else_node: Node,
        environment: dict[str, _Binding],
        expected: _Term | None = None,
        *,
        expression_branches: bool = True,
        facts: tuple[_Binding, ...] = (),
        site_node: Node,
    ) -> _Binding:
        visited_arms: set[int] = set()
        if expression_branches:
            synthetic: Node = {
                "kind": "match_expression",
                "span": site_node["span"],
                "value": is_node["value"],
                "motive": None,
                "cases": [
                    {
                        "kind": "expression_case",
                        "span": then_node["span"],
                        "pattern": is_node["pattern"],
                        "value": then_node,
                    },
                    {
                        "kind": "expression_case",
                        "span": else_node["span"],
                        "pattern": {"kind": "wildcard_pattern", "span": else_node["span"]},
                        "value": else_node,
                    },
                ],
            }
            result = self.match(
                synthetic,
                environment,
                expected,
                expression_arms=True,
                facts=facts,
                refine_scrutinee=True,
                visited_arms=visited_arms,
                synthetic=True,
            )
            if 1 not in visited_arms:
                self.check(else_node, result.type, environment)
            return result
        then_stmts = self.nodes(then_node["statements"]) if then_node["kind"] == "block" else [then_node]
        else_stmts = self.nodes(else_node["statements"]) if else_node["kind"] == "block" else [else_node]
        synthetic = {
            "kind": "match",
            "span": site_node["span"],
            "value": is_node["value"],
            "motive": None,
            "cases": [
                {
                    "kind": "case",
                    "span": then_node["span"],
                    "pattern": is_node["pattern"],
                    "statements": then_stmts,
                },
                {
                    "kind": "case",
                    "span": else_node["span"],
                    "pattern": {"kind": "wildcard_pattern", "span": else_node["span"]},
                    "statements": else_stmts,
                },
            ],
        }
        result = self.match(
            synthetic,
            environment,
            expected,
            expression_arms=False,
            facts=facts,
            refine_scrutinee=True,
            visited_arms=visited_arms,
            synthetic=True,
        )
        if 1 not in visited_arms:
            self.branch(else_node, environment, result.type, facts=facts)
        return result

    def if_expression(
        self: _Elaborator, node: Node, environment: dict[str, _Binding], expected: _Term | None = None
    ) -> _Binding:
        self.site = node
        cond_raw = self.node(node["condition"])
        cond_unwrapped = self._unwrap_group(cond_raw)
        then_node = self.node(node["then"])
        else_node = self.node(node["else"])
        if operands := self._pattern_conjuncts(cond_raw):
            guarded = self._guard_conditional(node, operands, then_node, else_node, environment)
            return self._check_guard_value(guarded, environment, expected)
        if cond_unwrapped["kind"] == "is":
            return self._if_is(
                cond_unwrapped,
                then_node,
                else_node,
                environment,
                expected,
                expression_branches=True,
                site_node=node,
            )
        synthetic: Node = {
            "kind": "match_expression",
            "span": node["span"],
            "value": cond_raw,
            "motive": None,
            "cases": [
                {
                    "kind": "expression_case",
                    "span": then_node["span"],
                    "pattern": {"kind": "bool_pattern", "span": cond_raw["span"], "value": True},
                    "value": then_node,
                },
                {
                    "kind": "expression_case",
                    "span": else_node["span"],
                    "pattern": {"kind": "bool_pattern", "span": cond_raw["span"], "value": False},
                    "value": else_node,
                },
            ],
        }
        return self.match(
            synthetic,
            environment,
            expected,
            expression_arms=True,
            refine_scrutinee=True,
            expected_scrutinee_type=_BOOL,
            synthetic=True,
        )

    def _check_guard_value(
        self: _Elaborator, guarded: Node, environment: dict[str, _Binding], expected: _Term | None,
    ) -> _Binding:
        if self.last_call_updates:
            raise self.fail("unsupported", "evaluate the earlier mutable loan call in a separate statement", guarded)
        saved = self.guard_value
        self.guard_value = True
        try:
            if expected is not None:
                return _Binding(self.check(guarded, expected, environment), expected)
            return self.expression(guarded, environment)
        finally:
            self.guard_value = saved

    def _is_expression(self: _Elaborator, node: Node, environment: dict[str, _Binding]) -> _Binding:
        self.site = node
        pat_node = self.node(node["pattern"])
        synthetic: Node = {
            "kind": "match_expression",
            "span": node["span"],
            "value": node["value"],
            "motive": None,
            "cases": [
                {
                    "kind": "expression_case",
                    "span": pat_node["span"],
                    "pattern": pat_node,
                    "value": {"kind": "bool", "span": pat_node["span"], "value": True},
                },
                {
                    "kind": "expression_case",
                    "span": node["span"],
                    "pattern": {"kind": "wildcard_pattern", "span": pat_node["span"]},
                    "value": {"kind": "bool", "span": node["span"], "value": False},
                },
            ],
        }
        return self.match(synthetic, environment, _BOOL, expression_arms=True, synthetic=True)

    def _project_member(
        self: _Elaborator, receiver: _Binding, member_name: str, node: Node, environment: dict[str, _Binding],
    ) -> _Binding:
        self.site = node
        receiver_type = self.whnf(receiver.type)
        head, type_args = self.spine(receiver_type)
        if head == _constant("Span") and len(type_args) == 1 and self.whnf(type_args[0]) == _U8:
            if member_name == "Model":
                self._check_span_can_read(receiver.term, environment, node)
                self._check_span_view_use(receiver.term, environment, node, use="read")
                return _Binding(
                    _apps(_constant("Span_Model"), _U8, receiver.term),
                    _app(_constant("Seq"), _U8),
                )
            span_props: dict[str, tuple[str, _Term]] = {
                "Base": ("Span_Base", _USIZE),
                "Length": ("Span_Length", _USIZE),
                "Tag": ("Span_Tag", _BOOL),
                "PermRead": ("Span_PermRead", _BOOL),
                "PermWrite": ("Span_PermWrite", _BOOL),
                "CanRead": ("Span_CanRead", _BOOL),
                "CanWrite": ("Span_CanWrite", _BOOL),
            }
            if member_name not in span_props:
                raise self.fail("name", f"Span<byte> has no property '{member_name}'", node)
            const_name, prop_ty = span_props[member_name]
            return _Binding(_apps(_constant(const_name), _U8, receiver.term), prop_ty)
        if head == _constant("Vec") and len(type_args) == 2:
            if member_name == "Model":
                return _Binding(
                    _apps(_constant("Vec_Model"), type_args[0], type_args[1], receiver.term),
                    _app(_constant("Seq"), type_args[0]),
                )
            if member_name == "Count":
                return _Binding(type_args[1], _NAT)
            raise self.fail("name", f"Vec has no property '{member_name}'", node)
        if head == _constant("Seq") and len(type_args) == 1:
            if member_name == "Count":
                return _Binding(_apps(_constant("Seq_Count"), type_args[0], receiver.term), _NAT)
            if member_name == "Model":
                return receiver
            raise self.fail("name", f"Seq has no property '{member_name}'", node)
        if head == _constant("Slots") and len(type_args) == 2:
            elem_t, cap_t = type_args[0], type_args[1]
            if member_name == "Capacity":
                return _Binding(_apps(_constant("Slots_Capacity"), elem_t, cap_t, receiver.term), _USIZE)
            if member_name == "Model":
                return _Binding(
                    _apps(_constant("Slots_Model"), elem_t, cap_t, receiver.term),
                    _app(_constant("Seq"), elem_t),
                )
            slots_props: dict[str, tuple[str, _Term]] = {
                "Base": ("Slots_Base", _USIZE),
                "LiveCount": ("Slots_LiveCount", _USIZE),
                "Tag": ("Slots_Tag", _BOOL),
                "PermRead": ("Slots_PermRead", _BOOL),
                "PermWrite": ("Slots_PermWrite", _BOOL),
                "CanRead": ("Slots_CanRead", _BOOL),
                "CanWrite": ("Slots_CanWrite", _BOOL),
            }
            if member_name not in slots_props:
                raise self.fail("name", f"Slots has no property '{member_name}'", node)
            const_name, prop_ty = slots_props[member_name]
            return _Binding(_apps(_constant(const_name), elem_t, cap_t, receiver.term), prop_ty)
        if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.records_by_type:
            raise self.fail(
                "unsupported",
                "member projection requires a record receiver, a Format.Write call or the full frontend",
                node,
            )
        record_info = self.records_by_type[head.value]
        for idx, rf in enumerate(record_info.fields):
            if rf.name == member_name:
                ftype = self._instantiate_record_field_type(record_info, type_args, idx, receiver.term)
                fterm = _apps(_constant(rf.proj_const), *type_args, receiver.term)
                return _Binding(fterm, ftype)
        if member_name in record_info.properties:
            prop_info = record_info.properties[member_name]
            if prop_info.private_to is not None and prop_info.private_to != self.module_name:
                raise self.fail("name", f"cannot access private property '{member_name}' of module '{prop_info.private_to}'", node)
            ptype = self._instantiate_record_type(record_info, type_args, prop_info.type)
            ptype = self.substitute(ptype, cast("int", prop_info.self_var.value), receiver.term)
            pterm = _apps(_constant(prop_info.prop_const), *type_args, receiver.term)
            return _Binding(pterm, ptype)
        raise self.fail("name", f"record '{record_info.name}' has no field or property '{member_name}'", node)

    def with_expression(
        self: _Elaborator, node: Node, environment: dict[str, _Binding], expected: _Term | None = None
    ) -> _Binding:
        self.site = node
        base_node = self.node(node["value"])
        expected_head = self.spine(self.whnf(expected))[0] if expected is not None else None
        if (
            expected is not None
            and expected_head is not None
            and expected_head.kind == "const"
            and expected_head.value in self.records_by_type
        ):
            base_term = self.check(base_node, expected, environment)
            base = _Binding(base_term, expected)
        else:
            base = self.expression(base_node, environment)
        self._check_value_copy(base_node, base.type)
        base_type = self.whnf(base.type)
        head, type_args = self.spine(base_type)
        if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.records_by_type:
            raise self.fail("type", "record update 'with { ... }' requires a record value", base_node)
        record_info = self.records_by_type[head.value]
        field_index_by_name = {rf.name: idx for idx, rf in enumerate(record_info.fields)}
        updates = self.nodes(node["updates"])
        update_by_index: dict[int, Node] = {}
        last_index = -1
        last_name = ""
        for update_node in updates:
            self.node(update_node, "field_update")
            fname = self.name(update_node["name"])
            if fname not in field_index_by_name:
                raise self.fail("name", f"record '{record_info.name}' has no field '{fname}'", update_node)
            fidx = field_index_by_name[fname]
            if fidx in update_by_index:
                raise self.fail("name", f"duplicate field '{fname}' in record update", update_node)
            if fidx < last_index:
                raise self.fail(
                    "name",
                    f"record update fields must appear in declaration order; '{fname}' cannot follow '{last_name}'",
                    update_node,
                )
            update_by_index[fidx] = update_node
            last_index = fidx
            last_name = fname
        if not record_info.fields:
            raise self.fail("type", f"record '{record_info.name}' has no fields to update", node)
        final_fields: list[_Term] = []
        for idx, rf in enumerate(record_info.fields):
            ftype = self._instantiate_record_type(record_info, type_args, rf.type)
            for j in range(idx):
                ftype = self.substitute(ftype, cast("int", record_info.fields[j].var.value), final_fields[j])
            if idx in update_by_index:
                u_node = update_by_index[idx]
                final_fields.append(self.check(self.node(u_node["value"]), ftype, environment))
            else:
                old_ftype = self._instantiate_record_field_type(record_info, type_args, idx, base.term)
                if not self._try_unify(old_ftype, ftype):
                    raise self.fail(
                        "type",
                        f"record update changes an index that field '{rf.name}' depends on; update '{rf.name}' as well",
                        node,
                    )
                final_fields.append(_apps(_constant(rf.proj_const), *type_args, base.term))
        result_term = _apps(_constant(record_info.ctor_const), *type_args, *final_fields)
        result_type = _apps(_constant(record_info.type_const), *type_args)
        if expected is not None:
            self.unify(result_type, expected)
        base_unwrapped = self._unwrap_group(base_node)
        if (
            base_unwrapped["kind"] == "unary"
            and isinstance(base_unwrapped.get("operator"), dict)
            and cast("Node", base_unwrapped["operator"]).get("text") == "move"
        ):
            base_unwrapped = self._unwrap_group(self.node(base_unwrapped["value"]))
        base_name = self.name(base_unwrapped["name"]) if base_unwrapped["kind"] == "name" else None
        assign_target = self._in_lifted_target_assignment
        excluded = (
            self.lifted_invariants.get(base_name, set())
            if base_name is not None and base_name == assign_target
            else set()
        )
        self._check_record_invariants(
            record_info, type_args, result_term, environment, node, exclude_clauses=excluded
        )
        return _Binding(result_term, result_type)

    def _nat_or_usize_index(
        self: _Elaborator, idx_node: Node, environment: dict[str, _Binding], container_name: str
    ) -> _Term:
        if self._is_unsuffixed_int_expr(idx_node):
            return self.check(idx_node, _NAT, environment)
        idx_b = self.expression(idx_node, environment)
        idx_w = self.whnf(idx_b.type)
        if idx_w == _NAT:
            return idx_b.term
        if idx_w == _USIZE:
            return _app(_constant("int_to_nat_usize"), idx_b.term)
        raise self.fail("type", f"{container_name} index must have type Nat or usize", idx_node)
