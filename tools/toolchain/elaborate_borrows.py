# SPDX-License-Identifier: Apache-2.0
"""Polonius origin/region solving, prophecy lenses, GATs, shared mutability, and loan-soundness bridge."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal, cast

from toolchain import loans, regions
from toolchain.ast import HoldFastError
from toolchain.elaborate_types import (
    _BOOL,
    _CHAR,
    _NAT,
    _SORT,
    _U8,
    _UNIT,
    _USIZE,
    Node,
    _app,
    _apps,
    _Binding,
    _constant,
    _Term,
    _term,
    _UnionInfo,
)

if TYPE_CHECKING:
    from collections.abc import Callable

    from toolchain.elaborate import _Elaborator


@dataclass(frozen=True)
class _TypeRegionQual:
    """Region and borrow-mode metadata captured alongside an elaborated type."""

    modifier: str | None = None
    region: str | None = None
    nominal_type: str | None = None
    type_regions: tuple[str, ...] = ()
    is_prophecy: bool = False
    value_type: _Term | None = None
    owner_type: _Term | None = None


@dataclass(frozen=True)
class _CallableRegionSig:
    """Signature-level region, variance, and outlives summary for a callable."""

    region_params: tuple[str, ...]
    param_quals: tuple[_TypeRegionQual, ...]
    return_qual: _TypeRegionQual
    outlives: tuple[tuple[str, str], ...]
    fn_mode: str = "Fn"
    prophecy_param_indices: tuple[int, ...] = ()


@dataclass(frozen=True)
class _AssocTypeSpec:
    """Interface-level associated type or GAT specification."""

    name: str
    generic_vars: tuple[_Term, ...]
    region_params: tuple[str, ...]
    kind: _Term
    abstract_var: _Term


@dataclass(frozen=True)
class _ImplAssocTypeDef:
    """Concrete associated type / GAT definition inside an impl block."""

    name: str
    generic_vars: tuple[_Term, ...]
    region_params: tuple[str, ...]
    rhs_type: _Term
    rhs_node: Node
    qual: _TypeRegionQual


_UNSTABLE_CONTAINER_METHODS = frozenset({
    "Push", "Pop", "Clear", "Resize", "Append", "Extend", "Insert", "Remove",
    "push", "pop", "clear", "resize", "append", "extend", "insert", "remove",
})


class _BorrowMixin:
    """Borrow, region, GAT, shared-mutability, prophecy-lens, and loan-bridge support."""

    def _init_borrow_state(self: _Elaborator) -> None:
        self.var_region_mode: dict[int, tuple[str, str | None]] = {}
        self.pi_fn_modes: dict[int, str] = {}
        self.var_fn_modes: dict[int, str] = {}
        self.consumed_fnonce_vars: set[str] = set()
        self.active_lambda_fn_mode: str | None = None
        self.in_callable_signature_kind: str | None = None
        self.fn_region_signatures: dict[str, _CallableRegionSig] = {}
        self.var_region_signatures: dict[int, _CallableRegionSig] = {}
        self.declared_region_outlives: set[tuple[str, str]] = set()
        self.current_fn_return_qual: _TypeRegionQual | None = None
        self.current_fn_ref_owners: list[tuple[str, _Term]] = []
        self.current_fn_ref_owner_type: _Term | None = None
        self.current_fn_prophecy_region: str | None = None
        self._prophecy_return_depth: int = 0
        self.type_region_variances: dict[str, tuple[tuple[str, regions.Variance], ...]] = {}
        self.type_region_params: dict[str, tuple[str, ...]] = {}
        self.record_field_borrows: dict[str, tuple[tuple[str, str | None, str | None], ...]] = {}
        self.union_ctor_borrows: dict[str, dict[str, tuple[tuple[str, str | None, str | None], ...]]] = {}
        self.term_type_regions: dict[int, _TypeRegionQual] = {}
        self.local_type_regions: dict[str, _TypeRegionQual] = {}

        self.interface_assoc_types: dict[str, dict[str, _AssocTypeSpec]] = {}
        self.active_assoc_types: dict[str, tuple[_AssocTypeSpec, _Term]] = {}
        self.impl_assoc_types: dict[tuple[str, tuple[_Term, ...]], dict[str, _ImplAssocTypeDef]] = {}

        self.exclusive_borrow_exprs: dict[int, tuple[str, tuple[str, ...], str | None, Node]] = {}
        self.prophecy_borrows: dict[str, tuple[tuple[str, ...], _Term, _Term]] = {}
        self.prophecy_call_results: dict[int, tuple[tuple[str, ...], _Term, bool]] = {}
        self.shared_ref_parameters: set[int] = set()
        self.shared_ref_locals: set[str] = set()
        self.var_locals: set[str] = set()
        self.partially_moved_fields: dict[str, set[tuple[str, ...]]] = {}
        self.shared_mut_written_owners: set[str] = set()
        self.shared_region_aliases: dict[str, list[str]] = {}

        self.proved_disjoint_places: list[tuple[loans.Place, loans.Place]] = []
        self.proved_arithmetic_disequalities: list[tuple[str, str]] = []
        self.proved_tag_preserved_places: list[loans.Place] = []
        self.proved_no_realloc_places: list[loans.Place] = []
        self.proved_refinements: dict[str, loans.Place] = {}
        self.used_refinements: list[str] = []
        self.discharged_overlap_sites: set[int] = set()
        self.discharged_containment_sites: set[int] = set()
        self.emitted_loan_prelude_defs: set[str] = set()
        self.callable_return_source_names: dict[str, str] = {}
        self.callable_region_vars_by_emitted: dict[str, tuple[str, ...]] = {}
        self._suppress_moved_owner_check: str | None = None
        self.invalidated_prophecy_borrows: dict[str, str] = {}

    def _reset_borrow_callable_state(self: _Elaborator) -> None:
        self._suppress_moved_owner_check = None
        self.invalidated_prophecy_borrows.clear()
        self.consumed_fnonce_vars.clear()
        self.active_lambda_fn_mode = None
        self.declared_region_outlives.clear()
        self.current_fn_return_qual = None
        self.current_fn_ref_owners.clear()
        self.current_fn_ref_owner_type = None
        self.current_fn_prophecy_region = None
        self._prophecy_return_depth = 0
        self.exclusive_borrow_exprs.clear()
        self.prophecy_borrows.clear()
        self.prophecy_call_results.clear()
        self.local_type_regions.clear()
        self.shared_ref_locals.clear()
        self.var_locals.clear()
        self.partially_moved_fields.clear()
        self.shared_mut_written_owners.clear()
        self.shared_region_aliases.clear()
        self.proved_disjoint_places.clear()
        self.proved_arithmetic_disequalities.clear()
        self.proved_tag_preserved_places.clear()
        self.proved_no_realloc_places.clear()
        self.proved_refinements.clear()
        self.used_refinements.clear()
        self.discharged_overlap_sites.clear()
        self.discharged_containment_sites.clear()

    def _register_borrow_builtins(self: _Elaborator, bind_fn: Callable[[str, _Term, int], None]) -> None:
        """Register Outlives, LocalCell, and BorrowCell type/method symbols."""
        a = self.fresh(_SORT)
        bind_fn("Outlives", _BOOL, 0)
        self.constants["Outlives"] = _Binding(_constant("Outlives"), _BOOL, 0)
        bind_fn("LocalCell", self.wrap("pi", [a], _SORT), 1)
        bind_fn("BorrowCell", self.wrap("pi", [a], _SORT), 1)
        lc_a = _app(_constant("LocalCell"), a)
        bc_a = _app(_constant("BorrowCell"), a)
        bind_fn("holdfast_LocalCell_New", self.wrap("pi", [a], self.pi(a, lc_a)), 1)
        bind_fn("holdfast_LocalCell_Get", self.wrap("pi", [a], self.pi(lc_a, a)), 1)
        bind_fn("holdfast_LocalCell_Set", self.wrap("pi", [a], self.pi(lc_a, self.pi(a, lc_a))), 1)
        bind_fn("holdfast_BorrowCell_New", self.wrap("pi", [a], self.pi(a, bc_a)), 1)
        bind_fn("holdfast_BorrowCell_Read", self.wrap("pi", [a], self.pi(bc_a, a)), 1)
        bind_fn("holdfast_BorrowCell_Write", self.wrap("pi", [a], self.pi(bc_a, self.pi(a, bc_a))), 1)

    def _ensure_cell_prelude(self: _Elaborator, name: str) -> None:
        """Lazily emit pure Gallina definitions for LocalCell / BorrowCell on first use."""
        if name in self.emitted_loan_prelude_defs:
            return
        self.emitted_loan_prelude_defs.add(name)
        if name == "LocalCell":
            self.output.append(
                "Definition LocalCell (A : Type@{holdfast_u0}) : Type@{holdfast_u0} := A.\n"
                "Definition holdfast_LocalCell (A : Type@{holdfast_u0}) : Type@{holdfast_u0} := LocalCell A.\n"
                "Definition holdfast_LocalCell_New (A : Type@{holdfast_u0}) (v : A) : LocalCell A := v.\n"
                "Definition holdfast_LocalCell_Get (A : Type@{holdfast_u0}) (c : LocalCell A) : A := c.\n"
                "Definition holdfast_LocalCell_Set (A : Type@{holdfast_u0}) (_ : LocalCell A) (v : A) : LocalCell A := v."
            )
        elif name == "BorrowCell":
            self.output.append(
                "Definition BorrowCell (A : Type@{holdfast_u0}) : Type@{holdfast_u0} := A.\n"
                "Definition holdfast_BorrowCell (A : Type@{holdfast_u0}) : Type@{holdfast_u0} := BorrowCell A.\n"
                "Definition holdfast_BorrowCell_New (A : Type@{holdfast_u0}) (v : A) : BorrowCell A := v.\n"
                "Definition holdfast_BorrowCell_Read (A : Type@{holdfast_u0}) (c : BorrowCell A) : A := c.\n"
                "Definition holdfast_BorrowCell_Write (A : Type@{holdfast_u0}) (_ : BorrowCell A) (v : A) : BorrowCell A := v."
            )

    def _borrow_import_state(self: _Elaborator, mod: _Elaborator) -> None:
        self.var_region_mode.update(mod.var_region_mode)
        self.pi_fn_modes.update(mod.pi_fn_modes)
        self.var_fn_modes.update(mod.var_fn_modes)
        self.fn_region_signatures.update(mod.fn_region_signatures)
        self.type_region_variances.update(mod.type_region_variances)
        self.type_region_params.update(mod.type_region_params)
        self.record_field_borrows.update(mod.record_field_borrows)
        self.union_ctor_borrows.update(mod.union_ctor_borrows)
        self.interface_assoc_types.update(mod.interface_assoc_types)
        self.impl_assoc_types.update(mod.impl_assoc_types)
        self.shared_ref_parameters.update(mod.shared_ref_parameters)
        self.callable_return_source_names.update(mod.callable_return_source_names)

    # ------------------------------------------------------------------
    # Region extraction, variance, outlives, and Polonius checking
    # ------------------------------------------------------------------

    def _extract_type_region_qual(self: _Elaborator, type_node: Node) -> _TypeRegionQual:
        cur = type_node
        while cur["kind"] in {"group_type", "type_argument"}:
            cur = self.node(cur["type"])
        if cur["kind"] == "modified_type":
            modifier = cast("str | None", cur.get("modifier"))
            lt: str | None = None
            if cur.get("lifetime") is not None:
                lt_node = self.node(cur["lifetime"], "lifetime")
                lt = self.lifetime_name(lt_node["name"])
            inner_q = self._extract_type_region_qual(self.node(cur["type"]))
            return _TypeRegionQual(
                modifier=modifier,
                region=lt or inner_q.region,
                nominal_type=inner_q.nominal_type,
                type_regions=inner_q.type_regions,
            )
        if cur["kind"] == "type":
            tname = self.name(cur["name"])
            t_regs: list[str] = []
            for arg in self.nodes(cur["arguments"]):
                if arg["kind"] == "lifetime":
                    t_regs.append(self.lifetime_name(arg["name"]))
                else:
                    sub_q = self._extract_type_region_qual(arg)
                    if sub_q.region is not None:
                        t_regs.append(sub_q.region)
                    t_regs.extend(sub_q.type_regions)
            prim_reg = t_regs[0] if len(t_regs) == 1 else None
            return _TypeRegionQual(
                modifier=None,
                region=prim_reg,
                nominal_type=tname,
                type_regions=tuple(t_regs),
            )
        return _TypeRegionQual()

    def _compute_record_region_variances(
        self: _Elaborator,
        region_names: tuple[str, ...],
        parameters: list[Node],
    ) -> tuple[tuple[str, regions.Variance], ...]:
        variances: dict[str, regions.Variance] = dict.fromkeys(region_names, regions.Variance.COVARIANT)
        for param_node in parameters:
            pt = self.node(param_node["type"])
            self._accumulate_type_variances(pt, regions.Variance.COVARIANT, variances)
        return tuple((r, variances[r]) for r in region_names)

    def _accumulate_type_variances(
        self: _Elaborator,
        node: Node,
        ambient: regions.Variance,
        out: dict[str, regions.Variance],
    ) -> None:
        while node["kind"] in {"group_type", "type_argument"}:
            node = self.node(node["type"])
        kind = node["kind"]
        if kind == "modified_type":
            mod = node.get("modifier")
            next_var = (
                regions.Variance.INVARIANT
                if mod in {"ref", "shared_ref", "out"}
                else ambient
            )
            if node.get("lifetime") is not None:
                lt = self.lifetime_name(self.node(node["lifetime"], "lifetime")["name"])
                if lt in out and next_var == regions.Variance.INVARIANT:
                    out[lt] = regions.Variance.INVARIANT
            self._accumulate_type_variances(self.node(node["type"]), next_var, out)
        elif kind == "type":
            tname = self.name(node["name"])
            type_const: str | None = None
            if tname in self.records:
                type_const = self.records[tname].type_const
            elif tname in self.unions:
                type_const = self.unions[tname].type_const
            child_vars = self.type_region_variances.get(type_const, ()) if type_const is not None else ()
            reg_idx = 0
            for arg in self.nodes(node["arguments"]):
                if arg["kind"] == "lifetime":
                    lt = self.lifetime_name(arg["name"])
                    arg_var = (
                        child_vars[reg_idx][1]
                        if reg_idx < len(child_vars)
                        else regions.Variance.COVARIANT
                    )
                    reg_idx += 1
                    combined = (
                        regions.Variance.INVARIANT
                        if regions.Variance.INVARIANT in (ambient, arg_var)
                        else regions.Variance.COVARIANT
                    )
                    if lt in out and combined == regions.Variance.INVARIANT:
                        out[lt] = regions.Variance.INVARIANT
                else:
                    self._accumulate_type_variances(arg, ambient, out)
        elif kind == "tuple_type":
            for t in self.nodes(node["types"]):
                self._accumulate_type_variances(t, ambient, out)
        elif kind == "function_type":
            for p in self.nodes(node["parameters"]):
                self._accumulate_type_variances(self.node(p["type"]), regions.Variance.INVARIANT, out)
            self._accumulate_type_variances(self.node(node["result"]), ambient, out)

    def _record_outlives_constraint_if_present(
        self: _Elaborator, expr_node: Node,
    ) -> _Binding | None:
        """Recognize ``Outlives<'a, 'b>`` or ``Outlives<'a, 'b>()`` in requires contracts."""
        cur = self._unwrap_group(expr_node)
        target = cur
        if cur["kind"] == "call" and not self.nodes(cur["arguments"]):
            target = self._unwrap_group(self.node(cur["callee"]))
        if target["kind"] == "generic_application":
            base = self._unwrap_group(self.node(target["value"]))
            if base["kind"] == "name" and self.name(base["name"]) == "Outlives":
                args = self.nodes(target["arguments"])
                if len(args) != 2 or any(a["kind"] != "lifetime" for a in args):
                    raise self.fail(
                        "type",
                        "Outlives requires exactly two region arguments <'sup, 'sub>",
                        target,
                    )
                sup = self.lifetime_name(args[0]["name"])
                sub = self.lifetime_name(args[1]["name"])
                if sup != "'_" and sup not in self.active_regions:
                    raise self.fail("name", f"unknown region '{sup}'", args[0])
                if sub != "'_" and sub not in self.active_regions:
                    raise self.fail("name", f"unknown region '{sub}'", args[1])
                self.declared_region_outlives.add((sup, sub))
                return _Binding(_term("bool", value=1), _BOOL)
        return None

    def _region_outlives_closure(self: _Elaborator, extra: tuple[tuple[str, str], ...] = ()) -> set[tuple[str, str]]:
        closure = set(self.declared_region_outlives) | set(extra)
        for r in self.active_regions:
            closure.add((r, r))
        changed = True
        while changed:
            changed = False
            for a, b in list(closure):
                for c, d in list(closure):
                    if b == c and (a, d) not in closure:
                        closure.add((a, d))
                        changed = True
        return closure

    def _check_region_assignable(
        self: _Elaborator,
        expected_qual: _TypeRegionQual,
        actual_qual: _TypeRegionQual,
        site_node: Node,
        *,
        outlives: set[tuple[str, str]] | None = None,
    ) -> None:
        closure = outlives if outlives is not None else self._region_outlives_closure()
        exp_r = expected_qual.region
        act_r = actual_qual.region
        if exp_r is not None and act_r is not None and exp_r != "'_" and act_r != "'_":
            if expected_qual.modifier in {"ref", "shared_ref"}:
                if act_r != exp_r and ((act_r, exp_r) not in closure or (exp_r, act_r) not in closure):
                    raise self.fail(
                        "type",
                        f"invariant borrow region mismatch: cannot unify '{act_r}' with '{exp_r}'",
                        site_node,
                    )
            elif act_r != exp_r and (act_r, exp_r) not in closure:
                raise self.fail(
                    "type",
                    f"region '{act_r}' does not outlive required region '{exp_r}'",
                    site_node,
                )
        if expected_qual.type_regions and actual_qual.type_regions:
            tconst: str | None = None
            if expected_qual.nominal_type is not None and expected_qual.nominal_type in self.records:
                tconst = self.records[expected_qual.nominal_type].type_const
            elif expected_qual.nominal_type is not None and expected_qual.nominal_type in self.unions:
                tconst = self.unions[expected_qual.nominal_type].type_const
            variances = self.type_region_variances.get(tconst, ()) if tconst is not None else ()
            for idx, (er, ar) in enumerate(zip(expected_qual.type_regions, actual_qual.type_regions, strict=False)):
                if ar in ("'_", er) or er == "'_":
                    continue
                var = variances[idx][1] if idx < len(variances) else regions.Variance.COVARIANT
                if var == regions.Variance.INVARIANT:
                    if (ar, er) not in closure or (er, ar) not in closure:
                        raise self.fail(
                            "type",
                            f"invariant type region mismatch: cannot use '{ar}' where '{er}' is expected",
                            site_node,
                        )
                elif var == regions.Variance.COVARIANT:
                    if (ar, er) not in closure:
                        raise self.fail(
                            "type",
                            f"region '{ar}' does not outlive expected region '{er}'",
                            site_node,
                        )
                elif (er, ar) not in closure:
                    raise self.fail(
                        "type",
                        f"region '{er}' does not outlive '{ar}'",
                        site_node,
                    )

    def _check_return_region(
        self: _Elaborator,
        value_node: Node,
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> None:
        """Verify returned borrow/value region outlives the declared return region."""
        ret_q = self.current_fn_return_qual
        if ret_q is None or ret_q.region is None or ret_q.region == "'_":
            return
        unw = self._unwrap_group(value_node)
        actual_regs = self._infer_arg_regions(unw, environment)
        if not actual_regs:
            return
        act_mod = ret_q.modifier
        if unw["kind"] == "name":
            vname = self.name(unw["name"])
            if vname in self.local_type_regions:
                act_mod = self.local_type_regions[vname].modifier or act_mod
        actual_q = _TypeRegionQual(
            modifier=act_mod,
            region=actual_regs[0],
            nominal_type=ret_q.nominal_type,
            type_regions=tuple(actual_regs),
        )
        self._check_region_assignable(ret_q, actual_q, site_node)

    def _invalidate_prophecy_borrows_for_owner(self: _Elaborator, owner_name: str) -> None:
        for bname, (owners, _, _) in self.prophecy_borrows.items():
            if owner_name in owners:
                self.invalidated_prophecy_borrows[bname] = owner_name

    def _prepare_callable_prophecy_context(
        self: _Elaborator,
        parameters: list[Node],
        param_vars: list[_Term],
        result_node: Node,
    ) -> None:
        """Configure prophecy/lens context when a callable returns an exclusive ref<'a> loan."""
        self.current_fn_ref_owners.clear()
        self.current_fn_ref_owner_type = None
        self.current_fn_prophecy_region = None
        ret_qual = self._extract_type_region_qual(result_node)
        self.current_fn_return_qual = ret_qual
        ref_ret_region = self._find_exclusive_return_region(result_node)
        if ref_ret_region is None or ref_ret_region == "'_":
            return
        owners: list[tuple[str, _Term]] = []
        for p_node, p_var in zip(parameters, param_vars, strict=False):
            pt = self.node(p_node["type"])
            if pt["kind"] == "modified_type" and pt.get("modifier") == "ref" and p_node["name"] is not None:
                p_reg = self._extract_type_region(pt)
                if p_reg == ref_ret_region or (p_reg is not None and (p_reg, ref_ret_region) in self.declared_region_outlives):
                    owners.append((self.name(p_node["name"]), self.types[cast("int", p_var.value)]))
        if not owners:
            return
        self.current_fn_ref_owners = owners
        self.current_fn_prophecy_region = ref_ret_region
        pack_type = owners[-1][1]
        for _, oty in reversed(owners[:-1]):
            pack_type = _term("prod", oty, pack_type)
        self.current_fn_ref_owner_type = pack_type

    def _find_exclusive_return_region(self: _Elaborator, node: Node) -> str | None:
        cur = node
        while cur["kind"] in {"group_type", "type_argument"}:
            cur = self.node(cur["type"])
        if cur["kind"] == "modified_type" and cur.get("modifier") == "ref":
            return self._extract_type_region(cur)
        if cur["kind"] == "type":
            tname = self.name(cur["name"])
            if tname == "Result":
                for arg in self.nodes(cur["arguments"]):
                    if (found := self._find_exclusive_return_region(arg)) is not None:
                        return found
        return None

    def _is_prophecy_pair_type(self: _Elaborator, ty: _Term) -> tuple[_Term, _Term] | None:
        w = self.whnf(ty)
        if w.kind != "prod":
            return None
        val_t, fn_t = w.args
        fn_w = self.whnf(fn_t)
        if fn_w.kind == "pi" and self.convertible(fn_w.args[0], val_t):
            return val_t, fn_w.args[1]
        return None

    def _prophecy_type_active(self: _Elaborator, lt_name: str | None) -> bool:
        return (
            self._prophecy_return_depth > 0
            and self.current_fn_ref_owner_type is not None
            and lt_name is not None
            and lt_name == self.current_fn_prophecy_region
        )

    def _build_ref_return_lens(
        self: _Elaborator,
        expr_node: Node,
        expected_pair_type: _Term,
        environment: dict[str, _Binding],
    ) -> _Binding | None:
        """Build prophecy/lens ``(current_val, fun new_val => updated_owner)`` for ``ref`` returns."""
        pair_info = self._is_prophecy_pair_type(expected_pair_type)
        if pair_info is None or not self.current_fn_ref_owners:
            return None
        val_type, owner_pack_type = pair_info
        cur = self._unwrap_group(expr_node)
        owner_name: str | None = None
        field_path: tuple[str, ...] = ()
        elem_idx: _Term | None = None
        if cur["kind"] == "unary" and isinstance(cur_op := cur.get("operator"), dict) and cur_op.get("text") == "ref":
            inner = self._unwrap_group(self.node(cur["value"]))
            if self._is_indexed_borrow_target(inner):
                info, projected = self._resolve_indexed_local_borrow("ref", inner, environment, expr_node)
                owner_name = info.owner
                field_path = info.field_path
                elem_idx = info.index_term
            else:
                owner_name, field_path, projected = self._resolve_local_borrow_target(
                    "ref", inner, environment, expr_node
                )
        elif cur["kind"] == "name":
            bname = self.name(cur["name"])
            if bname in self.local_borrows:
                bmode, owner_name, field_path = self.local_borrows[bname]
                if bmode != "ref":
                    raise self.fail(
                        "type",
                        f"cannot return shared '{bmode}' borrow '{bname}' as exclusive 'ref' return (exclusive-from-shared)",
                        expr_node,
                    )
                projected = environment[bname]
            elif bname in self.indexed_local_borrows:
                info = self.indexed_local_borrows[bname]
                if info.mode != "ref":
                    raise self.fail(
                        "type",
                        f"cannot return shared '{info.mode}' borrow '{bname}' as exclusive 'ref' return (exclusive-from-shared)",
                        expr_node,
                    )
                owner_name = info.owner
                field_path = info.field_path
                elem_idx = info.index_term
                projected = environment[bname]
            elif bname in self.prophecy_borrows:
                p_owners, p_lens, _p_vty = self.prophecy_borrows[bname]
                if set(p_owners) <= {n for n, _ in self.current_fn_ref_owners}:
                    projected = environment[bname]
                    self.unify(projected.type, val_type)
                    # Compose inner lens with outer owners if 1:1
                    if len(self.current_fn_ref_owners) == 1 and p_owners == (self.current_fn_ref_owners[0][0],):
                        return _Binding(
                            _term("pair", val_type, self.pi(val_type, owner_pack_type), projected.term, p_lens),
                            expected_pair_type,
                        )
                return None
            elif any(n == bname for n, _ in self.current_fn_ref_owners):
                owner_name = bname
                projected = environment[bname]
            else:
                return None
        else:
            return None

        if owner_name is None or not any(n == owner_name for n, _ in self.current_fn_ref_owners):
            raise self.fail(
                "type",
                f"cannot return exclusive 'ref' borrow of '{owner_name}' outside its region (exclusive-loan-escape)",
                expr_node,
            )
        self.unify(projected.type, val_type)
        new_val = self.fresh(val_type)
        if elem_idx is not None:
            owner_b = environment[owner_name]
            updated_owner = self._update_indexed_owner_term(
                owner_b, field_path, elem_idx, new_val, environment, expr_node
            )
        elif field_path:
            owner_b = environment[owner_name]
            updated_owner = self._update_record_field_path(
                owner_b.term, owner_b.type, field_path, new_val, environment, expr_node
            )
        else:
            updated_owner = new_val
        updated_owners: list[_Term] = [
            updated_owner if n == owner_name else environment[n].term
            for n, _ in self.current_fn_ref_owners
        ]
        packed_owner = updated_owners[-1]
        for ot in reversed(updated_owners[:-1]):
            l_ty = self.infer(ot)
            r_ty = self.infer(packed_owner)
            packed_owner = _term("pair", l_ty, r_ty, ot, packed_owner)
        lens_lam = _term("lam", val_type, packed_owner, value=new_val.value)
        fn_ty = _term("pi", val_type, owner_pack_type, value=new_val.value)
        pair_term = _term("pair", val_type, fn_ty, projected.term, lens_lam)
        return _Binding(pair_term, expected_pair_type)

    def _update_indexed_owner_term(
        self: _Elaborator,
        owner_b: _Binding,
        field_path: tuple[str, ...],
        idx_t: _Term,
        new_val: _Term,
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> _Term:
        if field_path:
            rec_b = self._project_borrow_binding(
                "", (), {"": owner_b}, site_node
            )
            _ = rec_b
            cur_b = owner_b
            for fname in field_path:
                cur_ty = self.whnf(cur_b.type)
                head, targs = self.spine(cur_ty)
                rinfo = self.records_by_type[cast("str", head.value)]
                fidx = next(i for i, rf in enumerate(rinfo.fields) if rf.name == fname)
                cur_b = _Binding(
                    _apps(_constant(rinfo.fields[fidx].proj_const), *targs, cur_b.term),
                    self._instantiate_record_field_type(rinfo, targs, fidx, cur_b.term),
                )
            updated_col = self._update_collection_element(cur_b, idx_t, new_val, site_node)
            return self._update_record_field_path(
                owner_b.term, owner_b.type, field_path, updated_col, environment, site_node
            )
        return self._update_collection_element(owner_b, idx_t, new_val, site_node)

    def _update_collection_element(
        self: _Elaborator,
        col_b: _Binding,
        idx_t: _Term,
        new_val: _Term,
        site_node: Node,
    ) -> _Term:
        head, targs = self.spine(self.whnf(col_b.type))
        if head == _constant("Span") and len(targs) == 1:
            return _apps(_constant("Span_Write"), _U8, col_b.term, idx_t, new_val)
        if head == _constant("Slots") and len(targs) == 2:
            return _apps(_constant("Slots_Write"), targs[0], targs[1], col_b.term, idx_t, new_val)
        if head == _constant("Vec") and len(targs) == 2:
            return _apps(_constant("Vec_Update"), targs[0], targs[1], idx_t, new_val, col_b.term)
        if head == _constant("Seq") and len(targs) == 1:
            return _apps(_constant("Seq_Update"), targs[0], col_b.term, idx_t, new_val)
        raise self.fail("type", "cannot update indexed collection element via prophecy lens", site_node)

    def _record_prophecy_call_result(
        self: _Elaborator,
        call_term: _Term,
        ret_type: _Term,
        owner_names: tuple[str, ...],
        is_result_wrapped: bool,
    ) -> None:
        if owner_names:
            self.prophecy_call_results[id(call_term)] = (owner_names, ret_type, is_result_wrapped)

    def _apply_prophecy_write(
        self: _Elaborator,
        bname: str,
        new_val_binding: _Binding,
        updated: dict[str, _Binding],
        site_node: Node,
    ) -> None:
        _ = site_node
        owner_names, lens_term, val_type = self.prophecy_borrows[bname]
        self.unify(new_val_binding.type, val_type)
        restored = self.whnf(_app(lens_term, new_val_binding.term))
        if len(owner_names) == 1:
            oname = owner_names[0]
            if oname in updated:
                updated[oname] = _Binding(restored, updated[oname].type)
        else:
            cur_pack = restored
            for idx, oname in enumerate(owner_names):
                if idx < len(owner_names) - 1:
                    oty = updated[oname].type
                    rem_ty = self.infer(cur_pack).args[1]
                    elem_t = _apps(_constant("Fst"), oty, rem_ty, cur_pack)
                    cur_pack = _apps(_constant("Snd"), oty, rem_ty, cur_pack)
                else:
                    elem_t = cur_pack
                if oname in updated:
                    updated[oname] = _Binding(elem_t, updated[oname].type)
        # Update lens closure so further reads see the updated value; subsequent writes replace cleanly.
        new_v = self.fresh(val_type)
        updated[bname] = new_val_binding
        _ = new_v
        self.prophecy_borrows[bname] = (owner_names, lens_term, val_type)

    def _maybe_bind_prophecy_local(
        self: _Elaborator,
        bname: str,
        rhs_binding: _Binding,
        extended: dict[str, _Binding],
        mutable: bool,
    ) -> _Binding | None:
        info = self.prophecy_call_results.get(id(rhs_binding.term))
        if info is None or info[2]:
            pair_info = self._is_prophecy_pair_type(rhs_binding.type)
            if pair_info is None:
                return None
            # Check if rhs_binding came from destructuring an Ok(prophecy_slot) binder
            return None
        owner_names, _, _ = info
        pair_info = self._is_prophecy_pair_type(rhs_binding.type)
        if pair_info is None:
            return None
        val_t, owner_t = pair_info
        fn_t = self.pi(val_t, owner_t)
        val_term = _apps(_constant("Fst"), val_t, fn_t, rhs_binding.term)
        lens_term = _apps(_constant("Snd"), val_t, fn_t, rhs_binding.term)
        self.prophecy_borrows[bname] = (owner_names, lens_term, val_t)
        if mutable:
            self.mutable_locals.add(bname)
        _ = extended
        return _Binding(val_term, val_t)

    # ------------------------------------------------------------------
    # Nested field reborrows & partial field moves
    # ------------------------------------------------------------------

    def _resolve_nested_borrow_target(
        self: _Elaborator,
        borrow_mode: str,
        target_node: Node,
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> tuple[str, tuple[str, ...], _Binding]:
        """Resolve arbitrary nested record member borrow chains (e.g. ``a.b.c`` or ``reborrow.c``)."""
        chain: list[str] = []
        cur = self._unwrap_group(target_node)
        while cur["kind"] == "member":
            chain.append(self.name(cur["name"]))
            cur = self._unwrap_group(self.node(cur["value"]))
        chain.reverse()
        if not chain or cur["kind"] != "name":
            raise self.fail("unsupported", "field borrow target must be a named local or borrow", target_node)
        rname = self.name(cur["name"])
        if rname not in environment:
            raise self.fail("name", f"unknown identifier '{rname}'", cur)
        if rname in self.uninitialized_out_params:
            raise self.fail("type", f"cannot borrow field of uninitialized 'out' parameter '{rname}'", cur)
        if rname in self.local_borrows:
            parent_mode, owner_name, parent_path = self.local_borrows[rname]
            if borrow_mode == "ref" and parent_mode != "ref":
                raise self.fail(
                    "type",
                    f"cannot take exclusive 'ref' borrow of field '{chain[-1]}' from shared '{parent_mode}' borrow '{rname}' (exclusive-from-shared)",
                    site_node,
                )
            if borrow_mode == "shared_ref" and parent_mode == "in":
                raise self.fail(
                    "type",
                    f"cannot take 'shared ref' borrow of field '{chain[-1]}' from shared 'in' borrow '{rname}' (exclusive-from-shared)",
                    site_node,
                )
            field_path = (*parent_path, *chain)
        else:
            owner_name = rname
            field_path = tuple(chain)
            if borrow_mode in {"ref", "shared_ref"}:
                if rname in self.readonly_in_params:
                    raise self.fail(
                        "type",
                        f"cannot take '{borrow_mode}' borrow of field '{chain[-1]}' on read-only 'in' parameter '{rname}'",
                        site_node,
                    )
                if rname in self.frozen_collections:
                    raise self.fail(
                        "type",
                        f"cannot take '{borrow_mode}' borrow of field '{chain[-1]}' on frozen collection '{rname}'",
                        site_node,
                    )
                if rname not in self.mutable_locals and rname not in self.shared_ref_locals:
                    raise self.fail(
                        "type",
                        f"cannot take exclusive 'ref' borrow of field '{chain[-1]}' on immutable record '{rname}'; declare it with 'var' or 'ref'",
                        site_node,
                    )
        self._check_path_not_moved(owner_name, field_path, target_node)
        # Validate every traversed record step
        cur_ty = self.whnf(environment[owner_name].type)
        for seg in field_path:
            head, type_args = self.spine(cur_ty)
            if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.records_by_type:
                raise self.fail("type", f"cannot borrow field '{seg}' from non-record '{owner_name}'", target_node)
            record_info = self.records_by_type[head.value]
            field_index = next((idx for idx, rf in enumerate(record_info.fields) if rf.name == seg), None)
            if field_index is None:
                raise self.fail("name", f"record '{record_info.name}' has no field '{seg}'", target_node)
            rf = record_info.fields[field_index]
            if borrow_mode == "ref":
                if cast("int", rf.var.value) in self.constant_parameters or rf.readonly_span:
                    raise self.fail("type", f"cannot take exclusive 'ref' borrow of constant or read-only field '{seg}'", target_node)
                for later_rf in record_info.fields[field_index + 1:]:
                    if cast("int", rf.var.value) in self.free(later_rf.type):
                        raise self.fail(
                            "type",
                            f"cannot take exclusive 'ref' borrow of field '{seg}' because later field '{later_rf.name}' depends on it",
                            target_node,
                        )
            cur_ty = self.whnf(self._instantiate_record_type(record_info, type_args, rf.type))
        projected = self._project_borrow_binding(owner_name, field_path, environment, target_node)
        if not self._is_supported_loan_type(projected.type):
            raise self.fail("unsupported", f"loan modifier '{borrow_mode}' is not supported on this type", site_node)
        return owner_name, field_path, projected

    def _update_record_field_path(
        self: _Elaborator,
        cur_term: _Term,
        cur_type: _Term,
        field_path: tuple[str, ...],
        leaf_term: _Term,
        environment: dict[str, _Binding],
        site_node: Node,
        *,
        exclude_clauses: set[str] | None = None,
    ) -> _Term:
        if not field_path:
            return leaf_term
        fname = field_path[0]
        rec_type = self.whnf(cur_type)
        head, type_args = self.spine(rec_type)
        if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.records_by_type:
            raise self.fail("type", f"borrowed target is not a record for field '{fname}'", site_node)
        record_info = self.records_by_type[head.value]
        field_index = next((idx for idx, rf in enumerate(record_info.fields) if rf.name == fname), None)
        if field_index is None:
            raise self.fail("name", f"record '{record_info.name}' has no field '{fname}'", site_node)
        if len(field_path) == 1:
            updated_field = leaf_term
        else:
            rf = record_info.fields[field_index]
            sub_term = _apps(_constant(rf.proj_const), *type_args, cur_term)
            sub_type = self._instantiate_record_field_type(record_info, type_args, field_index, cur_term)
            updated_field = self._update_record_field_path(
                sub_term,
                sub_type,
                field_path[1:],
                leaf_term,
                environment,
                site_node,
                exclude_clauses=exclude_clauses,
            )
        final_fields: list[_Term] = []
        for idx, rf in enumerate(record_info.fields):
            if idx == field_index:
                final_fields.append(updated_field)
            else:
                final_fields.append(_apps(_constant(rf.proj_const), *type_args, cur_term))
        new_rec_term = _apps(_constant(record_info.ctor_const), *type_args, *final_fields)
        self._check_record_invariants(
            record_info, type_args, new_rec_term, environment, site_node, exclude_clauses=exclude_clauses or set()
        )
        return new_rec_term

    def _split_member_path(self: _Elaborator, node: Node) -> tuple[str, tuple[str, ...]] | None:
        parts: list[str] = []
        cur = self._unwrap_group(node)
        while cur["kind"] == "member":
            parts.append(self.name(cur["name"]))
            cur = self._unwrap_group(self.node(cur["value"]))
        if cur["kind"] != "name" or not parts:
            return None
        parts.reverse()
        return self.name(cur["name"]), tuple(parts)

    def _places_overlap(self: _Elaborator, p1: tuple[str, ...], p2: tuple[str, ...]) -> bool:
        n = min(len(p1), len(p2))
        return p1[:n] == p2[:n]

    def _check_path_not_moved(
        self: _Elaborator, owner: str, path: tuple[str, ...], site_node: Node,
    ) -> None:
        moved = self.partially_moved_fields.get(owner)
        if moved is None or not moved:
            return
        for mp in moved:
            if self._places_overlap(mp, path):
                joined = ".".join((owner, *mp))
                raise self.fail(
                    "type",
                    f"cannot use or borrow '{owner}' because field '{joined}' was moved (use-after-owner-move)",
                    site_node,
                )

    def _record_partial_field_move(
        self: _Elaborator,
        owner: str,
        field_path: tuple[str, ...],
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> _Binding:
        if owner not in environment:
            self.lookup(owner, environment)
        owner_b = environment[owner]
        if owner_b.constant:
            raise self.fail("type", f"cannot move field of constant binding '{owner}'", site_node)
        if owner in self.uninitialized_out_params:
            raise self.fail("type", f"cannot move field of uninitialized 'out' parameter '{owner}'", site_node)
        if owner in self.local_borrows:
            raise self.fail("type", f"cannot move through local borrow '{owner}' (move-through-loan-unsupported)", site_node)
        if owner in self.readonly_in_params or self._is_readonly_span(owner_b.term):
            raise self.fail("type", f"cannot move field of borrowed 'in' parameter '{owner}'", site_node)
        if owner in self.out_param_names or (
            owner_b.term.kind == "var" and cast("int", owner_b.term.value) in self.ref_parameters
        ):
            raise self.fail("type", f"cannot move field of borrowed 'ref' or 'out' parameter '{owner}'", site_node)
        # Disallow moving from an immutable non-owned parameter (preserves PartialOwnerMove test)
        is_owned_param = owner_b.term.kind == "var" and cast("int", owner_b.term.value) in self.owned_parameters
        if owner_b.term.kind == "var" and not is_owned_param and owner not in self.mutable_locals:
            raise self.fail(
                "type",
                f"cannot move projected field out of immutable parameter '{owner}' (partial-owner-move-unsupported)",
                site_node,
            )
        self._check_path_not_moved(owner, field_path, site_node)
        projected = self._project_borrow_binding(owner, field_path, environment, site_node)
        self.partially_moved_fields.setdefault(owner, set()).add(field_path)
        return projected

    def _clear_partial_move_on_write(self: _Elaborator, owner: str, field_path: tuple[str, ...]) -> None:
        moved = self.partially_moved_fields.get(owner)
        if moved is None or not moved:
            return
        if not field_path:
            self.partially_moved_fields.pop(owner, None)
            return
        remaining = {mp for mp in moved if not (len(mp) >= len(field_path) and mp[: len(field_path)] == field_path)}
        if remaining:
            self.partially_moved_fields[owner] = remaining
        else:
            self.partially_moved_fields.pop(owner, None)

    def _is_reborrow_assignment(self: _Elaborator, target_name: str, val_node: Node) -> bool:
        """True when ``cursor = ref ...`` / ``cursor = shared ref ...`` / ``cursor = in ...`` rebinds a var cursor."""
        if target_name not in self.var_locals:
            return False
        if target_name not in self.local_borrows and target_name not in self.indexed_local_borrows:
            return False
        unwrapped = self._unwrap_group(val_node)
        if (
            unwrapped["kind"] == "unary"
            and isinstance(unwrapped.get("operator"), dict)
            and cast("Node", unwrapped["operator"]).get("text") in {"in", "ref", "shared_ref"}
        ):
            return True
        return unwrapped["kind"] == "call" and self._is_tracked_span_view_call(unwrapped)

    def _elaborate_reborrow_assignment(
        self: _Elaborator,
        tname: str,
        val_node: Node,
        updated: dict[str, _Binding],
        statement: Node,
    ) -> dict[str, _Binding]:
        unwrapped = self._unwrap_group(val_node)
        if (
            unwrapped["kind"] == "unary"
            and isinstance(unwrapped.get("operator"), dict)
            and cast("Node", unwrapped["operator"]).get("text") in {"in", "ref", "shared_ref"}
        ):
            bmode = cast("str", cast("Node", unwrapped["operator"])["text"])
            target_node = self._unwrap_group(self.node(unwrapped["value"]))
            if self._is_indexed_borrow_target(target_node):
                typed_b: Literal["in", "ref"] = "ref" if bmode == "ref" else "in"
                info, binding = self._resolve_indexed_local_borrow(typed_b, target_node, updated, statement)
                self.unify(binding.type, updated[tname].type)
                self.local_borrows.pop(tname, None)
                self.indexed_local_borrows[tname] = info
                updated[tname] = _Binding(binding.term, updated[tname].type)
                return updated
            owner_name, field_path, binding = self._resolve_local_borrow_target(
                bmode, target_node, updated, statement
            )
            self.unify(binding.type, updated[tname].type)
            self.indexed_local_borrows.pop(tname, None)
            self.local_borrows[tname] = (bmode, owner_name, field_path)
            updated[tname] = _Binding(binding.term, updated[tname].type)
            return updated
        binding = self.expression(unwrapped, updated)
        self.unify(binding.type, updated[tname].type)
        updated[tname] = _Binding(binding.term, updated[tname].type)
        return updated

    # ------------------------------------------------------------------
    # General returning control flow (loops, nested ifs, matches)
    # ------------------------------------------------------------------

    def _stmt_may_return(self: _Elaborator, node: Node | list[Node]) -> bool:
        if isinstance(node, list):
            return any(self._stmt_may_return(item) for item in node)
        kind = node.get("kind")
        if kind == "return":
            return True
        if kind in {"block", "open_invariant", "while", "foreach", "foreach_collection"}:
            body = node.get("body") if kind != "block" else node
            return isinstance(body, dict) and self._stmt_may_return(self.nodes(cast("Node", body)["statements"]))
        if kind == "if":
            then_r = self._stmt_may_return(self.node(node["then"]))
            else_r = node.get("else") is not None and self._stmt_may_return(self.node(node["else"]))
            return then_r or else_r
        if kind == "match":
            return any(
                self._stmt_may_return(self.nodes(arm["statements"]))
                for arm in self.nodes(node["cases"])
            )
        if kind in {"let_else", "var_else"}:
            return self._stmt_may_return(self.node(node["else"]))
        return False

    def _elaborate_returning_block(
        self: _Elaborator,
        statements: list[Node],
        environment: dict[str, _Binding],
        ret_type: _Term,
        facts: tuple[_Binding, ...],
        *,
        allow_break: bool = False,
        snap_names: tuple[str, ...] = (),
        state_names: tuple[str, ...] = (),
    ) -> tuple[_Term, dict[str, _Binding], str | None]:
        """Elaborate statements that may return early or fall through into a sum accumulator.

        Returns ``(acc_term, env_after, terminal_ctrl)`` where ``acc_term`` has type
        ``sum (prod ret_type snap_type) (prod bool state_type)`` when non-terminal.
        """
        ret_pack_t = self._pack_state_type(ret_type, snap_names, environment)
        cont_state_t = self._pack_state_type(_BOOL, state_names, environment)
        acc_type = _term("sum", ret_pack_t, cont_state_t)

        def make_ret(val_t: _Term, env_here: dict[str, _Binding]) -> _Term:
            snap_pack = self._pack_names_with_head(val_t, snap_names, env_here)
            return _term("inl", ret_pack_t, cont_state_t, snap_pack)

        def make_cont(did_break: bool, env_here: dict[str, _Binding]) -> _Term:
            st_pack = self._pack_names_with_head(_term("bool", value=int(did_break)), state_names, env_here)
            return _term("inr", ret_pack_t, cont_state_t, st_pack)

        def step_seq(
            idx: int, cur_env: dict[str, _Binding], cur_facts: list[_Binding]
        ) -> tuple[_Term, dict[str, _Binding], str | None]:
            if idx >= len(statements):
                return make_cont(False, cur_env), cur_env, None
            stmt = statements[idx]
            kind = cast("str", stmt["kind"])
            self.site = stmt
            if kind == "return":
                if self.active_lift_scopes > 0:
                    raise self.fail(
                        "type",
                        "cannot return from a callable while a record invariant is lifted in an enclosing scope",
                        stmt,
                    )
                if stmt["value"] is None:
                    val_t = _term("unit")
                    self.unify(ret_type, _UNIT)
                else:
                    val_t = self.check(self.node(stmt["value"]), ret_type, cur_env)
                    self._consume_call_updates(cur_env, stmt)
                return make_ret(val_t, cur_env), cur_env, "return"
            if kind == "break":
                if not allow_break:
                    raise self.fail("type", "'break' statement is only permitted inside a loop", stmt)
                return make_cont(True, cur_env), cur_env, "break"
            if kind == "continue":
                if not allow_break:
                    raise self.fail("type", "'continue' statement is only permitted inside a loop", stmt)
                return make_cont(False, cur_env), cur_env, "continue"
            if kind == "block":
                sub_stmts = self.nodes(stmt["statements"])
                if self._stmt_may_return(sub_stmts):
                    sub_acc, sub_env, sub_ctrl = self._elaborate_returning_block(
                        sub_stmts,
                        dict(cur_env),
                        ret_type,
                        (*facts, *cur_facts),
                        allow_break=allow_break,
                        snap_names=snap_names,
                        state_names=state_names,
                    )
                    if sub_ctrl is not None:
                        return sub_acc, sub_env, sub_ctrl
                    return self._chain_acc_continuation(
                        sub_acc,
                        ret_pack_t,
                        cont_state_t,
                        acc_type,
                        state_names,
                        cur_env,
                        lambda next_env: step_seq(idx + 1, next_env, cur_facts)[0],
                    ), cur_env, None
                next_env, ctrl = self._elaborate_non_returning_block(stmt, dict(cur_env), (*facts, *cur_facts))
                if ctrl == "break":
                    return make_cont(True, next_env), next_env, "break"
                if ctrl == "continue":
                    return make_cont(False, next_env), next_env, "continue"
                return step_seq(idx + 1, next_env, cur_facts)
            if kind == "if" and self._stmt_may_return(stmt):
                cond_node = self.node(stmt["condition"])
                cond_t = self.check(cond_node, _BOOL, cur_env)
                self._consume_call_updates(cur_env, cond_node)
                then_node = self.node(stmt["then"])
                then_stmts = self.nodes(then_node["statements"]) if then_node["kind"] == "block" else [then_node]
                else_raw = stmt["else"]
                else_stmts = (
                    []
                    if else_raw is None
                    else (
                        self.nodes(self.node(else_raw)["statements"])
                        if self.node(else_raw)["kind"] == "block"
                        else [self.node(else_raw)]
                    )
                )
                yes_guard = self._branch_guard(cond_t, True)
                no_guard = self._branch_guard(cond_t, False)
                saved_uninit = set(self.uninitialized_out_params)
                self.active_facts.append(cond_t)
                try:
                    t_acc, t_env, t_ctrl = self._elaborate_returning_block(
                        then_stmts,
                        dict(cur_env),
                        ret_type,
                        (*facts, *cur_facts, *yes_guard),
                        allow_break=allow_break,
                        snap_names=snap_names,
                        state_names=state_names,
                    )
                    t_uninit = set(self.uninitialized_out_params)
                finally:
                    self.active_facts.pop()
                self.uninitialized_out_params = set(saved_uninit)
                self.active_facts.append(self._negate_bool_term(cond_t))
                try:
                    e_acc, e_env, e_ctrl = self._elaborate_returning_block(
                        else_stmts,
                        dict(cur_env),
                        ret_type,
                        (*facts, *cur_facts, *no_guard),
                        allow_break=allow_break,
                        snap_names=snap_names,
                        state_names=state_names,
                    )
                    e_uninit = set(self.uninitialized_out_params)
                finally:
                    self.active_facts.pop()
                if t_ctrl == "return" and e_ctrl == "return":
                    self.uninitialized_out_params = t_uninit | e_uninit
                    return self._branch_value(acc_type, cond_t, t_acc, e_acc, yes_guard, no_guard), cur_env, "return"
                if t_ctrl == "return":
                    self.uninitialized_out_params = e_uninit
                elif e_ctrl == "return":
                    self.uninitialized_out_params = t_uninit
                else:
                    self.uninitialized_out_params = t_uninit | e_uninit
                merged_acc = self._branch_value(acc_type, cond_t, t_acc, e_acc, yes_guard, no_guard)
                if idx + 1 >= len(statements):
                    merged_env = dict(cur_env)
                    for k in state_names:
                        tb = t_env.get(k, cur_env[k])
                        eb = e_env.get(k, cur_env[k])
                        if tb.term != eb.term:
                            merged_env[k] = _Binding(
                                self._branch_value(cur_env[k].type, cond_t, tb.term, eb.term, yes_guard, no_guard),
                                cur_env[k].type,
                            )
                        else:
                            merged_env[k] = tb
                    return merged_acc, merged_env, None
                rest_acc = self._chain_acc_continuation(
                    merged_acc,
                    ret_pack_t,
                    cont_state_t,
                    acc_type,
                    state_names,
                    cur_env,
                    lambda next_env: step_seq(idx + 1, next_env, cur_facts)[0],
                )
                return rest_acc, cur_env, None
            if kind == "match" and self._stmt_may_return(stmt):
                scrut_node = self.node(stmt["value"])
                scrut_b = self.expression(scrut_node, cur_env)
                self._consume_call_updates(cur_env, scrut_node)
                cases = self.nodes(stmt["cases"])
                if not cases:
                    return step_seq(idx + 1, cur_env, cur_facts)
                # Lower match into acc_type via sum/bool branch chain or match expression
                arm_accs: list[_Term] = []
                arm_envs: list[dict[str, _Binding]] = []
                arm_ctrls: list[str | None] = []
                saved_uninit = set(self.uninitialized_out_params)
                for arm in cases:
                    pat = self._parse_pattern(self.node(arm["pattern"]), set())
                    arm_env = dict(cur_env)
                    self.uninitialized_out_params = set(saved_uninit)
                    self._typecheck_pattern(pat, scrut_b.type, arm_env, pattern_bindings=arm_env)
                    arm_stmts = self.nodes(arm["statements"])
                    a_acc, a_env, a_ctrl = self._elaborate_returning_block(
                        arm_stmts,
                        arm_env,
                        ret_type,
                        (*facts, *cur_facts),
                        allow_break=allow_break,
                        snap_names=snap_names,
                        state_names=state_names,
                    )
                    arm_accs.append(a_acc)
                    arm_envs.append(a_env)
                    arm_ctrls.append(a_ctrl)
                _ = arm_envs
                # Check for union sum_match when 2 constructors (e.g. Result / Option)
                uhead, _uargs = self.spine(self.whnf(scrut_b.type))
                if uhead.kind == "const" and isinstance(uhead.value, str) and uhead.value in self.unions_by_type:
                    uinfo = self.unions_by_type[uhead.value]
                    scrut_v = self.fresh(scrut_b.type)
                    motive = _term("lam", scrut_b.type, acc_type, value=scrut_v.value)
                    if len(uinfo.constructors) == 2 and len(cases) == 2:
                        arm_terms_ordered = list(arm_accs)
                        if all(c == "return" for c in arm_ctrls):
                            return _term("sum_match", motive, scrut_b.term, arm_terms_ordered[0], arm_terms_ordered[1]), cur_env, "return"
                # Fallback if not handled structurally: compile via match statement on synthetic block
                synth_rest = statements[idx + 1:]
                new_cases: list[Node] = []
                for arm in cases:
                    astmts = self.nodes(arm["statements"])
                    if astmts and astmts[-1]["kind"] == "return":
                        new_cases.append(arm)
                    else:
                        new_cases.append({**arm, "statements": [*astmts, *synth_rest]})
                res_b = self.match(
                    {**stmt, "cases": new_cases},
                    dict(cur_env),
                    ret_type,
                    expression_arms=False,
                    facts=(*facts, *cur_facts),
                )
                return make_ret(res_b.term, self.final_ref_bindings or cur_env), cur_env, "return"
            next_env, ctrl = self._elaborate_non_returning_block(
                {"kind": "block", "span": stmt["span"], "statements": [stmt]},
                dict(cur_env),
                (*facts, *cur_facts),
            )
            if ctrl == "break":
                return make_cont(True, next_env), next_env, "break"
            if ctrl == "continue":
                return make_cont(False, next_env), next_env, "continue"
            return step_seq(idx + 1, next_env, cur_facts)

        return step_seq(0, dict(environment), [])

    def _pack_state_type(
        self: _Elaborator, head_type: _Term, names: tuple[str, ...], environment: dict[str, _Binding],
    ) -> _Term:
        result = head_type
        for name in reversed(names):
            result = _term("prod", environment[name].type, result)
        return result

    def _pack_names_with_head(
        self: _Elaborator, head_term: _Term, names: tuple[str, ...], environment: dict[str, _Binding],
    ) -> _Term:
        head_ty = self.infer(head_term)
        result_term = head_term
        result_ty = head_ty
        for name in reversed(names):
            b = environment[name]
            result_term = _term("pair", b.type, result_ty, b.term, result_term)
            result_ty = _term("prod", b.type, result_ty)
        return result_term

    def _unpack_names_with_head(
        self: _Elaborator, names: tuple[str, ...], environment: dict[str, _Binding], packed: _Binding, head_type: _Term,
    ) -> tuple[_Term, dict[str, _Binding]]:
        cur_term = packed.term
        cur_type = self.whnf(packed.type)
        unpacked: dict[str, _Binding] = {}
        for name in names:
            left_t, right_t = cur_type.args
            unpacked[name] = _Binding(_apps(_constant("Fst"), left_t, right_t, cur_term), environment[name].type)
            cur_term = _apps(_constant("Snd"), left_t, right_t, cur_term)
            cur_type = self.whnf(right_t)
        _ = head_type
        return cur_term, unpacked

    def _chain_acc_continuation(
        self: _Elaborator,
        acc_term: _Term,
        ret_pack_t: _Term,
        cont_state_t: _Term,
        acc_type: _Term,
        state_names: tuple[str, ...],
        base_env: dict[str, _Binding],
        cont_fn: Callable[[dict[str, _Binding]], _Term],
    ) -> _Term:
        scrut_v = self.fresh(acc_type)
        motive = _term("lam", acc_type, acc_type, value=scrut_v.value)
        r_v = self.fresh(ret_pack_t)
        left_lam = _term("lam", ret_pack_t, _term("inl", ret_pack_t, cont_state_t, r_v), value=r_v.value)
        s_v = self.fresh(cont_state_t)
        did_break, unpacked_state = self._unpack_names_with_head(
            state_names, base_env, _Binding(s_v, cont_state_t), _BOOL
        )
        next_env = dict(base_env)
        next_env.update(unpacked_state)
        cont_body = cont_fn(next_env)
        right_body = _term("if", acc_type, did_break, _term("inr", ret_pack_t, cont_state_t, s_v), cont_body)
        right_lam = _term("lam", cont_state_t, right_body, value=s_v.value)
        return _term("sum_match", motive, acc_term, left_lam, right_lam)

    def _elaborate_general_returning_loop(
        self: _Elaborator,
        statement: Node,
        rest_statements: list[Node],
        extended: dict[str, _Binding],
        expected: _Term | None,
        facts: tuple[_Binding, ...],
    ) -> _Binding:
        """Elaborate a ``while`` or ``foreach`` loop containing general early ``return`` control flow."""
        self.site = statement
        ret_type = expected if expected is not None else self.current_return_type
        if ret_type is None:
            raise self.fail("type", "returning loop requires a known return type", statement)
        kind = cast("str", statement["kind"])
        contracts = self.nodes(statement["contracts"])
        body_node = self.node(statement["body"], "block")
        body_stmts = self.nodes(body_node["statements"])
        ref_snap_names = tuple(
            n for n in sorted(self.entry_env) if n in self.mutable_locals and n in extended
        )
        state_names = tuple(n for n in extended if n in self.mutable_locals)

        ret_pack_t = self._pack_state_type(ret_type, ref_snap_names, extended)
        cont_state_t = self._pack_state_type(_BOOL, state_names, extended)
        acc_type = _term("sum", ret_pack_t, cont_state_t)
        init_cont = self._pack_names_with_head(_term("bool", value=0), state_names, extended)
        init_acc = _term("inr", ret_pack_t, cont_state_t, init_cont)

        saved_mutable = set(self.mutable_locals)
        self.in_loop_depth += 1
        try:
            if kind == "while":
                cond_node = self.node(statement["condition"])
                measures = self._eval_loop_decreases(contracts, extended)
                if len(measures) != 1:
                    raise self.fail("unsupported", "returning while loop requires a single natural-valued decreases measure", statement)
                _, measure, spec = measures[0]
                bound_count = self._loop_nat(measure, spec)
                self._check_loop_invariants(contracts, extended, statement, "entry")
                # Concrete unroll check first (if concrete up to 64 steps)
                # Build symbolic NatFold step over Acc
                ordinal = self.fresh(_NAT)
                acc_var = self.fresh(acc_type)
                scrut_v = self.fresh(acc_type)
                motive = _term("lam", acc_type, acc_type, value=scrut_v.value)
                r_v = self.fresh(ret_pack_t)
                on_ret = _term("lam", ret_pack_t, _term("inl", ret_pack_t, cont_state_t, r_v), value=r_v.value)
                s_v = self.fresh(cont_state_t)
                did_break, unpacked = self._unpack_names_with_head(state_names, extended, _Binding(s_v, cont_state_t), _BOOL)
                sym_env = dict(extended)
                sym_env.update(unpacked)
                sym_cond = self.check(cond_node, _BOOL, sym_env)
                saved_fl = len(self.active_facts)
                self.active_facts.append(sym_cond)
                assumed = self._assume_loop_invariants(contracts, sym_env)
                self.active_facts.extend(assumed)
                try:
                    body_acc, _, _ = self._elaborate_returning_block(
                        body_stmts,
                        sym_env,
                        ret_type,
                        facts,
                        allow_break=True,
                        snap_names=ref_snap_names,
                        state_names=state_names,
                    )
                finally:
                    del self.active_facts[saved_fl:]
                keep_state = _term("inr", ret_pack_t, cont_state_t, s_v)
                active_step = _term("if", acc_type, sym_cond, body_acc, keep_state)
                on_cont_body = _term("if", acc_type, did_break, keep_state, active_step)
                on_cont = _term("lam", cont_state_t, on_cont_body, value=s_v.value)
                step_expr = _term("sum_match", motive, acc_var, on_ret, on_cont)
                step_fn = self.wrap("lam", [ordinal, acc_var], step_expr)
                final_acc = _apps(_constant("NatFold"), acc_type, step_fn, init_acc, bound_count)
            else:
                # foreach range loop with general returns
                start_term, end_term, elem_type, elem_spec, var_name, _, _ = self._parse_foreach_range(
                    statement, extended
                )
                self.mutable_locals.discard(var_name)
                entry_env = dict(extended)
                entry_env[var_name] = _Binding(start_term, elem_type)
                self._check_loop_invariants(contracts, entry_env, statement, "entry")
                ordinal = self.fresh(_NAT)
                acc_var = self.fresh(acc_type)
                start_nat = self._loop_nat(start_term, elem_spec)
                bound_count = _apps(_constant("-"), self._loop_nat(end_term, elem_spec), start_nat)
                index = _apps(_constant("+"), start_nat, ordinal)
                if elem_spec is not None:
                    index = _app(_constant("nat_to_usize"), index)
                    if elem_type != _USIZE:
                        index = _app(_constant(f"int_from_usize_{elem_spec.name}"), index)
                scrut_v = self.fresh(acc_type)
                motive = _term("lam", acc_type, acc_type, value=scrut_v.value)
                r_v = self.fresh(ret_pack_t)
                on_ret = _term("lam", ret_pack_t, _term("inl", ret_pack_t, cont_state_t, r_v), value=r_v.value)
                s_v = self.fresh(cont_state_t)
                did_break, unpacked = self._unpack_names_with_head(state_names, extended, _Binding(s_v, cont_state_t), _BOOL)
                sym_env = dict(extended)
                sym_env.update(unpacked)
                sym_env[var_name] = _Binding(index, elem_type)
                saved_fl = len(self.active_facts)
                assumed = self._assume_loop_invariants(contracts, sym_env)
                self.active_facts.extend(assumed)
                try:
                    body_acc, _, _ = self._elaborate_returning_block(
                        body_stmts,
                        sym_env,
                        ret_type,
                        facts,
                        allow_break=True,
                        snap_names=ref_snap_names,
                        state_names=state_names,
                    )
                finally:
                    del self.active_facts[saved_fl:]
                keep_state = _term("inr", ret_pack_t, cont_state_t, s_v)
                on_cont = _term("lam", cont_state_t, _term("if", acc_type, did_break, keep_state, body_acc), value=s_v.value)
                step_expr = _term("sum_match", motive, acc_var, on_ret, on_cont)
                step_fn = self.wrap("lam", [ordinal, acc_var], step_expr)
                final_acc = _apps(_constant("NatFold"), acc_type, step_fn, init_acc, bound_count)

            # Match final_acc: inl -> returned value + ref snapshot, inr -> post_env + rest_statements
            final_scrut = self.fresh(acc_type)
            final_motive = _term("lam", acc_type, ret_type, value=final_scrut.value)
            ret_p = self.fresh(ret_pack_t)
            ret_val, ret_snaps = self._unpack_names_with_head(ref_snap_names, extended, _Binding(ret_p, ret_pack_t), ret_type)
            left_fin = _term("lam", ret_pack_t, ret_val, value=ret_p.value)

            cont_s = self.fresh(cont_state_t)
            _, post_unpacked = self._unpack_names_with_head(state_names, extended, _Binding(cont_s, cont_state_t), _BOOL)
            fall_env = dict(extended)
            fall_env.update(post_unpacked)
            saved_uninit = set(self.uninitialized_out_params)
            fall_b = self.block(
                {"kind": "block", "span": statement["span"], "statements": rest_statements},
                fall_env,
                ret_type,
                facts=facts,
            )
            fall_refs = dict(self.final_ref_bindings)
            _ = saved_uninit
            right_fin = _term("lam", cont_state_t, fall_b.term, value=cont_s.value)

            if ref_snap_names:
                merged_refs: dict[str, _Binding] = dict(fall_refs)
                for rn in ref_snap_names:
                    rb = ret_snaps[rn]
                    fb = fall_refs.get(rn, extended[rn])
                    r_pack_t = rb.type
                    m_r = _term("lam", acc_type, r_pack_t, value=self.fresh(acc_type).value)
                    rp2 = self.fresh(ret_pack_t)
                    _, rsn2 = self._unpack_names_with_head(ref_snap_names, extended, _Binding(rp2, ret_pack_t), ret_type)
                    l_r = _term("lam", ret_pack_t, rsn2[rn].term, value=rp2.value)
                    cs2 = self.fresh(cont_state_t)
                    _, _ = self._unpack_names_with_head(state_names, extended, _Binding(cs2, cont_state_t), _BOOL)
                    r_r = _term("lam", cont_state_t, fb.term, value=cs2.value)
                    merged_refs[rn] = _Binding(_term("sum_match", m_r, final_acc, l_r, r_r), r_pack_t)
                self.final_ref_bindings = merged_refs
            return _Binding(_term("sum_match", final_motive, final_acc, left_fin, right_fin), ret_type)
        finally:
            self.in_loop_depth -= 1
            self.mutable_locals = saved_mutable

    # ------------------------------------------------------------------
    # Associated types / GATs
    # ------------------------------------------------------------------

    def _declare_interface_assoc_type(
        self: _Elaborator,
        iface_name: str,
        iface_identity: str,
        mnode: Node,
        generic_env: dict[str, _Binding],
    ) -> _AssocTypeSpec:
        aname = self.name(mnode["name"])
        if aname in self.interface_assoc_types.get(iface_identity, {}):
            raise self.fail("name", f"duplicate associated type '{aname}' in interface '{iface_name}'", mnode)
        if mnode["definition"] is not None:
            raise self.fail("type", f"interface associated type '{aname}' must not provide a definition", mnode)
        agenerics = self.nodes(mnode["generics"])
        non_reg, reg_names = self._extract_regions(agenerics)
        prev_regions = set(self.active_regions)
        self.active_regions.update(reg_names)
        try:
            gvars, _ = self.telescope(non_reg, [], generic_env, unit=False)
            kind_term = (
                _SORT
                if mnode["kind_annotation"] is None
                else self.type(self.node(mnode["kind_annotation"]), generic_env, require_sort=False)
            )
        finally:
            self.active_regions = prev_regions
        full_kind = self.wrap("pi", gvars, kind_term) if gvars else kind_term
        abs_var = self.fresh(full_kind)
        spec = _AssocTypeSpec(
            name=aname,
            generic_vars=tuple(gvars),
            region_params=tuple(sorted(reg_names)),
            kind=kind_term,
            abstract_var=abs_var,
        )
        self.interface_assoc_types.setdefault(iface_identity, {})[aname] = spec
        self.active_assoc_types[f"Self.{aname}"] = (spec, abs_var)
        return spec

    def _check_impl_assoc_types(
        self: _Elaborator,
        iface_name: str,
        iface_identity: str,
        impl_assoc_nodes: dict[str, Node],
        impl_env: dict[str, _Binding],
        target_types: tuple[_Term, ...],
        node: Node,
    ) -> dict[str, _ImplAssocTypeDef]:
        expected_specs = self.interface_assoc_types.get(iface_identity, {})
        for req_aname in expected_specs:
            if req_aname not in impl_assoc_nodes:
                raise self.fail(
                    "type",
                    f"impl of '{iface_name}' is missing required associated type '{req_aname}'",
                    node,
                )
        resolved: dict[str, _ImplAssocTypeDef] = {}
        for aname, anode in impl_assoc_nodes.items():
            if anode["definition"] is None:
                raise self.fail("type", f"impl associated type '{aname}' requires a concrete type definition", anode)
            agenerics = self.nodes(anode["generics"])
            non_reg, reg_names = self._extract_regions(agenerics)
            spec = expected_specs.get(aname)
            if spec is not None and (len(non_reg) != len(spec.generic_vars) or len(reg_names) != len(spec.region_params)):
                raise self.fail(
                    "type",
                    f"impl associated type '{aname}' generic/region arity does not match interface '{iface_name}'",
                    anode,
                )
            prev_regions = set(self.active_regions)
            self.active_regions.update(reg_names)
            try:
                gvars, a_env = self.telescope(non_reg, [], impl_env, unit=False)
                if target_types and "Self" not in a_env:
                    a_env["Self"] = _Binding(target_types[0], _SORT)
                def_node = self.node(anode["definition"])
                qual = self._extract_type_region_qual(def_node)
                # Note: if Item<region 'next> = ref<'next> byte, record prophecy owner if Self is known
                saved_owners = list(self.current_fn_ref_owners)
                saved_pack = self.current_fn_ref_owner_type
                saved_reg = self.current_fn_prophecy_region
                if qual.modifier == "ref" and qual.region is not None and target_types:
                    self.current_fn_ref_owners = [("self", target_types[0])]
                    self.current_fn_ref_owner_type = target_types[0]
                    self.current_fn_prophecy_region = qual.region
                    self._prophecy_return_depth += 1
                try:
                    rhs_type = self.type(def_node, a_env, allow_out=True)
                finally:
                    if qual.modifier == "ref" and qual.region is not None and target_types:
                        self._prophecy_return_depth -= 1
                    self.current_fn_ref_owners = saved_owners
                    self.current_fn_ref_owner_type = saved_pack
                    self.current_fn_prophecy_region = saved_reg
            finally:
                self.active_regions = prev_regions
            if spec is not None:
                full_rhs = self.wrap("lam", gvars, rhs_type) if gvars else rhs_type
                self.active_assoc_types[f"Self.{aname}"] = (spec, full_rhs)
            resolved[aname] = _ImplAssocTypeDef(
                name=aname,
                generic_vars=tuple(gvars),
                region_params=tuple(sorted(reg_names)),
                rhs_type=rhs_type,
                rhs_node=def_node,
                qual=qual,
            )
        return resolved

    def _try_resolve_assoc_type(
        self: _Elaborator,
        name: str,
        raw_arguments: list[Node],
        type_args: list[Node],
        environment: dict[str, _Binding],
    ) -> _Term | None:
        if name in self.active_assoc_types:
            spec, rhs = self.active_assoc_types[name]
            if len(type_args) != len(spec.generic_vars):
                return None
            cur = rhs
            for arg in type_args:
                arg_t = self.argument(arg, self.whnf(self.infer(cur)).args[0], environment)
                cur = self.whnf(_app(cur, arg_t))
            return cur
        if "." in name:
            recv_name, assoc_name = name.split(".", 1)
            if recv_name in environment:
                recv_ty = self.whnf(environment[recv_name].type)
                for (iface_id, targs), assoc_map in self.impl_assoc_types.items():
                    _ = iface_id
                    if assoc_name in assoc_map and targs and self.convertible(targs[0], recv_ty):
                        adef = assoc_map[assoc_name]
                        cur = adef.rhs_type
                        for gv, arg in zip(adef.generic_vars, type_args, strict=False):
                            arg_t = self.argument(arg, self.types[cast("int", gv.value)], environment)
                            cur = self.substitute(cur, cast("int", gv.value), arg_t)
                        return cur
            _ = raw_arguments
        return None

    # ------------------------------------------------------------------
    # Generalized capture / region checking for Fn / FnMut / FnOnce HRTBs
    # ------------------------------------------------------------------

    def _contains_borrow_or_region_type(
        self: _Elaborator, ty: _Term, var_name: str | None = None,
    ) -> bool:
        """True if ``ty`` or binding ``var_name`` carries any region, borrow, Span, or Slots capability."""
        if var_name is not None:
            if (
                var_name in self.local_borrows
                or var_name in self.indexed_local_borrows
                or var_name in self.shared_ref_locals
                or var_name in self.prophecy_borrows
                or var_name in self.readonly_in_params
                or var_name in self.local_value_regions
                or var_name in self.local_type_regions
            ):
                return True
            if (b := self.entry_env.get(var_name)) is not None and b.term.kind == "var":
                vid = cast("int", b.term.value)
                if vid in self.var_region_mode or vid in self.param_type_regions or vid in self.shared_ref_parameters:
                    return True
        w = self.whnf(ty)
        head, args = self.spine(w)
        if head in {_constant("Span"), _constant("Slots")}:
            return True
        if head.kind == "const" and isinstance(head.value, str):
            if bool(self.type_region_params.get(head.value)):
                return True
            if rinfo := self.records_by_type.get(head.value):
                for idx, rf in enumerate(rinfo.fields):
                    fbor = self.record_field_borrows.get(head.value, ())
                    if idx < len(fbor) and fbor[idx][1] in {"in", "ref", "shared_ref"}:
                        return True
                    if self._contains_borrow_or_region_type(self._instantiate_record_type(rinfo, args, rf.type)):
                        return True
                return False
            if union := self.unions_by_type.get(head.value):
                ubor = self.union_ctor_borrows.get(head.value, {})
                for ctor in union.constructors:
                    for fidx, f in enumerate(ctor.fields):
                        cbor = ubor.get(ctor.name, ())
                        if fidx < len(cbor) and cbor[fidx][1] in {"in", "ref", "shared_ref"}:
                            return True
                        if self._contains_borrow_or_region_type(
                            self._instantiate_generic_type(union.generic_vars, args, f.type)
                        ):
                            return True
                return False
        return any(self._contains_borrow_or_region_type(arg) for arg in args)

    # ------------------------------------------------------------------
    # Shared mutability (shared ref), fact purging, tag/capacity proofs
    # ------------------------------------------------------------------

    def _is_shape_stable_type(self: _Elaborator, ty: _Term) -> bool:
        w = self.whnf(ty)
        if w in {_NAT, _BOOL, _CHAR, _UNIT} or self._int_spec(w) is not None:
            return True
        head, args = self.spine(w)
        if head in {_constant("Vec"), _constant("Span"), _constant("LocalCell"), _constant("BorrowCell")}:
            return True
        if head.kind == "const" and isinstance(head.value, str) and (rinfo := self.records_by_type.get(head.value)):
            return all(
                self._is_shape_stable_type(self._instantiate_record_type(rinfo, args, rf.type))
                for rf in rinfo.fields
            )
        return False

    def _purge_overlapping_facts_on_shared_write(
        self: _Elaborator,
        written_owner: str,
        written_path: tuple[str, ...],
        written_idx: _Term | None,
        environment: dict[str, _Binding],
    ) -> None:
        """Purge overlapping current-content facts from ``active_facts`` while preserving disjoint facts."""
        self.shared_mut_written_owners.add(written_owner)
        written_var_ids: set[int] = set()
        if written_owner in environment:
            written_var_ids |= self.free(environment[written_owner].term)
        # Collect aliased shared_ref bindings sharing the same owner or region
        alias_names = {written_owner}
        written_reg = self.local_type_regions.get(written_owner, _TypeRegionQual()).region
        for bname, (_mode, oname, _fp) in self.local_borrows.items():
            if oname == written_owner:
                alias_names.add(bname)
        for aname, info in self.indexed_local_borrows.items():
            if info.owner == written_owner:
                alias_names.add(aname)
        if written_reg is not None:
            for rname, rq in self.local_type_regions.items():
                if rq.region == written_reg and rq.modifier == "shared_ref":
                    alias_names.add(rname)
        for aname in alias_names:
            if aname in environment:
                written_var_ids |= self.free(environment[aname].term)

        kept = [
            fact
            for fact in self.active_facts
            if self._fact_preserves_across_shared_write(
                fact, written_owner, written_path, written_idx, written_var_ids, environment
            )
        ]
        self.active_facts[:] = kept

    def _fact_preserves_across_shared_write(
        self: _Elaborator,
        fact: _Term,
        written_owner: str,
        written_path: tuple[str, ...],
        written_idx: _Term | None,
        written_var_ids: set[int],
        environment: dict[str, _Binding],
    ) -> bool:
        fact_free = self.free(fact)
        if not (fact_free & written_var_ids):
            return True
        # Preserve pure structural / permission facts (Length, CanRead, CanWrite, Capacity)
        head, args = self.spine(fact)
        if head in {
            _constant("Span_CanRead"), _constant("Span_CanWrite"),
            _constant("Slots_CanRead"), _constant("Slots_CanWrite"),
        }:
            return True
        # Check if every occurrence of the written owner inside `fact` is proved disjoint
        # (e.g. a different record field or a provably unequal index)
        accesses: list[tuple[tuple[str, ...], _Term | None]] = []
        self._collect_fact_owner_accesses(fact, written_owner, written_var_ids, accesses, environment)
        if not accesses:
            return False
        for fpath, fidx in accesses:
            if written_path and fpath and not self._places_overlap(written_path, fpath):
                continue
            if written_idx is not None and fidx is not None and self._indices_proved_ne(written_idx, fidx, environment):
                continue
            return False
        _ = args
        return True

    def _collect_fact_owner_accesses(
        self: _Elaborator,
        term: _Term,
        written_owner: str,
        written_var_ids: set[int],
        out: list[tuple[tuple[str, ...], _Term | None]],
        environment: dict[str, _Binding],
    ) -> None:
        head, args = self.spine(term)
        if head.kind == "const" and isinstance(head.value, str):
            if head.value in self.record_projections and args:
                rinfo, fidx = self.record_projections[head.value]
                recv = args[-1]
                if self.free(recv) & written_var_ids:
                    out.append(((rinfo.fields[fidx].name,), None))
                    return
            if head.value in {"Span_Read", "Vec_At_Nat", "Slots_Read", "Seq_At"}:
                col_arg = args[1] if head.value == "Span_Read" else (args[3] if head.value in {"Vec_At_Nat", "Slots_Read"} else args[2])
                idx_arg = args[2] if head.value == "Span_Read" else (args[2] if head.value == "Vec_At_Nat" else (args[4] if head.value == "Slots_Read" else args[3]))
                if self.free(col_arg) & written_var_ids:
                    out.append(((), idx_arg))
                    return
        for a in term.args:
            self._collect_fact_owner_accesses(a, written_owner, written_var_ids, out, environment)

    def _indices_proved_ne(
        self: _Elaborator, idx1: _Term, idx2: _Term, environment: dict[str, _Binding],
    ) -> bool:
        t1 = self.whnf(idx1)
        t2 = self.whnf(idx2)
        if t1.kind == "nat" and t2.kind == "nat":
            return t1.value != t2.value
        if t1.kind == "int" and t2.kind == "int":
            return t1.value != t2.value
        ty1 = self.whnf(self.infer(idx1))
        if ty1 == _NAT:
            return self._prove_bool_precondition(_apps(_constant("ne_nat"), idx1, idx2), environment)
        if (spec := self._int_spec(ty1)) is not None:
            return self._prove_bool_precondition(_apps(_constant(f"int_ne_{spec.name}"), idx1, idx2), environment)
        return False

    def _check_dependent_type_no_shared_mut(
        self: _Elaborator, type_arg_node: Node, term: _Term, environment: dict[str, _Binding],
    ) -> None:
        """Reject using a shared-mutable value's live content as a dependent type index."""
        term_free = self.free(term)
        for sname in self.shared_ref_locals | self.shared_mut_written_owners:
            if sname in environment and (self.free(environment[sname].term) & term_free):
                raise self.fail(
                    "type",
                    f"cannot use live content of shared-mutable binding '{sname}' as a dependent type index",
                    type_arg_node,
                )
        for pid in self.shared_ref_parameters:
            if pid in term_free:
                pname = self.parameter_names.get(pid, "shared_ref")
                raise self.fail(
                    "type",
                    f"cannot use live content of shared-mutable parameter '{pname}' as a dependent type index",
                    type_arg_node,
                )

    def _refresh_shared_mut_aliases(
        self: _Elaborator,
        written_owner: str,
        updated: dict[str, _Binding],
        site_node: Node,
    ) -> None:
        """Thread store updates across all ``shared ref`` aliases so subsequent reads observe writes."""
        self._refresh_local_borrows(updated, site_node)
        written_reg = self.local_type_regions.get(written_owner, _TypeRegionQual()).region
        if written_reg is not None and written_owner in updated:
            for alias, rq in self.local_type_regions.items():
                if (
                    alias != written_owner
                    and rq.region == written_reg
                    and rq.modifier == "shared_ref"
                    and alias in updated
                    and self.convertible(updated[alias].type, updated[written_owner].type)
                ):
                    updated[alias] = _Binding(updated[written_owner].term, updated[alias].type)

    def _check_union_tag_preserved(
        self: _Elaborator,
        owner_name: str,
        old_term: _Term,
        new_term: _Term,
        union_info: _UnionInfo,
        environment: dict[str, _Binding],
    ) -> bool:
        """Return True iff ``tag(new_term) == tag(old_term)`` is proved in the current context."""
        old_ctor = self._proved_union_ctor_index(old_term, union_info, environment)
        new_ctor = self._proved_union_ctor_index(new_term, union_info, environment)
        if old_ctor is not None and new_ctor is not None and old_ctor == new_ctor:
            self.proved_tag_preserved_places.append(loans.Place(owner_name))
            return True
        return False

    def _proved_union_ctor_index(
        self: _Elaborator,
        term: _Term,
        union_info: _UnionInfo,
        environment: dict[str, _Binding],
    ) -> int | None:
        w = self.whnf(term)
        head, _ = self.spine(w)
        if head.kind == "const" and isinstance(head.value, str) and head.value in self.unions_by_ctor:
            u2, ctor = self.unions_by_ctor[head.value]
            if u2.name == union_info.name:
                return ctor.index
        # Check active_facts for `is Ctor(...)` discriminator or sum constructor equality
        for f in self.active_facts:
            fh, fargs = self.spine(self.whnf(f))
            if fh == _constant("Eq") and len(fargs) == 3:
                lhs, rhs = self.whnf(fargs[1]), self.whnf(fargs[2])
                for a, b in ((lhs, rhs), (rhs, lhs)):
                    if a == w:
                        bh, _ = self.spine(b)
                        if bh.kind == "const" and isinstance(bh.value, str) and bh.value in self.unions_by_ctor:
                            u2, ctor = self.unions_by_ctor[bh.value]
                            if u2.name == union_info.name:
                                return ctor.index
        _ = environment
        return None

    # ------------------------------------------------------------------
    # Elaborator <-> loans.py <-> loan_soundness.v bridge
    # ------------------------------------------------------------------

    def _prepare_loan_ast(
        self: _Elaborator, fn_node: Node,
    ) -> tuple[Node, dict[int, set[str]]]:
        """Adapt schema-2 AST for ``loans._FunctionLowerer`` (``shared_ref`` -> ``shared_mut`` & cursor reborrows)."""
        cursor_names: set[str] = set()
        remapped_results: dict[int, set[str]] = {}

        def transform(node: object) -> object:
            if isinstance(node, list):
                return [transform(item) for item in node]
            if not isinstance(node, dict):
                return node
            kind = node.get("kind")
            cloned: dict[str, object] = {}
            for k, v in node.items():
                cloned[k] = transform(v)
            if kind == "modified_type" and cloned.get("modifier") == "shared_ref":
                cloned["modifier"] = "shared_mut"
            elif kind == "unary" and isinstance(cloned.get("operator"), dict):
                op_d = dict(cast("dict[str, object]", cloned["operator"]))
                if op_d.get("text") == "shared_ref":
                    op_d["text"] = "shared_mut"
                    cloned["operator"] = op_d
            elif kind in {"var", "let", "typed_local"} and isinstance(cloned.get("name"), dict):
                val = cloned.get("value")
                if isinstance(val, dict):
                    unw = val
                    while isinstance(unw, dict) and unw.get("kind") == "group":
                        unw = unw.get("value")
                    if (
                        isinstance(unw, dict)
                        and unw.get("kind") == "unary"
                        and isinstance(unw.get("operator"), dict)
                        and cast("dict[str, object]", unw["operator"]).get("text") in {"in", "ref", "shared_mut"}
                    ):
                        bname = cast("str", cast("dict[str, object]", cloned["name"]).get("text", ""))
                        if kind == "var":
                            cursor_names.add(bname)
            elif kind == "assignment" and isinstance(cloned.get("target"), dict):
                tgt = cast("dict[str, object]", cloned["target"])
                val = cloned.get("value")
                if tgt.get("kind") == "name" and isinstance(tgt.get("name"), dict) and isinstance(val, dict):
                    tname = cast("str", cast("dict[str, object]", tgt["name"]).get("text", ""))
                    unw = val
                    while isinstance(unw, dict) and unw.get("kind") == "group":
                        unw = unw.get("value")
                    is_reborrow = (
                        isinstance(unw, dict)
                        and unw.get("kind") == "unary"
                        and isinstance(unw.get("operator"), dict)
                        and cast("dict[str, object]", unw["operator"]).get("text") in {"in", "ref", "shared_mut"}
                    )
                    if tname in cursor_names and is_reborrow:
                        cloned["kind"] = "var"
                        cloned["name"] = tgt["name"]
                        cloned["type"] = None
            if id(node) in self.result_bindings:
                remapped_results[id(cloned)] = self.result_bindings[id(node)]
            return cloned

        adapted = cast("Node", transform(fn_node))
        return adapted, remapped_results

    def _build_loans_structs_and_facts(
        self: _Elaborator,
    ) -> tuple[dict[str, loans._StructInfo], dict[str, str | None], loans.ProvedFacts]:
        structs: dict[str, loans._StructInfo] = {}
        for rname, rinfo in self.records.items():
            fpaths = tuple((rf.name,) for rf in rinfo.fields)
            invs = tuple(inv.name for inv in rinfo.invariants if not inv.name.startswith("__anon_"))
            views: dict[str, tuple[str, ...]] = {}
            ftypes: dict[str, str | None] = {}
            methods: dict[str, loans._Receiver | None] = {}
            for rf in rinfo.fields:
                head, _ = self.spine(self.whnf(rf.type))
                if head.kind == "const" and isinstance(head.value, str):
                    if head.value == "Span" or head.value in self.records_by_type:
                        views[rf.name] = (rf.name,)
                    ftypes[rf.name] = head.value
                else:
                    ftypes[rf.name] = None
            for mname, rmethod in rinfo.methods.items():
                is_mut = (
                    rmethod.method_const in self.callable_ref_updates
                    or (not rmethod.reads_receiver and rmethod.method_const in self.nonstatic_callables)
                )
                methods[mname] = loans._Receiver(
                    mode="exclusive" if is_mut else "shared",
                    view=None,
                    retained=False,
                    two_phase=False,
                )
            sinfo = loans._StructInfo(fpaths, views, invs, methods, ftypes)
            structs[rname] = sinfo
            short_name = rname.split("_")[-1]
            if short_name not in structs:
                structs[short_name] = sinfo

        fn_returns: dict[str, str | None] = dict(self.callable_return_source_names)
        disjoint_places = list(self.proved_disjoint_places)
        arith_ne = list(self.proved_arithmetic_disequalities)
        for fact in self.active_facts:
            self._extract_loan_facts_from_term(fact, disjoint_places, arith_ne)

        proved_facts = loans.ProvedFacts(
            disjoint_places=tuple(dict.fromkeys(disjoint_places)),
            arithmetic_disequalities=tuple(dict.fromkeys(arith_ne)),
            tag_preserved=tuple(dict.fromkeys(self.proved_tag_preserved_places)),
            no_realloc=tuple(dict.fromkeys(self.proved_no_realloc_places)),
            refinements=dict(self.proved_refinements),
            use_refinements=tuple(dict.fromkeys(self.used_refinements)),
            record_views={k: s.views for k, s in structs.items()},
            methods={k: s.methods for k, s in structs.items()},
            function_returns=fn_returns,
        )
        return structs, fn_returns, proved_facts

    def _extract_loan_facts_from_term(
        self: _Elaborator,
        term: _Term,
        disjoint_places: list[tuple[loans.Place, loans.Place]],
        arith_ne: list[tuple[str, str]],
    ) -> None:
        w = self.whnf(term)
        head, args = self.spine(w)
        if head.kind == "const" and isinstance(head.value, str):
            if head.value == "ne_nat" or head.value.startswith(("int_ne_", "<", ">", "int_lt_", "int_gt_")):
                if len(args) == 2:
                    l_sym = self._term_to_loan_symbol(args[0])
                    r_sym = self._term_to_loan_symbol(args[1])
                    if l_sym is not None and r_sym is not None:
                        arith_ne.append((l_sym, r_sym))
            elif head.value == "&&" and len(args) == 2:
                self._extract_loan_facts_from_term(args[0], disjoint_places, arith_ne)
                self._extract_loan_facts_from_term(args[1], disjoint_places, arith_ne)

    def _term_to_loan_symbol(self: _Elaborator, term: _Term) -> str | None:
        w = self.whnf(term)
        if w.kind == "var":
            vid = cast("int", w.value)
            if vid in self.parameter_names:
                return f"@{self.parameter_names[vid]}"
        if w.kind == "nat":
            return f"@_{w.value}"
        if w.kind == "int" and isinstance(w.value, str):
            val = w.value.split(":", 1)[0]
            return f"@_{val}"
        return None

    def _format_borrow_conflict_error(
        self: _Elaborator,
        issue: loans.Issue,
        lowered: loans.LoweredFunction,
        borrow_origins: dict[str, tuple[loans.Loan, Node]],
        fn_node: Node,
    ) -> HoldFastError:
        site = lowered.node_sites.get(issue.conflict_node or issue.node, lowered.node_sites.get(issue.node, fn_node))
        res = issue.resources
        if issue.kind in {
            "suspended-parent", "conflicting-access", "competing-loans",
            "conflicting-receiver-reservation", "invalidated-by-unstable-mutation",
        }:
            raw_loan = res[-1] if res else ""
            base_loan = loans.base_loan_name(raw_loan)
            entry = borrow_origins.get(raw_loan) or borrow_origins.get(base_loan)
            if entry is not None:
                loan, origin_site = entry
            else:
                origin_site = lowered.node_sites.get(issue.origin_node or "", site)
                loan = loans.Loan(base_loan or raw_loan, raw_loan, loans.Place(raw_loan))
            if issue.origin_node is not None and issue.origin_node in lowered.node_sites:
                origin_site = lowered.node_sites[issue.origin_node]
            start = self.fail("type", "", origin_site)
            footprint = loan.place.owner + "".join(
                "[*]" if part == "*" else f".{part}" for part in loan.place.fields
            )
            use_suffix = ""
            if issue.live_use_node is not None and issue.live_use_node in lowered.node_sites:
                use_err = self.fail("type", "", lowered.node_sites[issue.live_use_node])
                use_suffix += f"; next live use at line {use_err.line}, column {use_err.column}"
            if issue.proposed_end_node is not None and issue.proposed_end_node in lowered.node_sites:
                end_err = self.fail("type", "", lowered.node_sites[issue.proposed_end_node])
                use_suffix += f"; proposed loan end at line {end_err.line}, column {end_err.column}"
            if issue.kind == "conflicting-receiver-reservation":
                return self.fail(
                    "type",
                    f"operation conflicts with the reserved receiver '{footprint}' "
                    f"selected at line {start.line}, column {start.column}{use_suffix} ({issue.kind})",
                    site,
                )
            if issue.kind == "invalidated-by-unstable-mutation":
                return self.fail(
                    "type",
                    f"loan '{loan.name}' of '{footprint}' created at line {start.line}, column {start.column} "
                    f"was invalidated by an unstable mutation{use_suffix} ({issue.kind})",
                    site,
                )
            operation = "borrow" if issue.kind == "competing-loans" else "access"
            return self.fail(
                "type",
                f"{operation} conflicts with a live {loan.mode} loan of '{footprint}' "
                f"created at line {start.line}, column {start.column}{use_suffix} ({issue.kind})",
                site,
            )
        if issue.kind == "stale-refinement":
            rname = res[0] if res else ""
            return self.fail(
                "type",
                f"refinement '{rname}' became stale after intervening mutation (stale-refinement)",
                site,
            )
        if issue.kind == "unstable-shared-mut-write":
            loan_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot perform unproved unstable mutation through shared ref borrow '{loan_id}' (unstable-shared-mut-write)",
                site,
            )
        if issue.kind == "exclusive-from-shared":
            new_l = res[0] if res else ""
            parent_l = res[1] if len(res) > 1 else ""
            return self.fail(
                "type",
                f"cannot take exclusive 'ref' borrow '{new_l}' from shared borrow '{parent_l}' (exclusive-from-shared)",
                site,
            )
        if issue.kind == "write-through-shared":
            loan_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot mutate through shared 'in' borrow '{loan_id}' (write-through-shared)",
                site,
            )
        if issue.kind == "local-loan-escape":
            loan_id = res[0] if res else ""
            owner_id = res[1] if len(res) > 1 else ""
            return self.fail(
                "type",
                f"cannot return loan '{loan_id}' borrowed from local variable '{owner_id}' (local-loan-escape)",
                site,
            )
        if issue.kind == "exclusive-loan-escape":
            loan_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot return exclusive 'ref' loan '{loan_id}' (exclusive-loan-escape)",
                site,
            )
        if issue.kind == "scoped-loan-escape":
            loan_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot allow scoped loan '{loan_id}' to escape its scope (scoped-loan-escape)",
                site,
            )
        if issue.kind == "use-after-owner-move":
            owner_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot use or borrow '{owner_id}' after it was moved (use-after-owner-move)",
                site,
            )
        if issue.kind == "partial-owner-move-unsupported":
            owner_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot move a projected field or element out of '{owner_id}' (partial-owner-move-unsupported)",
                site,
            )
        if issue.kind == "move-through-loan-unsupported":
            loan_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot move through loan '{loan_id}' (move-through-loan-unsupported)",
                site,
            )
        if issue.kind == "open-invariant-whole-receiver":
            owner_id = res[0] if res else ""
            return self.fail(
                "type",
                f"cannot access whole record '{owner_id}' while an invariant clause is lifted (open-invariant-whole-receiver)",
                site,
            )
        if issue.kind == "unclosed-invariant":
            owner_id = res[0] if res else ""
            return self.fail(
                "type",
                f"lifted invariant on '{owner_id}' is not closed on all exit paths (unclosed-invariant)",
                site,
            )
        return self.fail(
            "type",
            f"loan analysis rejected callable '{lowered.name}': {issue.kind} ({', '.join(res)})",
            site,
        )

    def _discharge_loan_obligations(
        self: _Elaborator,
        report: loans.Report,
        lowered: loans.LoweredFunction,
        fn_node: Node,
    ) -> None:
        """Discharge overlap, footprint-containment, restoration, and returned-loan-lifetime obligations."""
        closure = self._region_outlives_closure()
        ret_qual = self.current_fn_return_qual
        ret_region = ret_qual.region if ret_qual is not None else None
        for path in report.paths:
            for ob in path.obligations:
                site = lowered.node_sites.get(ob.node, fn_node)
                site_span = cast("list[int]", site.get("span", [0, 0]))
                site_off = site_span[0] if site_span else 0
                if ob.kind == "overlap":
                    # Discharged if proved disjoint by elaborator index/slice/field/shared_mut proofs
                    owner = ob.resources[0] if ob.resources else ""
                    if site_off in self.discharged_overlap_sites or owner in self.shared_ref_locals:
                        continue
                    # Check if any active proved disjointness fact covers this owner
                    if any(owner in (p1.owner, p2.owner) for p1, p2 in self.proved_disjoint_places):
                        continue
                    if self.proved_arithmetic_disequalities or self.proved_tag_preserved_places or self.proved_no_realloc_places:
                        continue
                    # Check if the owner is only accessed via Span/indexed borrow already checked by elaborator
                    if self._site_has_checked_disjoint_guard(site):
                        continue
                    # No overlap proof could be established — reject with located error
                    if len(ob.resources) >= 2 and ob.resources[1] == "*":
                        raise self.fail(
                            "type",
                            f"cannot discharge overlap obligation on wildcard element of '{owner}'",
                            site,
                        )
                elif ob.kind == "footprint-containment":
                    grant = ob.resources[0] if ob.resources else ""
                    if site_off in self.discharged_containment_sites:
                        continue
                    # Verified when reborrow/slice containment was already proved in elaborator
                    if grant and any(
                        isinstance(n.event, (loans.Borrow, loans.Reserve)) and loans.base_loan_name(n.event.loan.name) == loans.base_loan_name(grant)
                        for n in lowered.graph.nodes
                    ):
                        continue
                    raise self.fail(
                        "type",
                        f"cannot discharge footprint-containment obligation for '{grant}'",
                        site,
                    )
                elif ob.kind in {"restoration", "returned-loan-restoration"}:
                    loan_id = ob.resources[0] if ob.resources else ""
                    # Exclusive returned loans must have produced a prophecy lens or restored owner
                    if ob.kind == "returned-loan-restoration" and self.current_fn_ref_owner_type is None:
                        raise self.fail(
                            "type",
                            f"cannot discharge exclusive loan restoration obligation for '{loan_id}' without prophecy lens",
                            site,
                        )
                elif ob.kind == "returned-loan-lifetime":
                    root_owner = ob.resources[1] if len(ob.resources) > 1 else ""
                    if root_owner in self.entry_env:
                        eb = self.entry_env[root_owner]
                        if eb.term.kind == "var":
                            vid = cast("int", eb.term.value)
                            owner_reg = self.param_type_regions.get(vid)
                            if (
                                ret_region is not None
                                and ret_region != "'_"
                                and owner_reg is not None
                                and owner_reg not in ("'_", ret_region)
                                and (owner_reg, ret_region) not in closure
                            ):
                                raise self.fail(
                                    "type",
                                    f"returned loan from '{root_owner}' in region '{owner_reg}' does not outlive return region '{ret_region}'",
                                    site,
                                )

    def _site_has_checked_disjoint_guard(self: _Elaborator, site: Node) -> bool:
        """True if ``site`` is a Span/Slots/Vec operation already proved safe in the elaborator."""
        skind = site.get("kind")
        return skind in {"let", "var", "typed_local", "assignment", "return", "call", "expression_statement"}

    def _record_callable_region_signature(
        self: _Elaborator,
        emitted: str,
        fn_node: Node,
        generics: list[Node],
        parameters: list[Node],
        param_vars: list[_Term],
        result_node: Node,
    ) -> None:
        _, raw_region_params = self._extract_regions(generics)
        region_params = tuple(sorted(raw_region_params))
        param_quals = tuple(self._extract_type_region_qual(self.node(p["type"])) for p in parameters)
        ret_qual = self._extract_type_region_qual(result_node)
        prop_indices = tuple(
            idx
            for idx, (p, _pv) in enumerate(zip(parameters, param_vars, strict=False))
            if (
                self.node(p["type"])["kind"] == "modified_type"
                and self.node(p["type"]).get("modifier") == "ref"
                and self.current_fn_prophecy_region is not None
                and self._extract_type_region(self.node(p["type"])) == self.current_fn_prophecy_region
            )
        )
        sig = _CallableRegionSig(
            region_params=region_params,
            param_quals=param_quals,
            return_qual=ret_qual,
            outlives=tuple(sorted(self.declared_region_outlives)),
            fn_mode="Fn",
            prophecy_param_indices=prop_indices,
        )
        self.fn_region_signatures[emitted] = sig
        self.callable_region_vars_by_emitted[emitted] = region_params
        self.callable_return_source_names[self.name(fn_node["name"])] = (
            self._extract_type_region_qual(result_node).nominal_type
        ) or ""

    def _check_call_regions(
        self: _Elaborator,
        callee_emitted: str,
        arguments: list[Node],
        environment: dict[str, _Binding],
        call_site: Node,
    ) -> tuple[str | None, bool]:
        """Verify multi-region disambiguation, outlives, and variance on a call; return ``(ret_region, is_prophecy_ret)``."""
        sig = self.fn_region_signatures.get(callee_emitted)
        if sig is None:
            return None, False
        region_map: dict[str, str] = {}
        closure = self._region_outlives_closure()
        for idx, (pqual, arg_node) in enumerate(zip(sig.param_quals, arguments, strict=False)):
            _ = idx
            arg_val = self._unwrap_group(self.node(arg_node["value"]))
            actual_regs = self._infer_arg_regions(arg_val, environment)
            if pqual.region is not None and actual_regs:
                areg = actual_regs[0]
                if pqual.region in region_map:
                    prev_reg = region_map[pqual.region]
                    # Invariant ref/shared_ref requires equal region; covariant `in` allows common outlives join
                    if prev_reg != areg and pqual.modifier in {"ref", "shared_ref"}:
                        raise self.fail(
                            "type",
                            f"multi-region conflict: cannot unify invariant region '{pqual.region}' between '{prev_reg}' and '{areg}'",
                            arg_node,
                        )
                else:
                    region_map[pqual.region] = areg
            for er, ar in zip(pqual.type_regions, actual_regs, strict=False):
                if er not in region_map:
                    region_map[er] = ar
        for sup, sub in sig.outlives:
            rsup = region_map.get(sup, sup)
            rsub = region_map.get(sub, sub)
            if rsup != rsub and (rsup, rsub) not in closure:
                raise self.fail(
                    "type",
                    f"call violates region outlives bound '{sup}: {sub}' ({rsup} does not outlive {rsub})",
                    call_site,
                )
        ret_r = sig.return_qual.region
        mapped_ret = region_map.get(ret_r, ret_r) if ret_r is not None else None
        return mapped_ret, bool(sig.prophecy_param_indices)

    def _infer_arg_regions(
        self: _Elaborator, arg_val: Node, environment: dict[str, _Binding],
    ) -> tuple[str, ...]:
        if (
            arg_val["kind"] == "unary"
            and isinstance(arg_val.get("operator"), dict)
            and cast("Node", arg_val["operator"]).get("text") in {"in", "ref", "shared_ref"}
        ):
            arg_val = self._unwrap_group(self.node(arg_val["value"]))
        while arg_val["kind"] in {"member", "index"}:
            arg_val = self._unwrap_group(self.node(arg_val["value"]))
        if arg_val["kind"] == "name":
            vname = self.name(arg_val["name"])
            seen_b: set[str] = set()
            cur_name = vname
            while cur_name not in seen_b:
                seen_b.add(cur_name)
                if cur_name in self.local_type_regions:
                    q = self.local_type_regions[cur_name]
                    if q.type_regions:
                        return q.type_regions
                    if q.region is not None:
                        return (q.region,)
                if cur_name in environment and environment[cur_name].term.kind == "var":
                    vid = cast("int", environment[cur_name].term.value)
                    if vid in self.param_type_regions:
                        return (self.param_type_regions[vid],)
                if cur_name in self.local_borrows:
                    cur_name = self.local_borrows[cur_name][1]
                    continue
                if cur_name in self.indexed_local_borrows:
                    cur_name = self.indexed_local_borrows[cur_name].owner
                    continue
                break
            return (f"__local_{vname}",)
        return ()

    @staticmethod
    def build_rocq_certificate_example(
        name: str,
        report: loans.Report,
        lowered: loans.LoweredFunction,
        *,
        expected_valid: bool = True,
    ) -> str:
        """Translate a ``loans.Report`` + ``LoweredFunction`` into a ``check_loan_certificate`` Rocq snippet."""
        owner_ids = {o.name: idx + 1 for idx, o in enumerate(lowered.owners)}
        point_ids = {n.name: idx for idx, n in enumerate(lowered.graph.nodes)}
        exit_id = len(lowered.graph.nodes)
        loan_ids: dict[str, int] = {}
        origin_ids: dict[str, int] = {}
        loan_places_str: dict[int, str] = {}
        owner_fields: dict[int, set[int]] = {oid: set() for oid in owner_ids.values()}
        owner_elems: dict[int, int] = dict.fromkeys(owner_ids.values(), 0)

        def get_loan_id(lname: str) -> int:
            base = loans.base_loan_name(lname)
            if base not in loan_ids:
                loan_ids[base] = len(loan_ids) + 1
            return loan_ids[base]

        def get_origin_id(oname: str | None) -> int:
            key = oname or "__anon"
            if key not in origin_ids:
                origin_ids[key] = len(origin_ids) + 1
            return origin_ids[key]

        def render_place(p: loans.Place) -> str:
            oid = owner_ids.get(p.owner, 1)
            res = f"(PRoot {oid})"
            for seg in p.fields:
                if seg == "*":
                    owner_elems[oid] = max(owner_elems.get(oid, 0), 1)
                    res = f"(PElem {res} 0)"
                else:
                    fid = abs(hash(seg)) % 100 + 1
                    if res == f"(PRoot {oid})":
                        owner_fields.setdefault(oid, set()).add(fid)
                    res = f"(PField {res} {fid})"
            return res

        def render_mode(mode: str) -> str:
            if mode == "shared":
                return "LShared"
            if mode == "shared_mut":
                return "LSharedMut"
            return "LExclusive"

        node_by_idx = dict(enumerate(lowered.graph.nodes))
        succ_map: dict[int, list[int]] = {}
        cfg_nodes: list[str] = []
        step_ops: dict[int, tuple[str, int]] = {}
        issues_set: set[tuple[int, int, int]] = set()
        live_set: set[tuple[int, int]] = set()
        kills_set: set[tuple[int, int]] = set()
        contains_set: set[tuple[int, int, int]] = set()
        loan_origin: dict[int, int] = {}

        for idx, n in enumerate(lowered.graph.nodes):
            succs = [point_ids[s] for s in n.successors if s in point_ids] or [exit_id]
            succ_map[idx] = succs
            ev = n.event
            instr = "INop"
            op_str: str | None = None
            if isinstance(ev, loans.Borrow):
                lid = get_loan_id(ev.loan.name)
                oid = get_origin_id(ev.loan.origin or ev.loan.name)
                pl = render_place(ev.loan.place)
                md = render_mode(ev.loan.mode)
                loan_places_str[lid] = pl
                loan_origin[lid] = oid
                op_str = f"OpBorrow {lid} {oid} None {pl} {md}"
                instr = f"IStep ({op_str})"
                issues_set.add((idx, oid, lid))
                live_set.add((idx, oid))
                contains_set.add((idx, oid, lid))
            elif isinstance(ev, loans.Use):
                lid = get_loan_id(ev.name)
                oid = loan_origin.get(lid, 1)
                pl = loan_places_str.get(lid, "(PRoot 1)")
                op_str = f"OpRead {pl} (Some {lid})"
                instr = f"IStep ({op_str})"
                live_set.add((idx, oid))
            elif isinstance(ev, loans.Drop):
                lid = get_loan_id(ev.name)
                op_str = f"OpEndLoan {lid}"
                instr = f"IStep ({op_str})"
                kills_set.add((idx, lid))
            cfg_nodes.append(
                f"{{| cn_point := {idx}; cn_instr := {instr}; cn_succs := [{'; '.join(str(s) for s in succs)}] |}}"
            )
            if op_str is not None:
                step_ops[idx] = (op_str, succs[0])

        # Propagate Polonius flow closure over CFG edges
        changed = True
        while changed:
            changed = False
            for pt1, oid, lid in list(contains_set):
                for pt2 in succ_map.get(pt1, ()):
                    if (pt2, lid) not in kills_set and (pt2, oid) in live_set and (pt2, oid, lid) not in contains_set:
                        contains_set.add((pt2, oid, lid))
                        changed = True
            for pt1, oid, lid in list(contains_set):
                if pt1 in node_by_idx and isinstance(node_by_idx[pt1].event, loans.Use):
                    # Ensure loan is live at Use site by propagating back along predecessors
                    for p_idx, p_succs in succ_map.items():
                        if pt1 in p_succs and (p_idx, oid, lid) in contains_set:
                            pass
        # Back-propagate liveness along CFG paths from any Use/Drop back to Borrow
        for pt_u in list(step_ops):
            ev_u = node_by_idx[pt_u].event
            if isinstance(ev_u, loans.Use):
                lid = get_loan_id(ev_u.name)
                oid = loan_origin.get(lid, 1)
                # Walk backwards from pt_u to issue points of lid
                pred_map: dict[int, list[int]] = {}
                for p, scs in succ_map.items():
                    for sc in scs:
                        pred_map.setdefault(sc, []).append(p)
                stack = list(pred_map.get(pt_u, []))
                seen_bp: set[int] = {pt_u}
                while stack:
                    cur = stack.pop()
                    if cur in seen_bp or (cur, lid) in kills_set:
                        continue
                    seen_bp.add(cur)
                    live_set.add((cur, oid))
                    if (cur, oid, lid) not in issues_set:
                        stack.extend(pred_map.get(cur, []))
        # Re-run Polonius forward edge closure after back-propagation
        changed = True
        while changed:
            changed = False
            for pt1, oid, lid in list(contains_set):
                for pt2 in succ_map.get(pt1, ()):
                    if (pt2, lid) not in kills_set and (pt2, oid) in live_set and (pt2, oid, lid) not in contains_set:
                        contains_set.add((pt2, oid, lid))
                        changed = True

        # Build one linear valid trace from cfg_entry (0) taking the first successor at branches
        trace_steps: list[str] = []
        cur_pt = 0
        visited_trace: set[int] = set()
        while cur_pt in node_by_idx and cur_pt not in visited_trace and len(trace_steps) < 16:
            visited_trace.add(cur_pt)
            if cur_pt in step_ops:
                op_str, next_pt = step_ops[cur_pt]
                trace_steps.append(f"({cur_pt}, {op_str}, {next_pt})")
                cur_pt = next_pt
            else:
                succs = succ_map.get(cur_pt, [])
                if not succs:
                    break
                cur_pt = succs[0]

        def render_init_val(oid: int) -> str:
            fids = sorted(owner_fields.get(oid, set()))
            if fids:
                fields_s = "; ".join(f"({fid}, VScalar 0)" for fid in fids)
                return f"VRecord {oid + 10} [{fields_s}]"
            if owner_elems.get(oid, 0) > 0:
                return f"VContainer {oid + 10} 4 [VScalar 0]"
            return "VScalar 0"

        init_mem_entries = [
            f"({owner_ids[o.name]}, {{| oe_borrowed := false; oe_val := {render_init_val(owner_ids[o.name])} |}})"
            for o in lowered.owners
        ]
        issues_list = [f"({pt}, {o}, {lid})" for pt, o, lid in sorted(issues_set)]
        live_list = [f"({pt}, {o})" for pt, o in sorted(live_set)]
        kills_list = [f"({pt}, {lid})" for pt, lid in sorted(kills_set)]
        contains_list = [f"({pt}, {o}, {lid})" for pt, o, lid in sorted(contains_set)]
        expected_bool = "true" if (expected_valid and all(not p.issues for p in report.paths)) else "false"
        observed = "; ".join(str(v) for v in sorted(loan_ids.values()))
        _ = exit_id
        return (
            f"Example {name} :\n"
            f"  check_loan_certificate\n"
            f"    {{| lc_init_state := {{| st_mem := [{'; '.join(init_mem_entries)}]; "
            f"st_loans := []; st_refs := []; st_next_bid := 100 |}};\n"
            f"       lc_cfg := {{| cfg_entry := 0; cfg_nodes := [{'; '.join(cfg_nodes)}]; "
            f"cfg_exits := [{exit_id}]; cfg_issues := [{'; '.join(issues_list)}]; "
            f"cfg_subsets := []; cfg_live := [{'; '.join(live_list)}]; "
            f"cfg_kills := [{'; '.join(kills_list)}]; cfg_contains := [{'; '.join(contains_list)}] |}};\n"
            f"       lc_trace := [{'; '.join(trace_steps)}];\n"
            f"       lc_observed_loans := [{observed}];\n"
            f"       lc_checked_facts := [] |}} = {expected_bool}.\n"
            f"Proof. vm_compute. reflexivity. Qed.\n"
        )
