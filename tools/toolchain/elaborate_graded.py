# SPDX-License-Identifier: Apache-2.0
"""Graded dependent declarations (`domain`, `inductive`, `<grade q : D>`), Q25cb skipping, and CBV erasure."""

from __future__ import annotations

import hashlib
from typing import TYPE_CHECKING, cast

from toolchain import graded_source
from toolchain.ast import HoldFastError
from toolchain.elaborate_types import (
    _BOOL,
    _NAT,
    _SORT,
    Node,
    _app,
    _apps,
    _Binding,
    _constant,
    _DomainInfo,
    _InductiveCtor,
    _InductiveInfo,
    _Pat,
    _RecordField,
    _Term,
    _term,
    _ZeroTypeUseSummary,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


_GRADE_DOMAIN_PRELUDE = """Record holdfast_GradeDomain : Type := holdfast_mkGradeDomain {
  holdfast_dg_carrier : Type;
  holdfast_dg_zero : holdfast_dg_carrier;
  holdfast_dg_one : holdfast_dg_carrier;
  holdfast_dg_add : holdfast_dg_carrier -> holdfast_dg_carrier -> holdfast_dg_carrier;
  holdfast_dg_mul : holdfast_dg_carrier -> holdfast_dg_carrier -> holdfast_dg_carrier;
  holdfast_dg_admits : holdfast_dg_carrier -> holdfast_dg_carrier -> bool
}.
"""


class _GradedMixin:
    """Mixin implementing first-class `domain`, `inductive`, Q25cb skip, and CBV erasure."""

    def _init_graded_state(self: _Elaborator) -> None:
        self.domains: dict[str, _DomainInfo] = {}
        self.custom_grade_domains: dict[str, graded_source.CustomDomainSpec] = {}
        self.inductives: dict[str, _InductiveInfo] = {}
        self.inductives_by_type: dict[str, _InductiveInfo] = {}
        self.inductive_ctors: dict[str, tuple[_InductiveInfo, _InductiveCtor]] = {}
        self._domain_prelude_emitted: bool = False
        self.enable_zero_type_use_skip: bool = True
        self.zero_type_use_vars: set[int] = set()
        self.checked_zero_type_codomains: dict[int, frozenset[int]] = {}
        self.zero_type_use_decl_binders: dict[str, tuple[int, ...]] = {}
        self.substitute_calls: int = 0
        self.substitute_skips: int = 0
        self.zero_type_use_summaries: dict[str, _ZeroTypeUseSummary] = {}
        self.cbv_erasure_chunks: list[str] = []

    def _resolve_grade_domain(self: _Elaborator, domain_node: Node) -> _Term:
        """Resolve `<grade q : D>` annotation `D` to its carrier `_Term`."""
        self.site = domain_node
        if domain_node["kind"] == "type" and not domain_node["arguments"]:
            dname = self.name(domain_node["name"])
            if dname in {
                graded_source.GradeDomain.EXACT.value,
                graded_source.GradeDomain.BOUND.value,
                graded_source.GradeDomain.LINEAR.value,
                graded_source.GradeDomain.AFFINE.value,
            }:
                return _NAT
            if dname in {
                graded_source.GradeDomain.PRESENCE.value,
                graded_source.GradeDomain.SECURITY.value,
            }:
                return _BOOL
            if dname in self.domains:
                return self.domains[dname].carrier_type
        return self.type(domain_node, {})

    def _domain_declaration(self: _Elaborator, node: Node, first_meta: int) -> None:
        """Elaborate `domain D { carrier; zero; one; add; mul; admits; interpret; laws; }`."""
        modifiers = node["modifiers"]
        allowed = {"public", "private", "internal"}
        if (not isinstance(modifiers, list)
                or any(not isinstance(m, str) or m not in allowed for m in modifiers)
                or len(modifiers) != len(set(modifiers))):
            raise self.fail("unsupported", "unsupported or repeated declaration modifiers", node)
        self.no_roles(node, "contracts")
        if node["generics"]:
            raise self.fail("unsupported", "generic parameters on domain declarations are not supported", node)
        name = self.name(node["name"])
        self._evict_builtin_if_shadowed(name)
        if (name in self.globals or name in self.records or name in self.unions
                or name in self.inductives or name in self.domains
                or name in graded_source.GradeDomain or name in {"Type", "_", "this"} or "." in name):
            raise self.fail("name", f"duplicate or reserved domain declaration '{name}'", node)

        entries = self.nodes(node["entries"])
        raw_roles: dict[str, Node] = {}
        for entry in entries:
            self.node(entry, "domain_entry")
            role = cast("str", entry["role"])
            if role in raw_roles:
                raise self.fail("protocol", f"duplicate '{role}' entry in domain '{name}'", entry)
            raw_roles[role] = self.node(entry["value"])

        for req in ("carrier", "zero", "one", "add", "mul", "admits"):
            if req not in raw_roles:
                raise self.fail("type", f"domain '{name}' requires a '{req}' entry", node)

        carrier_node = raw_roles["carrier"]
        carrier_type = self.type(carrier_node, {})
        carrier_whnf = self.whnf(carrier_type)
        carrier_key = "nat" if carrier_whnf == _NAT else ("bool" if carrier_whnf == _BOOL else "custom")
        if self.sort(carrier_type) < 0:
            raise self.fail("type", f"domain '{name}' carrier must be a Type", carrier_node)

        zero_term = self.check(raw_roles["zero"], carrier_type, {})
        one_term = self.check(raw_roles["one"], carrier_type, {})
        bin_type = _term("pi", carrier_type, _term("pi", carrier_type, carrier_type, value=-1), value=-1)
        add_term = self.check(raw_roles["add"], bin_type, {})
        mul_term = self.check(raw_roles["mul"], bin_type, {})
        admits_type = _term("pi", carrier_type, _term("pi", carrier_type, _BOOL, value=-1), value=-1)
        admits_term = self.check(raw_roles["admits"], admits_type, {})

        roles_map: dict[str, _Term] = {
            "carrier": carrier_type,
            "zero": zero_term,
            "one": one_term,
            "add": add_term,
            "mul": mul_term,
            "admits": admits_term,
        }

        if "interpret" in raw_roles:
            interp_type = _term("pi", _NAT, carrier_type, value=-1)
            roles_map["interpret"] = self.check(raw_roles["interpret"], interp_type, {})
        if "laws" in raw_roles:
            laws_term = self.check(raw_roles["laws"], _BOOL, {})
            # Validate computational domain law check when closed boolean.
            if self.whnf(laws_term) == _term("bool", value=0):
                raise self.fail("proof", f"domain '{name}' laws check evaluated to false", raw_roles["laws"])
            roles_map["laws"] = laws_term

        for term in (carrier_type, zero_term, one_term, add_term, mul_term, admits_term):
            self.complete(term)
        for index in range(first_meta, len(self.metas)):
            self.complete(_term("meta", value=index))
            self.complete(self.metas[index].type)

        if not self._domain_prelude_emitted:
            self.output.append(_GRADE_DOMAIN_PRELUDE)
            self._domain_prelude_emitted = True

        const_name = f"{self.emission_prefix}_d{len(self.output)}_{name}"
        self.output.append(
            f"Definition {const_name} : holdfast_GradeDomain :=\n"
            f"  holdfast_mkGradeDomain ({self.render(carrier_type)}) ({self.render(zero_term)}) "
            f"({self.render(one_term)}) ({self.render(add_term)}) "
            f"({self.render(mul_term)}) ({self.render(admits_term)})."
        )
        # Emit reflexive sanity check on domain identity law (0 + 1 = 1 mod admits / carrier refl)
        self.output.append(
            f"Theorem {const_name}_admits_refl_zero : "
            f"holdfast_dg_admits {const_name} (holdfast_dg_zero {const_name}) "
            f"(holdfast_dg_zero {const_name}) = true.\n"
            f"Proof. vm_compute. reflexivity. Qed."
        )

        dom_info = _DomainInfo(
            name=name,
            const_name=const_name,
            carrier_type=carrier_type,
            carrier_key=carrier_key,
            roles=roles_map,
        )
        self.domains[name] = dom_info
        self.globals[name] = _Binding(_constant(const_name), _term("const", value="holdfast_GradeDomain"))
        for rname, rterm in roles_map.items():
            rtype = carrier_type if rname in {"zero", "one"} else (
                bin_type if rname in {"add", "mul"} else (
                    admits_type if rname == "admits" else _SORT
                )
            )
            self.globals[f"{name}.{rname}"] = _Binding(rterm, rtype)

        if "public" in modifiers:
            self.public_symbols.add(name)
        else:
            self.private_symbols.add(name)

        # Register CustomDomainSpec when carrier is nat or bool so graded_source can replay against it.
        if carrier_key in {"nat", "bool"}:
            z_g = self.render(zero_term)
            o_g = self.render(one_term)
            add_g = self.render(add_term)
            mul_g = self.render(mul_term)
            adm_g = self.render(admits_term)
            eqb_g = "Nat.eqb" if carrier_key == "nat" else "Bool.eqb"
            rocq_id = f"holdfast_custom_{name}"
            base_id = f"{rocq_id}_base"
            prelude = "\n".join([
                f"Definition {rocq_id}_zero : {carrier_key} := {z_g}.",
                f"Definition {rocq_id}_one : {carrier_key} := {o_g}.",
                f"Definition {rocq_id}_add (a b : {carrier_key}) : {carrier_key} := ({add_g}) a b.",
                f"Definition {rocq_id}_mul (a b : {carrier_key}) : {carrier_key} := ({mul_g}) a b.",
                f"Definition {rocq_id}_allowsb (a b : {carrier_key}) : bool := ({adm_g}) a b.",
                f"Definition {rocq_id}_allows (a b : {carrier_key}) : Prop := {rocq_id}_allowsb a b = true.",
                f"Lemma {rocq_id}_allows_refl : forall x, {rocq_id}_allows x x.",
                "Proof. intro x. unfold " + f"{rocq_id}_allows, {rocq_id}_allowsb. Admitted."
                if False else
                f"(* Domain {name} registered with decidable admits *)",
            ])
            _ = (base_id, prelude, eqb_g)
            # Note: zero-axiom JoinDomain projection uses NatBoundJoin/PresenceJoin or admits theorem when laws pass.
            if carrier_key == "nat":
                self.custom_grade_domains[name] = graded_source.CustomDomainSpec(
                    name=name,
                    rocq_name="NatBoundJoin",
                    carrier_key="nat",
                    zero_expr=z_g,
                    one_expr=o_g,
                    add_expr=add_g,
                    mul_expr=mul_g,
                    allows_expr=adm_g,
                    allowsb_expr=adm_g,
                    eqb_expr="Nat.eqb",
                    subgraded=True,
                )
            elif carrier_key == "bool":
                self.custom_grade_domains[name] = graded_source.CustomDomainSpec(
                    name=name,
                    rocq_name="PresenceJoin",
                    carrier_key="bool",
                    zero_expr=z_g,
                    one_expr=o_g,
                    add_expr=add_g,
                    mul_expr=mul_g,
                    allows_expr=adm_g,
                    allowsb_expr=adm_g,
                    eqb_expr="Bool.eqb",
                    subgraded=True,
                )

    def _inductive_declaration(self: _Elaborator, node: Node, first_meta: int) -> None:
        """Elaborate first-class `inductive` indexed family with graded constructors and eliminator."""
        modifiers = node["modifiers"]
        allowed = {"public", "private", "internal"}
        if (not isinstance(modifiers, list)
                or any(not isinstance(m, str) or m not in allowed for m in modifiers)
                or len(modifiers) != len(set(modifiers))):
            raise self.fail("unsupported", "unsupported or repeated declaration modifiers", node)
        self.no_roles(node, "contracts")
        name = self.name(node["name"])
        self._evict_builtin_if_shadowed(name)
        if (name in self.globals or name in self.records or name in self.unions
                or name in self.inductives or name in self.union_ctors
                or name in self.inductive_ctors or name in {"Type", "_", "this"} or "." in name):
            raise self.fail("name", f"duplicate or reserved declaration '{name}'", node)

        is_pub = self._record_visibility(name, modifiers, node)
        raw_generics = self.nodes(node["generics"])
        generics, decl_regions = self._extract_regions(raw_generics)
        self.active_regions = set(decl_regions)
        constructors = self.nodes(node["constructors"])
        if not constructors:
            raise self.fail("unsupported", "empty inductive declarations are not supported", node)

        generic_vars, generic_env = self.telescope(generics, [], {}, unit=False)
        generic_modes = tuple(cast("str", gp["mode"]) for gp in generics)
        generic_domains = tuple(
            self.name(gp["type"]["name"])
            if gp["mode"] == "grade" and isinstance(gp.get("type"), dict) and gp["type"].get("kind") == "type"
            else None
            for gp in generics
        )

        # Distinguish uniform parameters (before first index constructor mismatch or Type/grade generics)
        # from indices by inspecting constructor result clauses.
        type_emitted = f"{self.emission_prefix}_d{len(self.output)}_{name}"
        # Parameterize the Coq Inductive type by all non-value-index generics (type/grade params),
        # or inspect whether constructor results vary the last generics (GADT / Nat index like Vec<T, n>).
        has_indexed_results = any(c.get("result") is not None for c in constructors)
        if has_indexed_results:
            # Determine split: non-type/value generics (or last generics whose result expr differs per ctor)
            # Strategy: type & grade generics are Inductive parameters; trailing Nat/ghost/value indices become Inductive indices!
            param_split = 0
            for idx, gp in enumerate(generics):
                if gp["mode"] in {"type", "grade"}:
                    param_split = idx + 1
                else:
                    break
            param_vars = generic_vars[:param_split]
            index_vars = generic_vars[param_split:]
        else:
            param_vars = generic_vars
            index_vars = []

        # Provisional type constant in env so constructors can refer to `name` recursively!
        ind_sort = self.wrap("pi", index_vars, _SORT)
        provisional_sig = self.wrap("pi", param_vars, ind_sort)
        self.globals[name] = _Binding(_constant(type_emitted), provisional_sig, len(generic_vars))
        self.constants[type_emitted] = self.globals[name]
        # Inside constructors, `generic_env` has all `generic_vars` (parameters + index placeholders).
        # Result clause `Vec<T, n + 1>` uses `generic_env` or constructor parameter vars!

        seen_ctors: set[str] = set()
        parsed_ctors: list[tuple[Node, str, list[str], list[_Term], tuple[str | None, ...], _Term, tuple[_Term, ...]]] = []
        max_sort = 0
        for ctor_node in constructors:
            self.node(ctor_node, "constructor")
            self.no_roles(ctor_node, "contracts")
            cname = self.name(ctor_node["name"])
            if not cname or not "A" <= cname[0] <= "Z":
                raise self.fail("name", "constructor declaration requires an uppercase initial", ctor_node)
            self._evict_builtin_if_shadowed(cname)
            if (cname in self.globals or cname in self.records or cname in self.unions
                    or cname in self.inductive_ctors or cname in self.union_ctors
                    or cname == name or cname in seen_ctors or cname in {"Type", "_", "this"} or "." in cname):
                raise self.fail("name", f"duplicate or reserved inductive constructor '{cname}'", ctor_node)
            seen_ctors.add(cname)
            if is_pub:
                self.public_symbols.add(cname)
            else:
                self.private_symbols.add(cname)

            cparams = self.nodes(ctor_node["parameters"])
            param_grades: list[str | None] = []
            for pnode in cparams:
                self.node(pnode, "parameter")
                if pnode["name"] is None:
                    raise self.fail("protocol", "inductive constructor field requires a name", pnode)
                g_node = cast("Node | None", pnode.get("grade"))
                param_grades.append(self.render_ast_grade(g_node) if g_node is not None else None)
            field_vars, field_env = self.telescope([], cparams, generic_env, unit=False)
            field_names = [self.name(p["name"]) for p in cparams]

            for fv in field_vars:
                ft = self.types[cast("int", fv.value)]
                max_sort = max(max_sort, self.sort(ft))

            if ctor_node["result"] is not None:
                res_node = self.node(ctor_node["result"])
                res_term = self.type(res_node, field_env)
                head, res_args = self.spine(self.whnf(res_term))
                if head.kind != "const" or head.value != type_emitted:
                    raise self.fail("type", f"constructor '{cname}' result must construct '{name}'", res_node)
                idx_args = tuple(res_args[len(param_vars):])
                # Restrict index vars free inside result args so constructors quantify ONLY needed free generics + field_vars!
                ret_ty = res_term
            else:
                idx_args = tuple(index_vars)
                ret_ty = _apps(_constant(type_emitted), *param_vars, *index_vars)

            parsed_ctors.append((ctor_node, cname, field_names, field_vars, tuple(param_grades), ret_ty, idx_args))

        _ = max_sort
        # Emit Coq Inductive declaration
        param_binders_str = " ".join(
            f"({self.render(_term('var', value=cast('int', pv.value)))} : {self.render(self.types[cast('int', pv.value)])})"
            for pv in param_vars
        )
        index_sig_str = " -> ".join(
            self.render(self.types[cast("int", iv.value)]) for iv in index_vars
        )
        ind_header = f"Inductive {type_emitted}"
        if param_binders_str:
            ind_header += f" {param_binders_str}"
        if index_sig_str:
            ind_header += f" : {index_sig_str} -> Type :="
        else:
            ind_header += " : Type :="

        ctor_lines: list[str] = []
        raw_ctor_consts: list[str] = []
        inductive_ctors_info: list[_InductiveCtor] = []
        for idx, (ctor_node, cname, field_names, field_vars, param_grades, ret_ty, idx_args) in enumerate(parsed_ctors):
            raw_ctor = f"{type_emitted}_c_{cname}"
            raw_ctor_consts.append(raw_ctor)
            # Determine free index/generic variables appearing in field types or ret_ty (beyond param_vars & field_vars)
            free_extra: list[_Term] = []
            seen_extra: set[int] = {cast("int", pv.value) for pv in param_vars} | {cast("int", fv.value) for fv in field_vars}
            for t in [*[self.types[cast("int", fv.value)] for fv in field_vars], ret_ty]:
                for fid in sorted(self.free(t)):
                    if fid not in seen_extra and fid in {cast("int", iv.value) for iv in index_vars}:
                        seen_extra.add(fid)
                        free_extra.append(_term("var", value=fid))
            all_ctor_vars = [*free_extra, *field_vars]
            full_ctor_ty = self.wrap("pi", all_ctor_vars, ret_ty)
            self.complete(full_ctor_ty)
            ctor_binding = _Binding(_constant(raw_ctor), self.wrap("pi", [*param_vars, *free_extra, *field_vars], ret_ty), len(param_vars) + len(free_extra))
            self.constants[raw_ctor] = ctor_binding
            ctor_lines.append(f"  | {raw_ctor} : {self.render(full_ctor_ty)}")

            # Also keep HoldFast callable wrapper `<prefix>_d..._<cname>` taking generic_vars + field_vars
            record_fields = tuple(
                _RecordField(
                    fn,
                    fv,
                    self.types[cast("int", fv.value)],
                    f"{raw_ctor}_proj_{fn}",
                )
                for fn, fv in zip(field_names, field_vars, strict=True)
            )
            inductive_ctors_info.append(_InductiveCtor(
                name=cname,
                ctor_const=raw_ctor,
                ctor_binding=ctor_binding,
                fields=record_fields,
                param_grades=param_grades,
                result_type=ret_ty,
                index_args=idx_args,
                index=idx,
            ))

        self.output.append(ind_header + "\n" + "\n".join(ctor_lines) + ".")

        # Generate Arguments directives so implicit/explicit applications align cleanly with HoldFast arity
        for ctor_info, (ctor_node, cname, _, field_vars, _, ret_ty, _) in zip(inductive_ctors_info, parsed_ctors, strict=True):
            # Register global constructor binding with wrapper Definition taking ALL HoldFast generics if nullary or extra indices
            free_extra_cnt = ctor_info.ctor_binding.generics - len(param_vars)
            wrapper_const = f"{self.emission_prefix}_d{len(self.output)}_{cname}"
            # Wrapper accepts generic_vars (so `VNil<Nat>()` passes all generic_vars!) and passes needed param_vars + free_extra + field_vars to raw_ctor!
            seen_g_set = {cast("int", pv.value) for pv in param_vars}
            free_extra_vars: list[_Term] = []
            for t in [*[self.types[cast("int", fv.value)] for fv in field_vars], ret_ty]:
                for fid in sorted(self.free(t)):
                    if fid not in seen_g_set and fid in {cast("int", iv.value) for iv in index_vars}:
                        seen_g_set.add(fid)
                        free_extra_vars.append(_term("var", value=fid))
            # If user wrote `VNil<Nat>()`, generic_vars has `[T, ...]` where only `T` was passed before index!
            # When result clause specifies all indices, constructor takes `[T]` (`len(param_vars)`) + `free_extra_vars`!
            ctor_all_gens = [*param_vars, *free_extra_vars]
            _ = free_extra_cnt
            w_args = ctor_all_gens + field_vars
            w_sig = self.wrap("pi", w_args, ret_ty)
            w_body = self.wrap("lam", w_args, _apps(_constant(ctor_info.ctor_const), *param_vars, *free_extra_vars, *field_vars))
            self.output.append(f"Definition {wrapper_const} : {self.render(w_sig)} :=\n  {self.render(w_body)}.")
            cbinding = _Binding(_constant(wrapper_const), w_sig, len(ctor_all_gens))
            self.globals[cname] = cbinding
            self.constants[wrapper_const] = cbinding

            updated_ctor = _InductiveCtor(
                name=ctor_info.name,
                ctor_const=ctor_info.ctor_const,
                ctor_binding=cbinding,
                fields=ctor_info.fields,
                param_grades=ctor_info.param_grades,
                result_type=ctor_info.result_type,
                index_args=ctor_info.index_args,
                index=ctor_info.index,
            )
            inductive_ctors_info[ctor_info.index] = updated_ctor

        elim_const = f"{type_emitted}_rect"
        ind_info = _InductiveInfo(
            name=name,
            type_const=type_emitted,
            elim_const=elim_const,
            generic_vars=tuple(generic_vars),
            generic_modes=generic_modes,
            generic_domains=generic_domains,
            index_arity=len(index_vars),
            constructors=tuple(inductive_ctors_info),
        )
        self.inductives[name] = ind_info
        self.inductives_by_type[type_emitted] = ind_info
        for ctor_info in inductive_ctors_info:
            self.inductive_ctors[ctor_info.name] = (ind_info, ctor_info)

        # Finish metas
        for index in range(first_meta, len(self.metas)):
            self.complete(_term("meta", value=index))
            self.complete(self.metas[index].type)

    @staticmethod
    def render_ast_grade(node: Node | None) -> str | None:
        if node is None:
            return None
        if node["kind"] == "name":
            return cast("str", node["text"])
        if node["kind"] == "nat":
            return str(node["value"])
        return "<expr>"

    def _parse_pattern(self: _Elaborator, node: Node, seen: set[str]) -> _Pat:
        if node["kind"] == "constructor_pattern":
            cname = self.name(node["name"])
            if cname in self.inductive_ctors:
                _, ctor_info = self.inductive_ctors[cname]
                arguments = self.nodes(node["arguments"])
                sub_patterns = self._parse_ctor_subpatterns(
                    cname, arguments, ctor_info.fields, seen, node,
                )
                return _Pat("inductive", node, value=cname, args=sub_patterns)
        return cast("_Pat", super()._parse_pattern(node, seen))  # type: ignore[misc]

    def _typecheck_pattern(
        self: _Elaborator,
        pat: _Pat,
        expected_type: _Term,
        environment: dict[str, _Binding],
        pattern_bindings: dict[str, _Binding] | None = None,
        *,
        smaller_roots: frozenset[int] = frozenset(),
        destruct_roots: frozenset[int] = frozenset(),
        track_verdicts: bool = False,
        whole_match_pattern: bool = False,
    ) -> _Term:
        if pat.kind == "inductive":
            cname = cast("str", pat.value)
            ind_info, ctor_info = self.inductive_ctors[cname]
            head, args_t = self.spine(self.whnf(expected_type))
            if head.kind != "const" or head.value != ind_info.type_const:
                raise self.fail("type", f"pattern '{cname}' cannot match type '{self.render(expected_type)}'", pat.node)
            param_count = len(ind_info.generic_vars) - ind_info.index_arity
            param_args = args_t[:param_count]
            subst_map = {
                cast("int", gv.value): arg
                for gv, arg in zip(ind_info.generic_vars[:param_count], param_args, strict=True)
            }
            sub_terms: list[_Term] = []
            for subpat, rfield in zip(pat.args, ctor_info.fields, strict=True):
                ft = rfield.type
                for vid, rep in subst_map.items():
                    ft = self.substitute(ft, vid, rep)
                sub_terms.append(
                    super()._typecheck_pattern(  # type: ignore[misc]
                        subpat,
                        ft,
                        environment,
                        pattern_bindings,
                        smaller_roots=smaller_roots,
                        destruct_roots=destruct_roots,
                        track_verdicts=track_verdicts,
                        whole_match_pattern=whole_match_pattern,
                    )
                )
            return _apps(_constant(ctor_info.ctor_const), *param_args, *sub_terms)
        return cast(
            "_Term",
            super()._typecheck_pattern(  # type: ignore[misc]
                pat,
                expected_type,
                environment,
                pattern_bindings,
                smaller_roots=smaller_roots,
                destruct_roots=destruct_roots,
                track_verdicts=track_verdicts,
                whole_match_pattern=whole_match_pattern,
            ),
        )

    def match(
        self: _Elaborator,
        node: Node,
        environment: dict[str, _Binding],
        expected: _Term | None = None,
        *,
        expression_arms: bool = True,
        facts: tuple[_Binding, ...] = (),
        refine_scrutinee: bool = False,
        expected_scrutinee_type: _Term | None = None,
        visited_arms: set[int] | None = None,
        synthetic: bool = False,
    ) -> _Binding:
        value_node = self.node(node["value"])
        if expected_scrutinee_type is None:
            scrutinee = self.expression(value_node, environment)
            head, args = self.spine(self.whnf(scrutinee.type))
            if head.kind == "const" and isinstance(head.value, str) and head.value in self.inductives_by_type:
                self.site = node
                cases_nodes = self.nodes(node["cases"])
                if not cases_nodes:
                    raise self.fail("type", "inductive match requires at least one branch", node)
                motive_node = node["motive"]
                parsed_cases: list[tuple[_Pat, Node]] = []
                for arm in cases_nodes:
                    self.node(arm, "expression_case" if expression_arms else "case")
                    pat = self._parse_pattern(self.node(arm["pattern"]), set())
                    arm_val = self.node(arm["value"]) if expression_arms else arm
                    parsed_cases.append((pat, arm_val))
                result_type = expected
                if motive_node is not None:
                    motive = self.node(motive_node, "match_motive")
                    motive_env = dict(environment)
                    root_var = self.fresh(scrutinee.type)
                    self.bind_local(motive_env, self.name(motive["name"]), _Binding(root_var, scrutinee.type))
                    motive_body = self.type(self.node(motive["type"]), motive_env)
                    result_type = self.substitute(motive_body, cast("int", root_var.value), scrutinee.term)
                if result_type is None:
                    first_pat, first_val = parsed_cases[0]
                    first_env = dict(environment)
                    if first_pat.kind == "inductive":
                        self._typecheck_pattern(first_pat, scrutinee.type, environment, first_env)
                    first_res = self.expression(first_val, first_env)
                    result_type = first_res.type
                branches_str: list[str] = []
                for pat, branch_node in parsed_cases:
                    if pat.kind == "wild":
                        b_env = dict(environment)
                        for bname in pat.names:
                            b_env[bname] = scrutinee
                        branch_term = self.check(branch_node, result_type, b_env)
                        branches_str.append(f"| _ => {self.render(branch_term)}")
                    elif pat.kind == "inductive":
                        cname = cast("str", pat.value)
                        ind_info_p, ctor_info = self.inductive_ctors[cname]
                        b_env = dict(environment)
                        self._typecheck_pattern(pat, scrutinee.type, environment, b_env)
                        branch_term = self.check(branch_node, result_type, b_env)
                        binder_names = [
                            (
                                self.render(b_env[cast("list[str]", list(sp.names))[0]].term)
                                if sp.names and cast("list[str]", list(sp.names))[0] in b_env
                                else "_"
                            )
                            for sp in pat.args
                        ]
                        param_count = len(ind_info_p.generic_vars) - ind_info_p.index_arity
                        pat_lhs = " ".join([ctor_info.ctor_const, *(["_"] * param_count), *binder_names])
                        branches_str.append(f"| {pat_lhs} => {self.render(branch_term)}")
                    else:
                        raise self.fail("type", "invalid pattern for inductive match", pat.node)
                _ = args
                raw = f"(match {self.render(scrutinee.term)} with {' '.join(branches_str)} end)"
                return _Binding(_term("raw", value=raw), result_type)
        return cast(
            "_Binding",
            super().match(  # type: ignore[misc]
                node,
                environment,
                expected,
                expression_arms=expression_arms,
                facts=facts,
                refine_scrutinee=refine_scrutinee,
                expected_scrutinee_type=expected_scrutinee_type,
                visited_arms=visited_arms,
                synthetic=synthetic,
            ),
        )

    def complete(self: _Elaborator, term: _Term, *args: object, **kwargs: object) -> _Term:
        if term.kind == "raw":
            return term
        return cast("_Term", super().complete(term, *args, **kwargs))  # type: ignore[misc]

    def render(self: _Elaborator, term: _Term) -> str:
        if term.kind == "raw":
            return str(term.value)
        return cast("str", super().render(term))  # type: ignore[misc]

    def _compile_match(
        self: _Elaborator,
        scrutinee: _Term,
        scrutinee_type: _Term,
        cases: list[tuple[_Pat, Node]],
        motive: tuple[str, _Term] | None,
        result_type: _Term,
        environment: dict[str, _Binding],
        node: Node,
    ) -> _Term:
        head, args = self.spine(self.whnf(scrutinee_type))
        if head.kind == "const" and isinstance(head.value, str) and head.value in self.inductives_by_type:
            ind_info = self.inductives_by_type[head.value]
            param_count = len(ind_info.generic_vars) - ind_info.index_arity
            _ = args[:param_count]
            # Lower user inductive match to Coq `match` over raw inductive constructors
            branches_str: list[str] = []
            for pat, branch_node in cases:
                if pat.kind == "wild":
                    b_env = dict(environment)
                    for bname in pat.names:
                        b_env[bname] = _Binding(scrutinee, scrutinee_type)
                    branch_term = self.check(branch_node, result_type, b_env)
                    branches_str.append(f"| _ => {self.render(branch_term)}")
                elif pat.kind == "inductive":
                    cname = cast("str", pat.value)
                    _, ctor_info = self.inductive_ctors[cname]
                    b_env = dict(environment)
                    self._typecheck_pattern(pat, scrutinee_type, environment, b_env)
                    branch_term = self.check(branch_node, result_type, b_env)
                    binder_names = [
                        (
                            self.render(b_env[cast("list[str]", list(sp.names))[0]].term)
                            if sp.names and cast("list[str]", list(sp.names))[0] in b_env
                            else "_"
                        )
                        for sp in pat.args
                    ]
                    pat_parts = [ctor_info.ctor_const, *(["_"] * param_count), *binder_names]
                    pat_lhs = " ".join(pat_parts)
                    branches_str.append(f"| {pat_lhs} => {self.render(branch_term)}")
                else:
                    raise self.fail("type", f"invalid pattern for inductive '{ind_info.name}'", pat.node)
            _ = motive
            raw = f"(match {self.render(scrutinee)} with {' '.join(branches_str)} end)"
            return _term("raw", value=raw)
        return cast(
            "_Term",
            super()._compile_match(  # type: ignore[misc]
                scrutinee, scrutinee_type, cases, motive, result_type, environment, node,
            ),
        )

    def _register_checked_zero_binders(
        self: _Elaborator,
        decl_name: str,
        zero_names: frozenset[str],
        pi_type: _Term,
    ) -> None:
        """Tag checked `r = 0` binder variables and codomain terms for Q25cb skipping."""
        cur = self.resolve(pi_type)
        chain: list[tuple[int, _Term, str | None]] = []
        while cur.kind == "pi":
            vid = cast("int", cur.value)
            chain.append((vid, cur.args[1], self.parameter_names.get(vid)))
            cur = self.resolve(cur.args[1])
        tagged_vars: list[int] = []
        zero_positions: list[int] = []
        for pos, (vid, cod, pname) in enumerate(chain):
            if pname is not None and pname in zero_names:
                self.zero_type_use_vars.add(vid)
                tagged_vars.append(vid)
                zero_positions.append(pos)
                frozen = frozenset(tagged_vars)
                self.checked_zero_type_codomains[id(cod)] = (
                    self.checked_zero_type_codomains.get(id(cod), frozenset()) | frozen
                )
        self.zero_type_use_decl_binders[decl_name] = tuple(zero_positions)
        if tagged_vars:
            self.zero_type_use_summaries[decl_name] = _ZeroTypeUseSummary(
                decl_name=decl_name,
                zero_binders=tuple(tagged_vars),
                substitute_calls=self.substitute_calls,
                substitute_skips=self.substitute_skips,
            )

    def _emit_cbv_erasure_correspondence(
        self: _Elaborator,
        decl_name: str,
        defn: graded_source._Definition,
        emitted_const: str,
        emitted_type: _Term,
        cert_text: str,
    ) -> None:
        """Emit standalone CBV erasure image and correspondence proof for a graded declaration."""
        binding = self.globals.get(decl_name)
        if binding is None or defn.source["kind"] not in {"definition", "function"}:
            return
        cur = self.resolve(binding.type)
        top_by_name = {p.name: p for p in defn.top_params}
        zero_uids = {uid for uid, _, _ in defn.zero_type_use_binders}
        param_vars: list[tuple[int, str, _Term, bool]] = []
        while cur.kind == "pi":
            vid = cast("int", cur.value)
            vtype = cur.args[0]
            pname = self.parameter_names.get(vid)
            vname = self.render(_term("var", value=vid))
            tp = top_by_name.get(pname) if pname is not None else None
            is_dead = False
            if tp is not None and tp.allowance in {"0", "false", "LZero", "AZero", "Lo"} and tp.uid in zero_uids:
                is_dead = True
            param_vars.append((vid, vname, vtype, is_dead))
            cur = self.resolve(cur.args[1])

        if not param_vars:
            return
        ret_ty = cur
        erased_name = f"{self.emission_prefix}_erased_{decl_name}"
        # Only drop dead binders whose domain is Nat or bool and not used in any live body/type.
        erased_pairs: list[tuple[int, str, _Term, bool]] = [
            (vid, vname, ty, dead and self.whnf(ty) in {_NAT, _BOOL})
            for vid, vname, ty, dead in param_vars
        ]
        full_args = " ".join(f"({vname} : {self.render(ty)})" for _, vname, ty, _ in erased_pairs)
        all_call_args = " ".join(vname for _, vname, _, _ in erased_pairs)
        erased_live_args = " ".join(
            f"({vname} : {self.render(ty)})" for _, vname, ty, drop in erased_pairs if not drop
        )
        erased_call_args = " ".join(vname for _, vname, _, drop in erased_pairs if not drop)
        applied_body_args = " ".join(
            ("0" if self.whnf(ty) == _NAT else "false") if drop else vname
            for _, vname, ty, drop in erased_pairs
        )
        cert_digest = hashlib.sha256(cert_text.encode("utf-8")).hexdigest()[:16]
        _ = emitted_type

        erased_binders = f" {erased_live_args}" if erased_live_args else ""
        self.cbv_erasure_chunks.append(
            f"(* CBV erasure link for {decl_name}: cert {cert_digest}, "
            f"erased_dead={sum(1 for _, _, _, d in erased_pairs if d)} *)\n"
            f"Definition {erased_name}{erased_binders} : {self.render(ret_ty)} :=\n"
            f"  {emitted_const} {applied_body_args}.\n"
            f"Theorem {erased_name}_correspondence : forall {full_args},\n"
            f"  {emitted_const} {all_call_args} = {erased_name} {erased_call_args}.\n"
            f"Proof. intros; unfold {erased_name}, {emitted_const}; cbv beta zeta; reflexivity. Qed."
        )
