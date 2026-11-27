# SPDX-License-Identifier: Apache-2.0
"""Pattern parsing, dependent pattern typing, and exhaustive match compilation for HoldFast elaboration."""

from collections.abc import Callable
from functools import partial
from typing import TYPE_CHECKING, Literal, cast

from toolchain.elaborate_flow_lints import branch as lint_branch
from toolchain.elaborate_flow_lints import forwards_case, observe
from toolchain.elaborate_types import (
    _BOOL,
    _CHAR,
    _NAT,
    _NUMERICS_ALIASES,
    _SORT,
    _U8,
    _UNIT,
    _USIZE,
    MAX_PATTERN_NAT,
    Node,
    _app,
    _apps,
    _Binding,
    _constant,
    _IndexedBorrowPeer,
    _IndexedLocalBorrow,
    _int_term,
    _parse_numeric_magnitude,
    _Pat,
    _RecordField,
    _RecordInfo,
    _Row,
    _Term,
    _term,
    _UnionCtor,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


class _PatternsMixin:
    def _pattern_names(self: _Elaborator, pattern: Node) -> frozenset[str]:
        if pattern["kind"] == "binding_pattern":
            return frozenset({self.name(pattern["name"])})
        names: set[str] = set()
        for key in ("pattern", "arguments", "elements", "patterns"):
            inner = pattern.get(key)
            if isinstance(inner, dict):
                names.update(self._pattern_names(self.node(inner)))
            elif isinstance(inner, list):
                for child in self.nodes(inner):
                    names.update(self._pattern_names(child))
        return frozenset(names)

    def _parse_pattern(self: _Elaborator, node: Node, seen: set[str]) -> _Pat:
        self.tick()
        self.site = node
        kind = node["kind"]
        if kind == "wildcard_pattern":
            return _Pat("wild", node)
        if kind == "binding_pattern":
            name = self.name(node["name"])
            if not name or "." in name or name == "_" or ("A" <= name[0] <= "Z") or name in seen:
                raise self.fail("name", f"duplicate or invalid pattern binding '{name}'", node)
            seen.add(name)
            return _Pat("wild", node, names=(name,))
        if kind == "group_pattern":
            return self._parse_pattern(self.node(node["pattern"]), seen)
        if kind == "unit_pattern":
            return _Pat("unit", node)
        if kind == "bool_pattern":
            return _Pat("bool", node, value=cast("bool", node["value"]))
        if kind == "character_pattern":
            cp = self._decode_char_literal(cast("str", node["value"]), node)
            return _Pat("char", node, value=cp)
        if kind == "string_pattern":
            raw_bytes = self._decode_string_literal(cast("str", node["value"]), node)
            return _Pat("string", node, value=raw_bytes.decode("latin1"))
        if kind == "tuple_pattern":
            items = [self._parse_pattern(item, seen) for item in self.nodes(node["patterns"])]
            if len(items) < 2:
                raise self.fail("protocol", "a tuple pattern requires at least two components", node)
            result = items[-1]
            for item in reversed(items[:-1]):
                result = _Pat("pair", node, args=(item, result))
            return result
        if kind == "nat_pattern":
            amount = _parse_numeric_magnitude(cast("str", node["value"]))
            suffix = cast("str", node["suffix"])
            if suffix or amount > MAX_PATTERN_NAT:
                return _Pat("int_lit", node, value=f"{amount}:{suffix}")
            result = _Pat("zero", node, value=f"{amount}:")
            for _ in range(amount):
                result = _Pat("succ", node, value=f"{amount}:", args=(result,))
            return result
        if kind == "constructor_pattern":
            cname = self.name(node["name"])
            short_cname = cname.rsplit(".", 1)[-1]
            if not short_cname or not ("A" <= short_cname[0] <= "Z"):
                raise self.fail(
                    "name",
                    f"constructor pattern '{cname}' requires an uppercase constructor name",
                    node,
                )
            arguments = self.nodes(node["arguments"])
            if cname == "Succ":
                if len(arguments) != 1:
                    raise self.fail("type", "constructor 'Succ' expects 1 pattern argument", node)
                if arguments[0]["kind"] == "labeled_pattern":
                    raise self.fail("name", "constructor 'Succ' does not accept labeled pattern arguments", arguments[0])
                return _Pat("succ", node, args=(self._parse_pattern(arguments[0], seen),))
            if cname in self.records:
                sub_patterns = self._parse_ctor_subpatterns(
                    cname, arguments, self.records[cname].fields, seen, node
                )
                return _Pat("record", node, value=cname, args=sub_patterns)
            if cname in self.union_ctors:
                _, ctor_info = self.union_ctors[cname]
                sub_patterns = self._parse_ctor_subpatterns(
                    cname, arguments, ctor_info.fields, seen, node
                )
                return _Pat("union", node, value=cname, args=sub_patterns)
            if cname not in self.globals:
                raise self.fail(
                    "name",
                    f"unknown constructor '{cname}' (pattern binders must start with a lowercase letter or '_')",
                    node,
                )
            if cname in {"VNil", "VCons", "FZero", "FSucc"}:
                raise self.fail("unsupported", f"indexed elimination over '{cname}' requires the full frontend", node)
            raise self.fail(
                "type",
                f"'{cname}' is not a pattern constructor (pattern binders must start with a lowercase letter or '_')",
                node,
            )
        raise self.fail("protocol", f"unexpected pattern node '{kind}'", node)

    def _pattern_covers(self: _Elaborator, earlier: _Pat, later: _Pat) -> bool:
        self.tick()
        if earlier.kind == "wild":
            return True
        if earlier.kind != later.kind or len(earlier.args) != len(later.args):
            return False
        if earlier.kind == "union":
            if self.union_ctors[cast("str", earlier.value)][1].ctor_const != self.union_ctors[cast("str", later.value)][1].ctor_const:
                return False
        elif earlier.kind == "record":
            if self.records[cast("str", earlier.value)].type_const != self.records[cast("str", later.value)].type_const:
                return False
        elif earlier.kind not in {"succ", "zero"} and earlier.value != later.value:
            return False
        return all(self._pattern_covers(left, right) for left, right in zip(earlier.args, later.args, strict=True))

    def _parse_ctor_subpatterns(
        self: _Elaborator,
        cname: str,
        arguments: list[Node],
        fields: tuple[_RecordField, ...],
        seen: set[str],
        node: Node,
    ) -> tuple[_Pat, ...]:
        if len(arguments) != len(fields):
            raise self.fail(
                "type",
                f"constructor '{cname}' expects {len(fields)} pattern arguments, got {len(arguments)}",
                node,
            )
        labeled = False
        sub_patterns: list[_Pat] = []
        for idx, arg_node in enumerate(arguments):
            expected_field = fields[idx]
            if arg_node["kind"] == "labeled_pattern":
                labeled = True
                spelling = self.name(arg_node["label"])
                if spelling != expected_field.name:
                    raise self.fail(
                        "name",
                        f"expected pattern field label '{expected_field.name}', got '{spelling}'",
                        arg_node,
                    )
                sub_patterns.append(self._parse_pattern(self.node(arg_node["pattern"]), seen))
            else:
                if labeled:
                    raise self.fail(
                        "name",
                        "positional pattern arguments cannot follow a labeled pattern argument",
                        arg_node,
                    )
                sub_patterns.append(self._parse_pattern(arg_node, seen))
        return tuple(sub_patterns)

    def _instantiate_generic_type(
        self: _Elaborator, generic_vars: tuple[_Term, ...], type_args: list[_Term], target_type: _Term
    ) -> _Term:
        result = target_type
        for gv, arg in zip(generic_vars, type_args, strict=True):
            result = self.substitute(result, cast("int", gv.value), arg)
        return result

    def _instantiate_record_type(
        self: _Elaborator, record_info: _RecordInfo, type_args: list[_Term], target_type: _Term
    ) -> _Term:
        return self._instantiate_generic_type(record_info.generic_vars, type_args, target_type)

    def _instantiate_record_field_type(
        self: _Elaborator, record_info: _RecordInfo, type_args: list[_Term], field_idx: int, receiver_term: _Term
    ) -> _Term:
        ftype = self._instantiate_record_type(record_info, type_args, record_info.fields[field_idx].type)
        for j in range(field_idx):
            earlier_rf = record_info.fields[j]
            proj_term = _apps(_constant(earlier_rf.proj_const), *type_args, receiver_term)
            ftype = self.substitute(ftype, cast("int", earlier_rf.var.value), proj_term)
        return ftype

    def _expand_union_ctor(self: _Elaborator, term: _Term) -> _Term:
        head, args = self.spine(term)
        if head.kind != "const" or not isinstance(head.value, str) or head.value not in self.unions_by_ctor:
            return term
        union_info, ctor_info = self.unions_by_ctor[head.value]
        expected_val_arity = len(ctor_info.fields) if ctor_info.fields else 1
        if len(args) != len(union_info.generic_vars) + expected_val_arity:
            return term
        type_args = args[:len(union_info.generic_vars)]
        field_vals = args[len(union_info.generic_vars):]
        field_types = [
            self._instantiate_generic_type(union_info.generic_vars, type_args, rf.type)
            for rf in ctor_info.fields
        ]
        if not ctor_info.fields:
            payload_val = _term("unit")
        elif len(ctor_info.fields) == 1:
            if len(union_info.constructors) == 1:
                payload_val = _term("pair", field_types[0], _UNIT, field_vals[0], _term("unit"))
            else:
                payload_val = field_vals[0]
        elif ctor_info.is_dependent:
            payload_val = field_vals[-1]
            for k in range(len(field_vals) - 2, -1, -1):
                fv = field_vals[k]
                fvar_id = cast("int", ctor_info.fields[k].var.value)
                ftype = field_types[k]
                tail_type = self._instantiate_generic_type(
                    union_info.generic_vars, type_args, ctor_info.tail_sig_types[k + 1]
                )
                for j in range(k):
                    earlier_id = cast("int", ctor_info.fields[j].var.value)
                    ftype = self.substitute(ftype, earlier_id, field_vals[j])
                    tail_type = self.substitute(tail_type, earlier_id, field_vals[j])
                fam_lam = _term("lam", ftype, tail_type, value=fvar_id)
                payload_val = _term("existT", ftype, fam_lam, fv, payload_val)
        else:
            payload_val = field_vals[-1]
            acc_type = field_types[-1]
            for fv, ft in reversed(list(zip(field_vals[:-1], field_types[:-1], strict=True))):
                payload_val = _term("pair", ft, acc_type, fv, payload_val)
                acc_type = _term("prod", ft, acc_type)
        if len(union_info.constructors) == 1:
            return payload_val
        inst_payload_types = [
            self._instantiate_generic_type(union_info.generic_vars, type_args, c.payload_type)
            for c in union_info.constructors
        ]
        inst_suffix_types = [
            self._instantiate_generic_type(union_info.generic_vars, type_args, st)
            for st in union_info.suffix_types
        ]
        idx = ctor_info.index
        if idx < len(union_info.constructors) - 1:
            result = _term("inl", inst_payload_types[idx], inst_suffix_types[idx + 1], payload_val)
        else:
            result = payload_val
        for j in range(idx - 1, -1, -1):
            result = _term("inr", inst_payload_types[j], inst_suffix_types[j + 1], result)
        return result

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
        self.tick()
        self.site = pat.node
        bound_var: _Term | None = None
        if pattern_bindings is not None:
            for name in pat.names:
                fresh_v = self.fresh(expected_type)
                for r_id in smaller_roots:
                    if r_id in self.smaller_vars:
                        self.smaller_vars[r_id].add(cast("int", fresh_v.value))
                pattern_bindings[name] = _Binding(fresh_v, expected_type)
                if bound_var is None:
                    bound_var = fresh_v
        if pat.kind == "wild":
            if pat.names and pat.node["kind"] == "binding_pattern":
                binder = pat.names[0]
                expected_head, _ = self.spine(self.whnf(expected_type))
                for spelling, (owner, constructor) in self.union_ctors.items():
                    if (_constant(owner.type_const) == expected_head
                            and spelling.rsplit(".", 1)[-1] == binder[:1].upper() + binder[1:]):
                        if whole_match_pattern:
                            suggested = spelling + ("(...)" if constructor.fields else "")
                            raise self.fail(
                                "type", f"'{binder}' binds every value of the scrutinee. Use '{suggested}' "
                                "to match the constructor, '_' to discard, or a different binding name", pat.node,
                            )
                        start = cast("list[int]", pat.node["span"])[0]
                        self.constructor_suggestions[start] = spelling
                        break
            if track_verdicts and not pat.names and self._result_paths("", expected_type):
                raise self.fail("type", "unexamined Result in wildcard pattern", pat.node)
            if bound_var is not None:
                return bound_var
            fresh_w = self.fresh(expected_type)
            for r_id in smaller_roots:
                if r_id in self.smaller_vars:
                    self.smaller_vars[r_id].add(cast("int", fresh_w.value))
            return fresh_w
        if pat.kind == "unit":
            self.unify(expected_type, _UNIT)
            return _term("unit")
        if pat.kind == "bool":
            self.unify(expected_type, _BOOL)
            return _term("bool", value=1 if pat.value else 0)
        if pat.kind == "char":
            self.unify(expected_type, _CHAR)
            return _term("char", value=cast("int", pat.value))
        if pat.kind == "string":
            str_b = self._bytes_binding(cast("str", pat.value).encode("latin1"))
            self.unify(expected_type, str_b.type)
            return str_b.term
        spec = self._int_spec(expected_type)
        if spec is not None and pat.kind in {"zero", "succ", "int_lit"}:
            if pat.node["kind"] != "nat_pattern":
                raise self.fail("type", "constructor 'Succ' requires a Nat scrutinee", pat.node)
            amount = _parse_numeric_magnitude(cast("str", pat.node["value"]))
            suffix = cast("str", pat.node["suffix"])
            if suffix:
                canonical = "u8" if suffix == "byte" else _NUMERICS_ALIASES.get(suffix, suffix)
                if canonical != spec.name:
                    raise self.fail(
                        "type",
                        f"integer pattern suffix '{suffix}' does not match scrutinee type '{spec.name}'",
                        pat.node,
                    )
            if not spec.min_val <= amount <= spec.max_val:
                raise self.fail(
                    "type",
                    f"integer pattern {amount} is out of range for '{spec.name}' ({spec.min_val}..{spec.max_val})",
                    pat.node,
                )
            return _int_term(spec, amount)
        if pat.kind == "int_lit":
            self.unify(expected_type, _NAT)
            _, suffix = cast("str", pat.value).split(":", 1)
            if suffix:
                raise self.fail(
                    "type",
                    f"integer pattern with suffix '{suffix}' requires type '{suffix}', not Nat",
                    pat.node,
                )
            raise self.fail(
                "limit",
                f"natural pattern literal exceeds structural bound ({MAX_PATTERN_NAT})",
                pat.node,
            )
        if pat.kind in {"zero", "succ"}:
            self.unify(expected_type, _NAT)
            if pat.kind == "zero":
                return _term("nat", value=0)
            pred_term = self._typecheck_pattern(
                pat.args[0],
                _NAT,
                environment,
                pattern_bindings,
                smaller_roots=smaller_roots | destruct_roots,
                destruct_roots=destruct_roots,
            )
            return _app(_constant("Succ"), pred_term)
        if pat.kind == "record":
            record_info = self.records[cast("str", pat.value)]
            type_args = [self.meta(self.types[cast("int", gv.value)], environment) for gv in record_info.generic_vars]
            expected_rec_type = _apps(_constant(record_info.type_const), *type_args)
            self.unify(expected_type, expected_rec_type)
            sub_terms: list[_Term] = []
            for idx, (sub_pat, rf) in enumerate(zip(pat.args, record_info.fields, strict=True)):
                ftype = self._instantiate_record_type(record_info, type_args, rf.type)
                for j in range(idx):
                    ftype = self.substitute(ftype, cast("int", record_info.fields[j].var.value), sub_terms[j])
                sub_terms.append(
                    self._typecheck_pattern(sub_pat, ftype, environment, pattern_bindings, track_verdicts=track_verdicts)
                )
            if not sub_terms:
                return _apps(_constant(record_info.ctor_const), *type_args, _term("unit"))
            return _apps(_constant(record_info.ctor_const), *type_args, *sub_terms)
        if pat.kind == "union":
            union_info, ctor_info = self.union_ctors[cast("str", pat.value)]
            type_args = [self.meta(self.types[cast("int", gv.value)], environment) for gv in union_info.generic_vars]
            expected_union_type = _apps(_constant(union_info.type_const), *type_args)
            self.unify(expected_type, expected_union_type)
            sub_terms = []
            for idx, (sub_pat, rf) in enumerate(zip(pat.args, ctor_info.fields, strict=True)):
                ftype = self._instantiate_generic_type(union_info.generic_vars, type_args, rf.type)
                for j in range(idx):
                    ftype = self.substitute(ftype, cast("int", ctor_info.fields[j].var.value), sub_terms[j])
                sub_terms.append(
                    self._typecheck_pattern(sub_pat, ftype, environment, pattern_bindings, track_verdicts=track_verdicts)
                )
            if not sub_terms:
                return _apps(_constant(ctor_info.ctor_const), *type_args, _term("unit"))
            return _apps(_constant(ctor_info.ctor_const), *type_args, *sub_terms)
        if pat.kind == "pair":
            resolved = self.whnf(expected_type)
            if resolved.kind == "meta":
                left_type = self.meta(_SORT, environment)
                right_type = self.meta(_SORT, environment)
                self.unify(resolved, _term("prod", left_type, right_type))
                resolved = self.whnf(expected_type)
            if resolved.kind != "prod":
                raise self.fail("type", "tuple pattern requires a product scrutinee", pat.node)
            left_t = self._typecheck_pattern(pat.args[0], resolved.args[0], environment, pattern_bindings, track_verdicts=track_verdicts)
            right_t = self._typecheck_pattern(pat.args[1], resolved.args[1], environment, pattern_bindings, track_verdicts=track_verdicts)
            return _term("pair", resolved.args[0], resolved.args[1], left_t, right_t)
        raise self.fail("protocol", f"unexpected internal pattern '{pat.kind}'", pat.node)

    def _require_irrefutable(self: _Elaborator, pat: _Pat) -> None:
        if pat.kind in {"bool", "zero", "succ", "int_lit", "char", "string", "union"}:
            raise self.fail("type", "local pattern binding requires an irrefutable pattern; use match", pat.node)
        for child in pat.args:
            self._require_irrefutable(child)

    def _bind_irrefutable(self: _Elaborator, pat: _Pat, current: _Binding, extended: dict[str, _Binding],
                          result_paths: set[str] | None = None) -> None:
        self.site = pat.node
        if (result_paths is not None and pat.kind == "wild" and not pat.names
                and self._result_paths("", current.type)):
            raise self.fail("type", "unexamined Result in wildcard binding", pat.node)
        for name in pat.names:
            self.bind_local(extended, name, current)
            if result_paths is not None:
                result_paths.update(self._result_paths(name, current.type))
        if pat.kind == "record":
            rec_type = self.whnf(current.type)
            _, type_args = self.spine(rec_type)
            record_info = self.records[cast("str", pat.value)]
            for idx, (sub_pat, rf) in enumerate(zip(pat.args, record_info.fields, strict=True)):
                ftype = self._instantiate_record_field_type(record_info, type_args, idx, current.term)
                fterm = _apps(_constant(rf.proj_const), *type_args, current.term)
                self._bind_irrefutable(sub_pat, _Binding(fterm, ftype), extended, result_paths)
        elif pat.kind == "pair":
            prod_type = self.whnf(current.type)
            left_type, right_type = prod_type.args
            left_term = _apps(_constant("Fst"), left_type, right_type, current.term)
            right_term = _apps(_constant("Snd"), left_type, right_type, current.term)
            self._bind_irrefutable(pat.args[0], _Binding(left_term, left_type), extended, result_paths)
            self._bind_irrefutable(pat.args[1], _Binding(right_term, right_type), extended, result_paths)

    def _collect_pat_names(self: _Elaborator, pat: _Pat, out: set[str]) -> None:
        for name in pat.names:
            out.add(name)
        for child in pat.args:
            self._collect_pat_names(child, out)

    def _project_borrow_binding(
        self: _Elaborator,
        owner_name: str,
        field_path: tuple[str, ...],
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> _Binding:
        if owner_name not in environment:
            raise self.fail("name", f"unknown identifier '{owner_name}'", site_node)
        cur = environment[owner_name]
        for fname in field_path:
            cur_ty = self.whnf(cur.type)
            head, type_args = self.spine(cur_ty)
            if (
                head.kind != "const"
                or not isinstance(head.value, str)
                or head.value not in self.records_by_type
            ):
                raise self.fail("type", f"cannot borrow field '{fname}' from non-record '{owner_name}'", site_node)
            record_info = self.records_by_type[head.value]
            field_index = next(
                (idx for idx, rf in enumerate(record_info.fields) if rf.name == fname),
                None,
            )
            if field_index is None:
                raise self.fail("name", f"record '{record_info.name}' has no field '{fname}'", site_node)
            rf = record_info.fields[field_index]
            f_type = self._instantiate_record_field_type(record_info, type_args, field_index, cur.term)
            f_term = _apps(_constant(rf.proj_const), *type_args, cur.term)
            cur = _Binding(f_term, f_type)
        return cur

    def _refresh_local_borrows(
        self: _Elaborator, environment: dict[str, _Binding], site_node: Node
    ) -> None:
        for bname, (_mode, owner_name, field_path) in list(self.local_borrows.items()):
            if bname in environment and owner_name in environment:
                environment[bname] = self._project_borrow_binding(
                    owner_name, field_path, environment, site_node
                )

    def _resolve_local_borrow_target(
        self: _Elaborator,
        borrow_mode: str,
        target_node: Node,
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> tuple[str, tuple[str, ...], _Binding]:
        target_node = self._unwrap_group(target_node)
        t_kind = target_node["kind"]
        if t_kind == "name":
            tname = self.name(target_node["name"])
            if tname not in environment:
                raise self.fail("name", f"unknown identifier '{tname}'", target_node)
            if tname in self.uninitialized_out_params:
                raise self.fail("type", f"cannot borrow uninitialized 'out' parameter '{tname}'", target_node)
            if tname in self.local_borrows:
                parent_mode, owner_name, field_path = self.local_borrows[tname]
                if borrow_mode == "ref" and parent_mode != "ref":
                    raise self.fail(
                        "type",
                        f"cannot take exclusive 'ref' borrow from shared '{parent_mode}' borrow '{tname}' (exclusive-from-shared)",
                        site_node,
                    )
                if borrow_mode == "shared_ref" and parent_mode == "in":
                    raise self.fail(
                        "type",
                        f"cannot take 'shared ref' borrow from shared 'in' borrow '{tname}' (exclusive-from-shared)",
                        site_node,
                    )
                self._check_path_not_moved(owner_name, field_path, target_node)
            else:
                owner_name = tname
                field_path = ()
                self._check_path_not_moved(owner_name, field_path, target_node)
                if borrow_mode in {"ref", "shared_ref"}:
                    if tname in self.readonly_in_params or self._is_readonly_span(environment[tname].term):
                        raise self.fail(
                            "type",
                            f"cannot take '{borrow_mode}' borrow of read-only 'in' parameter '{tname}'",
                            site_node,
                        )
                    if tname in self.frozen_collections:
                        raise self.fail(
                            "type",
                            f"cannot take '{borrow_mode}' borrow of frozen collection '{tname}'",
                            site_node,
                        )
                    if tname not in self.mutable_locals and tname not in self.shared_ref_locals:
                        raise self.fail(
                            "type",
                            f"cannot take exclusive 'ref' borrow of immutable binding '{tname}'; declare it with 'var' or 'ref'",
                            site_node,
                        )
        elif t_kind == "member":
            return self._resolve_nested_borrow_target(borrow_mode, target_node, environment, site_node)
        else:
            raise self.fail("type", f"'{borrow_mode}' borrow requires a variable or record field place", target_node)
        projected = self._project_borrow_binding(owner_name, field_path, environment, target_node)
        if not self._is_supported_loan_type(projected.type):
            raise self.fail("unsupported", f"loan modifier '{borrow_mode}' is not supported on this type", site_node)
        return owner_name, field_path, projected

    def _is_indexed_borrow_target(self: _Elaborator, target_node: Node) -> bool:
        cur = self._unwrap_group(target_node)
        while cur["kind"] == "member":
            cur = self._unwrap_group(self.node(cur["value"]))
        return cur["kind"] == "index"

    def _collection_kind_and_elem(
        self: _Elaborator, col_type: _Term, site_node: Node,
    ) -> tuple[Literal["vec", "seq", "span", "slots"], _Term, tuple[_Term, ...]]:
        head, targs = self.spine(self.whnf(col_type))
        if head == _constant("Vec") and len(targs) == 2:
            return "vec", targs[0], tuple(targs)
        if head == _constant("Seq") and len(targs) == 1:
            return "seq", targs[0], tuple(targs)
        if head == _constant("Span") and len(targs) == 1 and self.whnf(targs[0]) == _U8:
            return "span", _U8, tuple(targs)
        if head == _constant("Slots") and len(targs) == 2:
            return "slots", targs[0], tuple(targs)
        raise self.fail(
            "type",
            "indexed local borrow requires a Vec<T, n>, Seq<T>, Span<byte>, or Slots<T, capacity> collection",
            site_node,
        )

    def _resolve_indexed_local_borrow(
        self: _Elaborator,
        borrow_mode: Literal["in", "ref"],
        target_node: Node,
        environment: dict[str, _Binding],
        site_node: Node,
    ) -> tuple[_IndexedLocalBorrow, _Binding]:
        cur = self._unwrap_group(target_node)
        member_suffix: list[str] = []
        while cur["kind"] == "member":
            member_suffix.append(self.name(cur["name"]))
            cur = self._unwrap_group(self.node(cur["value"]))
        member_suffix.reverse()
        index_chain: list[Node] = []
        while cur["kind"] == "index":
            index_chain.append(cur)
            cur = self._unwrap_group(self.node(cur["value"]))
        index_chain.reverse()
        if not index_chain or cur["kind"] != "name":
            raise self.fail("unsupported", "indexed local borrow requires a named collection binding", cur)
        rname = self.name(cur["name"])
        if rname not in environment:
            raise self.fail("name", f"unknown identifier '{rname}'", cur)
        if rname in self.uninitialized_out_params:
            raise self.fail("type", f"cannot borrow element of uninitialized 'out' parameter '{rname}'", cur)
        if borrow_mode == "ref":
            if rname in self.readonly_in_params or self._is_readonly_span(environment[rname].term):
                raise self.fail(
                    "type",
                    f"cannot take exclusive 'ref' borrow of read-only 'in' parameter '{rname}'",
                    site_node,
                )
            if rname in self.frozen_collections:
                raise self.fail(
                    "type",
                    f"cannot take exclusive 'ref' borrow of frozen collection '{rname}'",
                    site_node,
                )
            if rname in self.local_borrows and self.local_borrows[rname][0] != "ref":
                raise self.fail(
                    "type",
                    f"cannot take exclusive 'ref' borrow from shared 'in' borrow '{rname}' (exclusive-from-shared)",
                    site_node,
                )
            if rname in self.indexed_local_borrows and self.indexed_local_borrows[rname].mode != "ref":
                raise self.fail(
                    "type",
                    f"cannot take exclusive 'ref' borrow from shared 'in' borrow '{rname}' (exclusive-from-shared)",
                    site_node,
                )
            if rname not in self.mutable_locals:
                raise self.fail(
                    "type",
                    f"cannot take exclusive 'ref' borrow of immutable binding '{rname}'; declare it with 'var' or 'ref'",
                    site_node,
                )
        collection = environment[rname]
        collection_kind, elem_type, targs = self._collection_kind_and_elem(collection.type, index_chain[0])
        if borrow_mode == "ref":
            if collection_kind == "span":
                self._check_span_can_write(collection.term, environment, index_chain[0])
            elif collection_kind == "slots" and not self._prove_bool_precondition(
                _apps(_constant("Slots_CanWrite"), *targs, collection.term), environment
            ):
                raise self.fail("type", "indexed local 'ref' borrow requires Slots.CanWrite", index_chain[0])
        element, index = self._read_indexed_place(index_chain[0], environment, check_view=True)
        if index.type not in {_NAT, _USIZE}:
            raise self.fail("unsupported", "indexed local borrow requires a Nat or usize index", index_chain[0])
        nested_levels: list[
            tuple[Literal["vec", "seq", "span", "slots"], _Term, _Term, tuple[_Term, ...], _Term]
        ] = []
        for idx_node in index_chain[1:]:
            sub_kind, sub_elem, sub_targs = self._collection_kind_and_elem(element.type, idx_node)
            if borrow_mode == "ref":
                if sub_kind == "span":
                    self._check_span_can_write(element.term, environment, idx_node)
                elif sub_kind == "slots" and not self._prove_bool_precondition(
                    _apps(_constant("Slots_CanWrite"), *sub_targs, element.term), environment
                ):
                    raise self.fail("type", "indexed local 'ref' borrow requires Slots.CanWrite", idx_node)
            sub_elem_b, sub_idx_b = self._read_indexed_place(idx_node, environment, check_view=True)
            if sub_idx_b.type not in {_NAT, _USIZE}:
                raise self.fail("unsupported", "indexed local borrow requires a Nat or usize index", idx_node)
            nested_levels.append((sub_kind, sub_idx_b.term, sub_idx_b.type, sub_targs, sub_elem))
            element = sub_elem_b
        for fname in member_suffix:
            rec_ty = self.whnf(element.type)
            r_head, _ = self.spine(rec_ty)
            if r_head.kind != "const" or not isinstance(r_head.value, str) or r_head.value not in self.records_by_type:
                raise self.fail("type", f"cannot borrow field '{fname}' from non-record indexed element", target_node)
            record_info = self.records_by_type[r_head.value]
            field_index = next((idx for idx, rf in enumerate(record_info.fields) if rf.name == fname), None)
            if field_index is None:
                raise self.fail("name", f"record '{record_info.name}' has no field '{fname}'", target_node)
            rf = record_info.fields[field_index]
            if borrow_mode == "ref":
                if cast("int", rf.var.value) in self.constant_parameters or rf.readonly_span:
                    raise self.fail("type", f"cannot take exclusive 'ref' borrow of constant or read-only field '{fname}'", target_node)
                for later_rf in record_info.fields[field_index + 1:]:
                    if cast("int", rf.var.value) in self.free(later_rf.type):
                        raise self.fail(
                            "type",
                            f"cannot take exclusive 'ref' borrow of field '{fname}' because later field '{later_rf.name}' depends on it",
                            target_node,
                        )
            element = self._project_member(element, fname, target_node, environment)
        if not self._is_supported_loan_type(element.type):
            raise self.fail("unsupported", f"loan modifier '{borrow_mode}' is not supported on this type", site_node)
        self.indexed_borrow_serial += 1
        info = _IndexedLocalBorrow(
            mode=borrow_mode,
            owner=rname,
            collection_kind=collection_kind,
            index_term=index.term,
            index_type=index.type,
            owner_term=self.whnf(environment[rname].term),
            elem_type=elem_type,
            type_args=tuple(targs),
            birth_id=self.indexed_borrow_serial,
            site=site_node,
            field_path=tuple(member_suffix),
            nested_indices=tuple(nested_levels),
        )
        return info, element

    def local(self: _Elaborator, node: Node, environment: dict[str, _Binding]) -> dict[str, _Binding]:
        self.site = node
        if node["kind"] in {"let_pattern", "var_pattern"}:
            binding = self.expression(self.node(node["value"]), environment)
            self._check_value_copy(self.node(node["value"]), binding.type)
            pat = self._parse_pattern(self.node(node["pattern"]), set())
            self._require_irrefutable(pat)
            self._typecheck_pattern(pat, binding.type, environment)
            extended = dict(environment)
            self._consume_call_updates(extended, node)
            result_paths: set[str] | None = set() if self.in_executable_function else None
            self._bind_irrefutable(pat, binding, extended, result_paths)
            if result_paths is not None and result_paths:
                self.result_bindings[id(node)] = result_paths
            bound_names: set[str] = set()
            self._collect_pat_names(pat, bound_names)
            for bname in bound_names:
                if bname in self.frozen_collections:
                    raise self.fail("type", f"cannot rebind collection '{bname}' while iterating over it", node)
                self.local_borrows.pop(bname, None)
                self.indexed_local_borrows.pop(bname, None)
                if node["kind"] == "var_pattern":
                    self.mutable_locals.add(bname)
                else:
                    self.mutable_locals.discard(bname)
            return extended
        if node["kind"] == "constant_local":
            binding, _ = self.constant_value(node, environment)
        elif node["kind"] not in {"let", "typed_local", "var"}:
            raise self.fail("unsupported", "only local let/var name bindings are supported")
        else:
            self.no_roles(node, "grade")
            value_node = self._unwrap_group(self.node(node["value"]))
            type_mod: str | None = None
            if node["type"] is not None:
                tnode = self.node(node["type"])
                if tnode["kind"] == "modified_type" and tnode.get("modifier") in {"in", "ref", "shared_ref"}:
                    type_mod = cast("str", tnode["modifier"])
            expr_mod: str | None = None
            borrow_target_node = value_node
            if (
                value_node["kind"] == "unary"
                and isinstance(value_node.get("operator"), dict)
                and cast("Node", value_node["operator"]).get("text") in {"in", "ref", "shared_ref"}
            ):
                expr_mod = cast("str", cast("Node", value_node["operator"])["text"])
                borrow_target_node = self._unwrap_group(self.node(value_node["value"]))
            if type_mod is not None and expr_mod is not None and type_mod != expr_mod:
                raise self.fail(
                    "type",
                    f"local borrow modifier '{type_mod}' does not match initializer '{expr_mod}'",
                    node,
                )
            borrow_mode = expr_mod or type_mod
            if borrow_mode is not None:
                bname = self.name(node["name"])
                if self._is_indexed_borrow_target(borrow_target_node):
                    typed_borrow: Literal["in", "ref"] = "ref" if borrow_mode == "ref" else "in"
                    info, binding = self._resolve_indexed_local_borrow(
                        typed_borrow, borrow_target_node, environment, node
                    )
                    if node["type"] is not None:
                        value_type = self.type(self.node(node["type"]), environment)
                        self.site = node
                        self.unify(binding.type, value_type)
                        binding = _Binding(binding.term, value_type)
                    extended = dict(environment)
                    self._consume_call_updates(extended, node)
                    if bname in self.frozen_collections:
                        raise self.fail("type", f"cannot rebind collection '{bname}' while iterating over it", node)
                    self.local_borrows.pop(bname, None)
                    self.prophecy_borrows.pop(bname, None)
                    self._clear_partial_move_on_write(bname, ())
                    self.indexed_local_borrows[bname] = info
                    self.indexed_borrow_peers.append(
                        _IndexedBorrowPeer(
                            birth_id=info.birth_id,
                            owner=info.owner,
                            mode=info.mode,
                            index_term=info.index_term,
                            index_type=info.index_type,
                            guards=tuple(self.active_facts),
                            site=node,
                            field_path=info.field_path,
                            nested_indices=info.nested_indices,
                        )
                    )
                    if node["kind"] == "var":
                        self.var_locals.add(bname)
                    else:
                        self.var_locals.discard(bname)
                    if borrow_mode == "ref" or node["kind"] == "var":
                        self.mutable_locals.add(bname)
                    else:
                        self.mutable_locals.discard(bname)
                    if borrow_mode == "shared_ref":
                        self.shared_ref_locals.add(bname)
                    else:
                        self.shared_ref_locals.discard(bname)
                    self.slice_views.pop(bname, None)
                    self.slice_view_own_updates.pop(bname, None)
                    self.local_value_regions.pop(bname, None)
                    if node["type"] is not None:
                        self.local_type_regions[bname] = self._extract_type_region_qual(self.node(node["type"]))
                    self.bind_local(extended, bname, binding)
                    return extended
                if borrow_mode == "ref" and borrow_target_node["kind"] == "call":
                    call_b = self.expression(borrow_target_node, environment)
                    if (unwrapped_p := self._maybe_bind_prophecy_local(bname, call_b, environment, True)) is not None:
                        extended = dict(environment)
                        self._consume_call_updates(extended, node)
                        self.local_borrows.pop(bname, None)
                        self.indexed_local_borrows.pop(bname, None)
                        if node["kind"] == "var":
                            self.var_locals.add(bname)
                        else:
                            self.var_locals.discard(bname)
                        self.mutable_locals.add(bname)
                        self.shared_ref_locals.discard(bname)
                        self.bind_local(extended, bname, unwrapped_p)
                        return extended
                if borrow_mode == "ref" and borrow_target_node["kind"] == "call" and self._is_tracked_span_view_call(borrow_target_node):
                    binding = self.expression(borrow_target_node, environment)
                    if node["type"] is not None:
                        value_type = self.type(self.node(node["type"]), environment)
                        self.site = node
                        self.unify(binding.type, value_type)
                        binding = _Binding(binding.term, value_type)
                    b_w = self.whnf(binding.term)
                    b_head, b_args = self.spine(b_w)
                    if b_head != _constant("Span_Slice") or len(b_args) != 4:
                        raise self.fail("type", "'ref' slice borrow requires a mutable Span.Slice(...) view", node)
                    parent_w = self.whnf(b_args[1])
                    parent_name = next(
                        (env_k for env_k, env_b in environment.items() if self.whnf(env_b.term) == parent_w),
                        None,
                    )
                    if parent_name is None:
                        raise self.fail("type", "'ref' Span.Slice borrow requires a named Span owner", node)
                    if parent_name in self.readonly_in_params or self._is_readonly_span(environment[parent_name].term):
                        raise self.fail(
                            "type",
                            f"cannot take exclusive 'ref' borrow of read-only 'in' parameter '{parent_name}'",
                            node,
                        )
                    if parent_name in self.frozen_collections:
                        raise self.fail(
                            "type",
                            f"cannot take exclusive 'ref' borrow of frozen collection '{parent_name}'",
                            node,
                        )
                    if parent_name not in self.mutable_locals:
                        raise self.fail(
                            "type",
                            f"cannot take exclusive 'ref' borrow of immutable binding '{parent_name}'; declare it with 'var' or 'ref'",
                            node,
                        )
                    self._check_span_can_write(binding.term, environment, node)
                    extended = dict(environment)
                    self._consume_call_updates(extended, node)
                    if bname in self.frozen_collections:
                        raise self.fail("type", f"cannot rebind collection '{bname}' while iterating over it", node)
                    self._check_new_slice_view_disjoint(bname, binding.term, parent_name, extended, node)
                    self.local_borrows.pop(bname, None)
                    self.indexed_local_borrows.pop(bname, None)
                    self.prophecy_borrows.pop(bname, None)
                    self.mutable_locals.add(bname)
                    if node["kind"] == "var":
                        self.var_locals.add(bname)
                    else:
                        self.var_locals.discard(bname)
                    self.slice_views[bname] = parent_name
                    self.slice_view_own_updates.pop(bname, None)
                    self.local_value_regions.pop(bname, None)
                    self.bind_local(extended, bname, binding)
                    return extended
                owner_name, field_path, binding = self._resolve_local_borrow_target(
                    borrow_mode, borrow_target_node, environment, node
                )
                if node["type"] is not None:
                    value_type = self.type(self.node(node["type"]), environment)
                    self.site = node
                    self.unify(binding.type, value_type)
                    binding = _Binding(binding.term, value_type)
                extended = dict(environment)
                self._consume_call_updates(extended, node)
                if bname in self.frozen_collections:
                    raise self.fail("type", f"cannot rebind collection '{bname}' while iterating over it", node)
                self.indexed_local_borrows.pop(bname, None)
                self.prophecy_borrows.pop(bname, None)
                self._clear_partial_move_on_write(bname, ())
                self.local_borrows[bname] = (borrow_mode, owner_name, field_path)
                if node["kind"] == "var":
                    self.var_locals.add(bname)
                else:
                    self.var_locals.discard(bname)
                if borrow_mode == "ref" or node["kind"] == "var":
                    self.mutable_locals.add(bname)
                else:
                    self.mutable_locals.discard(bname)
                if borrow_mode == "shared_ref":
                    self.shared_ref_locals.add(bname)
                else:
                    self.shared_ref_locals.discard(bname)
                self.slice_views.pop(bname, None)
                self.slice_view_own_updates.pop(bname, None)
                self.local_value_regions.pop(bname, None)
                if node["type"] is not None:
                    self.local_type_regions[bname] = self._extract_type_region_qual(self.node(node["type"]))
                self.bind_local(extended, bname, binding)
                return extended
            if node["type"] is None:
                binding = self.expression(self.node(node["value"]), environment)
            else:
                value_type = self.type(self.node(node["type"]), environment)
                binding = _Binding(self.check(self.node(node["value"]), value_type, environment), value_type)
        bname = self.name(node["name"])
        if (unwrapped_p := self._maybe_bind_prophecy_local(bname, binding, environment, node["kind"] == "var")) is not None:
            binding = unwrapped_p
        else:
            self.prophecy_borrows.pop(bname, None)
            self._check_value_copy(self.node(node["value"]), binding.type)
        extended = dict(environment)
        self._consume_call_updates(extended, node)
        if self.in_executable_function and (paths := self._result_paths(bname, binding.type)):
            self.result_bindings[id(node)] = paths
        if bname in self.frozen_collections:
            raise self.fail("type", f"cannot rebind collection '{bname}' while iterating over it", node)
        self.local_borrows.pop(bname, None)
        self.indexed_local_borrows.pop(bname, None)
        self._clear_partial_move_on_write(bname, ())
        if node["kind"] == "var":
            self.var_locals.add(bname)
            self.mutable_locals.add(bname)
        else:
            self.var_locals.discard(bname)
            self.mutable_locals.discard(bname)
        self.shared_ref_locals.discard(bname)
        self.slice_views.pop(bname, None)
        self.slice_view_own_updates.pop(bname, None)
        self.local_value_regions.pop(bname, None)
        if node["kind"] != "constant_local" and node.get("type") is not None:
            self.local_type_regions[bname] = self._extract_type_region_qual(self.node(node["type"]))
        if (hr_tag := self._term_hr_region(binding.term, environment)) is not None:
            self.local_value_regions[bname] = (id(binding.term), hr_tag)
        b_w = self.whnf(binding.term)
        if b_w.kind == "app":
            b_head, b_args = self.spine(b_w)
            if b_head == _constant("Span_Slice") and len(b_args) == 4:
                parent_w = self.whnf(b_args[1])
                for env_k, env_b in extended.items():
                    if self.whnf(env_b.term) == parent_w:
                        if node["kind"] == "var":
                            self._check_new_slice_view_disjoint(bname, binding.term, env_k, extended, node)
                        self.slice_views[bname] = env_k
                        break
        self.bind_local(extended, bname, binding)
        return extended

    def match(self: _Elaborator, node: Node, environment: dict[str, _Binding], expected: _Term | None = None,
              *, expression_arms: bool = True, facts: tuple[_Binding, ...] = (),
              refine_scrutinee: bool = False, expected_scrutinee_type: _Term | None = None,
              visited_arms: set[int] | None = None, synthetic: bool = False,
              scrutinee: _Binding | None = None) -> _Binding:
        self.site = node
        value_node = self.node(node["value"])
        if scrutinee is None:
            if expected_scrutinee_type is not None:
                scrutinee = _Binding(self.check(value_node, expected_scrutinee_type, environment), expected_scrutinee_type)
            else:
                scrutinee = self.expression(value_node, environment)
        if synthetic and self.last_call_updates:
            environment = dict(environment)
            self._consume_call_updates(environment, value_node)
        if synthetic and expected_scrutinee_type == _BOOL:
            lint_branch(self, value_node, scrutinee.term, environment)
        root_var = self.fresh(scrutinee.type)
        root_var_id = cast("int", root_var.value)
        motive_node = node["motive"]
        motive_body: _Term | None = None
        if motive_node is not None:
            motive = self.node(motive_node, "match_motive")
            motive_env = dict(environment)
            self.bind_local(motive_env, self.name(motive["name"]), _Binding(root_var, scrutinee.type))
            motive_body = self.type(self.node(motive["type"]), motive_env)
            match_type = self.substitute(motive_body, root_var_id, scrutinee.term)
            if expected is not None:
                self.unify(match_type, expected)
        elif (expected is not None and scrutinee.term.kind == "var"
              and cast("int", scrutinee.term.value) in self.free(expected)):
            motive_body = self.substitute(expected, cast("int", scrutinee.term.value), root_var)
        if expected is not None and self._is_prop_type(expected):
            refine_scrutinee = True
        scrut_smaller_roots: frozenset[int] = frozenset[int]()
        scrut_destruct_roots: frozenset[int] = frozenset[int]()
        if scrutinee.term.kind == "var":
            scrut_var_id_0 = cast("int", scrutinee.term.value)
            scrut_smaller_roots = frozenset(
                [r_id for r_id, s_set in self.smaller_vars.items() if scrut_var_id_0 in s_set]
            )
            scrut_destruct_roots = frozenset(
                [
                    r_id
                    for r_id, s_set in self.smaller_vars.items()
                    if scrut_var_id_0 == r_id or scrut_var_id_0 in s_set
                ]
            )
        cases = self.nodes(node["cases"])
        nested_verdicts = self.in_executable_function and bool(self._result_paths("", scrutinee.type) - {""})
        if nested_verdicts and synthetic:
            raise self.fail("type", "unexamined Result in a pattern test: use an exhaustive match to handle each payload", value_node)
        if nested_verdicts:
            self.result_bindings[id(node)] = set()
        rows: list[_Row] = []
        arm_pattern_bindings: list[dict[str, _Binding]] = []
        for arm_index, arm in enumerate(cases):
            self.node(arm, "expression_case" if expression_arms else "case")
            pat = self._parse_pattern(self.node(arm["pattern"]), set())
            bindings_for_arm: dict[str, _Binding] = {}
            self._typecheck_pattern(
                pat,
                scrutinee.type,
                environment,
                bindings_for_arm,
                smaller_roots=scrut_smaller_roots,
                destruct_roots=scrut_destruct_roots,
                track_verdicts=nested_verdicts,
                whole_match_pattern=True,
            )
            if nested_verdicts:
                self.result_bindings[id(arm["pattern"])] = {
                    path for name, binding in bindings_for_arm.items() for path in self._result_paths(name, binding.type)
                }
            arm_pattern_bindings.append(bindings_for_arm)
            rows.append(_Row((pat,), (), arm, arm_index))
        if (self.in_executable_function and not synthetic and self._is_result(scrutinee.type)
                and not any(row.patterns[0].kind == "union" for row in rows)):
            raise self.fail("type", "unexamined Result: match an explicit Ok or Err case", node)
        scrutinee_type = self.whnf(scrutinee.type)
        scrutinee_head, scrutinee_targs = self.spine(scrutinee_type)
        if (scrutinee_type not in {_UNIT, _BOOL, _NAT, _CHAR}
                and self._int_spec(scrutinee_type) is None
                and scrutinee_type.kind != "prod"
                and not (
                    scrutinee_head == _constant("Vec")
                    and len(scrutinee_targs) == 2
                    and self.whnf(scrutinee_targs[0]) == _NAT
                )
                and not (
                    scrutinee_head.kind == "const"
                    and (scrutinee_head.value in self.records_by_type or scrutinee_head.value in self.unions_by_type)
                )):
            raise self.fail(
                "type",
                "match scrutinee must have type Nat, bool, char, Unit, a fixed-width integer, a product, a record or a union",
                value_node,
            )
        inferred_result = expected
        local_visited: set[int] = set()
        forwarded_arms: set[int] = set()
        forwardable = not synthetic and motive_body is None and len(rows) == 2 and (
            {row.patterns[0].value for row in rows if row.patterns[0].kind == "union"}
            in ({"Ok", "Err"}, {"Some", "None"})
        )
        initial_uninit_out = set(self.uninitialized_out_params)
        arm_uninit_sets: list[set[str]] = []

        def note_forwarding(
            index: int, value_node: Node, value: _Term, pattern_term: _Term, arm_env: dict[str, _Binding],
        ) -> None:
            root_pattern = rows[index].patterns[0]
            if (all(child.kind == "wild" and len(child.names) == 1 for child in root_pattern.args)
                    and forwards_case(self, value_node, value, pattern_term, arm_env, cast("str", root_pattern.value),
                                      tuple(child.names[0] for child in root_pattern.args))):
                forwarded_arms.add(index)

        def subst_cols(
            cols: list[tuple[_Term, _Term, _Term]], var_id: int, replacement: _Term
        ) -> list[tuple[_Term, _Term, _Term]]:
            return [(cv, cs, self.substitute(ct, var_id, replacement)) for cv, cs, ct in cols]

        def specialize_rows(active_rows: list[_Row], index: int, ctor_kind: str, ctor_term: _Term,
                            col_var_id: int, col_type: _Term, sub_count: int, *,
                            bool_value: bool = False, ctor_name: str = "") -> list[_Row]:
            specialized: list[_Row] = []
            for row in active_rows:
                pat = row.patterns[index]
                updated_bindings = tuple(
                    (
                        bname,
                        _Binding(
                            self.substitute(bval.term, col_var_id, ctor_term),
                            self.substitute(bval.type, col_var_id, ctor_term),
                        ),
                    )
                    for bname, bval in row.bindings
                )
                if pat.kind == "wild":
                    extra = tuple((name, _Binding(ctor_term, col_type)) for name in pat.names)
                    wilds = tuple(_Pat("wild", pat.node) for _ in range(sub_count))
                    specialized.append(_Row(
                        row.patterns[:index] + wilds + row.patterns[index + 1:],
                        updated_bindings + extra,
                        row.arm,
                        row.arm_index,
                    ))
                elif (
                    pat.kind == ctor_kind
                    and (ctor_kind != "bool" or pat.value == bool_value)
                    and (ctor_kind != "union" or self.union_ctors[cast("str", pat.value)][1].ctor_const == ctor_name)
                ):
                    specialized.append(_Row(
                        row.patterns[:index] + pat.args + row.patterns[index + 1:],
                        updated_bindings,
                        row.arm,
                        row.arm_index,
                    ))
            return specialized

        def compile_matrix(columns: list[tuple[_Term, _Term, _Term]], active_rows: list[_Row],
                           pattern_term: _Term) -> _Term:
            nonlocal inferred_result
            self.tick()
            if not active_rows:
                raise self.fail("type", "non-exhaustive match: missing pattern case", node)
            first = active_rows[0]
            if all(pat.kind == "wild" for pat in first.patterns):
                local_visited.add(first.arm_index)
                if visited_arms is not None:
                    visited_arms.add(first.arm_index)
                arm_env = dict(environment)
                leaf_pattern = pattern_term
                for col_var, col_scrutinee, _ in columns:
                    if col_var != col_scrutinee:
                        leaf_pattern = self.substitute(leaf_pattern, cast("int", col_var.value), col_scrutinee)
                arm_facts = facts
                if refine_scrutinee:
                    for env_name, env_binding in list(arm_env.items()):
                        if env_binding.term == scrutinee.term:
                            arm_env[env_name] = _Binding(
                                leaf_pattern,
                                scrutinee.type,
                                env_binding.generics,
                                env_binding.constant,
                            )
                        elif scrutinee.term.kind == "var" and cast("int", scrutinee.term.value) in self.free(env_binding.type):
                            arm_env[env_name] = _Binding(
                                env_binding.term,
                                self.substitute(env_binding.type, cast("int", scrutinee.term.value), leaf_pattern),
                                env_binding.generics,
                                env_binding.constant,
                            )
                    if scrutinee.term.kind == "var":
                        scrut_id = cast("int", scrutinee.term.value)
                        arm_facts = tuple(
                            _Binding(
                                f.term,
                                self.substitute(f.type, scrut_id, leaf_pattern),
                                f.generics,
                                f.constant,
                            )
                            for f in facts
                        )
                scrut_prophecy = self.prophecy_call_results.get(id(scrutinee.term))
                for name, bound in first.bindings:
                    bound_term = bound.term
                    bound_type = bound.type
                    for col_var, col_scrutinee, _ in columns:
                        if col_var != col_scrutinee:
                            bound_term = self.substitute(bound_term, cast("int", col_var.value), col_scrutinee)
                            bound_type = self.substitute(bound_type, cast("int", col_var.value), col_scrutinee)
                    if scrut_prophecy is not None and (pinfo := self._is_prophecy_pair_type(bound_type)) is not None:
                        val_t, owner_t = pinfo
                        fn_t = self.pi(val_t, owner_t)
                        self.prophecy_borrows[name] = (
                            scrut_prophecy[0],
                            _apps(_constant("Snd"), val_t, fn_t, bound_term),
                            val_t,
                        )
                        self.mutable_locals.add(name)
                        self.bind_local(arm_env, name, _Binding(_apps(_constant("Fst"), val_t, fn_t, bound_term), val_t))
                    else:
                        self.bind_local(arm_env, name, _Binding(bound_term, bound_type))
                for pat, (_, col_scrutinee, col_type) in zip(first.patterns, columns, strict=True):
                    for name in pat.names:
                        if scrut_prophecy is not None and (pinfo := self._is_prophecy_pair_type(col_type)) is not None:
                            val_t, owner_t = pinfo
                            fn_t = self.pi(val_t, owner_t)
                            self.prophecy_borrows[name] = (
                                scrut_prophecy[0],
                                _apps(_constant("Snd"), val_t, fn_t, col_scrutinee),
                                val_t,
                            )
                            self.mutable_locals.add(name)
                            self.bind_local(arm_env, name, _Binding(_apps(_constant("Fst"), val_t, fn_t, col_scrutinee), val_t))
                        else:
                            self.bind_local(arm_env, name, _Binding(col_scrutinee, col_type))
                arm = first.arm
                self.site = arm
                leaf_expected = (self.substitute(motive_body, root_var_id, leaf_pattern)
                                 if motive_body is not None else inferred_result)
                if expression_arms:
                    if synthetic:
                        self.uninitialized_out_params = set(initial_uninit_out)
                    value_node = self.node(arm["value"])
                    if leaf_expected is None:
                        evaluated = self.expression(value_node, arm_env)
                        inferred_result = evaluated.type
                        value = evaluated.term
                    else:
                        value = self.check(value_node, leaf_expected, arm_env)
                    if forwardable:
                        note_forwarding(first.arm_index, value_node, value, leaf_pattern, arm_env)
                    if synthetic:
                        arm_uninit_sets.append(set(self.uninitialized_out_params))
                    return value
                block_node = {"kind": "block", "span": arm["span"], "statements": arm["statements"]}
                self.uninitialized_out_params = set(initial_uninit_out)
                evaluated = self.block(block_node, arm_env, leaf_expected, facts=arm_facts)
                if forwardable:
                    steps = self.nodes(arm["statements"])
                    if len(steps) == 1 and steps[0]["kind"] == "block":
                        steps = self.nodes(steps[0]["statements"])
                    if len(steps) == 1 and steps[0]["kind"] == "return" and steps[0]["value"] is not None:
                        note_forwarding(first.arm_index, self.node(steps[0]["value"]), evaluated.term, leaf_pattern, arm_env)
                arm_uninit_sets.append(set(self.uninitialized_out_params))
                if motive_body is None and inferred_result is None:
                    inferred_result = evaluated.type
                return evaluated.term

            index = next(i for i, pat in enumerate(first.patterns) if pat.kind != "wild")
            col_var, col_scrutinee, col_type = columns[index]
            col_var_id = cast("int", col_var.value)
            col_type = self.whnf(col_type)
            without_index = columns[:index] + columns[index + 1:]

            def column_result_type() -> _Term:
                if motive_body is not None:
                    return self.substitute(motive_body, root_var_id, pattern_term)
                return cast("_Term", inferred_result)

            def split_literal_column(
                lit_term: _Term,
                eq_cond: _Term,
                ne_cond: _Term,
                matches_literal: Callable[[_Pat], bool],
            ) -> _Term:
                yes_rows: list[_Row] = []
                no_rows: list[_Row] = []
                for row in active_rows:
                    pat = row.patterns[index]
                    updated_bindings = tuple(
                        (
                            bname,
                            _Binding(
                                self.substitute(bval.term, col_var_id, lit_term),
                                self.substitute(bval.type, col_var_id, lit_term),
                            ),
                        )
                        for bname, bval in row.bindings
                    )
                    if pat.kind == "wild":
                        extra = tuple((name, _Binding(lit_term, col_type)) for name in pat.names)
                        yes_rows.append(
                            _Row(
                                row.patterns[:index] + row.patterns[index + 1:],
                                updated_bindings + extra,
                                row.arm,
                                row.arm_index,
                            )
                        )
                        no_rows.append(row)
                    elif matches_literal(pat):
                        yes_rows.append(
                            _Row(
                                row.patterns[:index] + row.patterns[index + 1:],
                                updated_bindings,
                                row.arm,
                                row.arm_index,
                            )
                        )
                    else:
                        no_rows.append(row)
                self.active_facts.append(eq_cond)
                try:
                    yes_branch = compile_matrix(
                        subst_cols(without_index, col_var_id, lit_term),
                        yes_rows,
                        self.substitute(pattern_term, col_var_id, lit_term),
                    )
                finally:
                    self.active_facts.pop()
                self.active_facts.append(ne_cond)
                try:
                    no_branch = compile_matrix(columns, no_rows, pattern_term)
                finally:
                    self.active_facts.pop()
                ret_ty = column_result_type()
                return _term("if", ret_ty, eq_cond, yes_branch, no_branch)

            if first.patterns[index].kind == "string":
                target_str = cast("str", first.patterns[index].value)
                str_b = self._bytes_binding(target_str.encode("latin1"))
                eq_cond = self._structural_eq_bool(str_b.type, col_scrutinee, str_b.term, node)
                return split_literal_column(
                    str_b.term,
                    eq_cond,
                    _app(_constant("!"), eq_cond),
                    lambda pat: pat.kind == "string" and pat.value == target_str,
                )

            if col_type == _CHAR:
                target_cp = cast("int", first.patterns[index].value)
                lit_term = _term("char", value=target_cp)
                return split_literal_column(
                    lit_term,
                    _apps(_constant("char_eq"), col_scrutinee, lit_term),
                    _apps(_constant("char_ne"), col_scrutinee, lit_term),
                    lambda pat: pat.kind == "char" and pat.value == target_cp,
                )

            if col_type == _UNIT:
                unit_term = _term("unit")
                body = compile_matrix(
                    subst_cols(without_index, col_var_id, unit_term),
                    specialize_rows(active_rows, index, "unit", unit_term, col_var_id, _UNIT, 0),
                    self.substitute(pattern_term, col_var_id, unit_term),
                )
                if motive_body is None:
                    return body
                motive_lam = _term("lam", _UNIT, self.substitute(motive_body, root_var_id, pattern_term), value=col_var_id)
                return _term("unit_match", motive_lam, col_scrutinee, body)

            if col_type == _BOOL:
                true_term = _term("bool", value=1)
                false_term = _term("bool", value=0)
                self.active_facts.append(col_scrutinee)
                try:
                    yes = compile_matrix(
                        subst_cols(without_index, col_var_id, true_term),
                        specialize_rows(active_rows, index, "bool", true_term, col_var_id, _BOOL, 0, bool_value=True),
                        self.substitute(pattern_term, col_var_id, true_term),
                    )
                    yes_refs = dict(self.final_ref_bindings)
                finally:
                    self.active_facts.pop()
                self.active_facts.append(_app(_constant("!"), col_scrutinee))
                try:
                    no = compile_matrix(
                        subst_cols(without_index, col_var_id, false_term),
                        specialize_rows(active_rows, index, "bool", false_term, col_var_id, _BOOL, 0, bool_value=False),
                        self.substitute(pattern_term, col_var_id, false_term),
                    )
                    no_refs = dict(self.final_ref_bindings)
                finally:
                    self.active_facts.pop()
                if not expression_arms:
                    merged_refs = dict(environment)
                    for rk in set(yes_refs) & set(no_refs):
                        yb = yes_refs[rk]
                        nb = no_refs[rk]
                        if yb.term != nb.term:
                            merged_refs[rk] = _Binding(
                                self.whnf(_term("if", yb.type, col_scrutinee, yb.term, nb.term)),
                                yb.type,
                            )
                        else:
                            merged_refs[rk] = yb
                    self.final_ref_bindings = merged_refs
                if motive_body is None:
                    return _term("if", cast("_Term", inferred_result), col_scrutinee, yes, no)
                motive_lam = _term("lam", _BOOL, self.substitute(motive_body, root_var_id, pattern_term), value=col_var_id)
                return _term("bool_match", motive_lam, col_scrutinee, yes, no)

            col_int_spec = self._int_spec(col_type)
            if col_int_spec is not None:
                target_val = _parse_numeric_magnitude(cast("str", first.patterns[index].node["value"]))
                lit_term = _int_term(col_int_spec, target_val)
                return split_literal_column(
                    lit_term,
                    _apps(_constant(f"int_eq_{col_int_spec.name}"), col_scrutinee, lit_term),
                    _apps(_constant(f"int_ne_{col_int_spec.name}"), col_scrutinee, lit_term),
                    lambda pat: _parse_numeric_magnitude(cast("str", pat.node["value"])) == target_val,
                )

            if col_type.kind == "prod":
                left_type, right_type = col_type.args
                left_var = self.fresh(left_type)
                right_var = self.fresh(right_type)
                pair_term = _term("pair", left_type, right_type, left_var, right_var)
                sub_columns = [(left_var, left_var, left_type), (right_var, right_var, right_type)]
                body = compile_matrix(
                    subst_cols(columns[:index], col_var_id, pair_term)
                    + sub_columns
                    + subst_cols(columns[index + 1:], col_var_id, pair_term),
                    specialize_rows(active_rows, index, "pair", pair_term, col_var_id, col_type, 2),
                    self.substitute(pattern_term, col_var_id, pair_term),
                )
                motive_return = column_result_type()
                motive_lam = _term("lam", col_type, motive_return, value=col_var_id)
                branch_lam = _term("lam", left_type, _term("lam", right_type, body, value=right_var.value), value=left_var.value)
                return _term("pair_match", motive_lam, col_scrutinee, branch_lam)

            col_head, col_type_args = self.spine(col_type)
            type_name = col_head.value if col_head.kind == "const" and isinstance(col_head.value, str) else ""
            record = self.records_by_type.get(type_name)
            union_info = self.unions_by_type.get(type_name)

            def constructor_body(
                ctor: _RecordInfo | _UnionCtor, fields: list[_Binding],
            ) -> _Term:
                arguments = [binding.term for binding in fields] or [_term("unit")]
                ctor_term = _apps(_constant(ctor.ctor_const), *col_type_args, *arguments)
                sub_columns = [(binding.term, binding.term, binding.type) for binding in fields]
                return compile_matrix(
                    subst_cols(columns[:index], col_var_id, ctor_term)
                    + sub_columns
                    + subst_cols(columns[index + 1:], col_var_id, ctor_term),
                    specialize_rows(
                        active_rows, index, "record" if isinstance(ctor, _RecordInfo) else "union",
                        ctor_term, col_var_id, col_type, len(fields), ctor_name=ctor.ctor_const,
                    ),
                    self.substitute(pattern_term, col_var_id, ctor_term),
                )

            def product_branch(
                ctor: _RecordInfo | _UnionCtor, generics: tuple[_Term, ...],
                subject: _Term, subject_id: int, subject_type: _Term,
                inject: Callable[[_Term], _Term] | None = None,
            ) -> _Term:
                """Destructure two or more fields, restoring their dependencies in each match motive."""
                nonlocal inferred_result
                fields: list[_Binding] = []

                def instantiate(target: _Term, earlier: list[_Binding]) -> _Term:
                    result = self._instantiate_generic_type(generics, col_type_args, target)
                    for field, binding in zip(ctor.fields, earlier, strict=False):
                        result = self.substitute(result, cast("int", field.var.value), binding.term)
                    return result

                for field in ctor.fields:
                    field_type = instantiate(field.type, fields)
                    fields.append(_Binding(self.fresh(field_type), field_type))
                body = constructor_body(ctor, fields)
                if ctor.is_dependent:
                    tail_types = [
                        instantiate(ctor.tail_sig_types[k + 1], fields[:k + 1])
                        for k in range(len(fields) - 1)
                    ]
                else:
                    tail_types = [fields[-1].type]
                    for field_binding in reversed(fields[1:-1]):
                        tail_types.append(_term("prod", field_binding.type, tail_types[-1]))
                    tail_types.reverse()
                tails = [self.fresh(tail) for tail in tail_types[:-1]] + [fields[-1].term]
                for k in range(len(fields) - 2, -1, -1):
                    left, right, right_type = fields[k], tails[k], tail_types[k]
                    if k == 0:
                        scrut, scrut_id, scrut_type = subject, subject_id, subject_type
                    else:
                        scrut, scrut_type = tails[k - 1], tail_types[k - 1]
                        scrut_id = cast("int", scrut.value)
                    motive_return = cast("_Term", inferred_result)
                    if k == 0 and inject is None and motive_body is not None:
                        motive_return = self.substitute(motive_body, root_var_id, pattern_term)
                    elif motive_body is not None and isinstance(ctor, _UnionCtor) and not ctor.is_dependent:
                        payload, payload_type = scrut, scrut_type
                        for prefix in reversed(fields[:k]):
                            payload = _term("pair", prefix.type, payload_type, prefix.term, payload)
                            payload_type = _term("prod", prefix.type, payload_type)
                        if inject is not None:
                            payload = inject(payload)
                        motive_return = self.substitute(
                            motive_body, root_var_id, self.substitute(pattern_term, col_var_id, payload),
                        )
                    left_id = cast("int", left.term.value)
                    if ctor.is_dependent and left_id in self.free(motive_return):
                        family = _term("lam", left.type, right_type, value=left_id)
                        projection = _term("projT1", left.type, family, _term("var", value=scrut_id))
                        motive_return = self.substitute(motive_return, left_id, projection)
                        if motive_body is None and inferred_result is not None:
                            inferred_result = self.substitute(motive_return, scrut_id, scrut)
                    motive = _term("lam", scrut_type, motive_return, value=scrut_id)
                    branch = _term("lam", left.type, _term("lam", right_type, body, value=right.value), value=left_id)
                    body = _term("sigT_match" if ctor.is_dependent else "pair_match", motive, scrut, branch)
                return body

            if record is not None:
                single_ctor, generics = record, record.generic_vars
            elif union_info is not None and len(union_info.constructors) == 1:
                single_ctor, generics = union_info.constructors[0], union_info.generic_vars
            else:
                single_ctor, generics = None, ()
            if single_ctor is not None:
                ctor = single_ctor
                if not ctor.fields:
                    body = constructor_body(ctor, [])
                    if motive_body is None:
                        return body
                    motive = self.substitute(motive_body, root_var_id, pattern_term)
                    return _term("unit_match", _term("lam", col_type, motive, value=col_var_id), col_scrutinee, body)
                if len(ctor.fields) == 1:
                    field_type = self._instantiate_generic_type(generics, col_type_args, ctor.fields[0].type)
                    field_var = self.fresh(field_type)
                    unit_var = self.fresh(_UNIT)
                    body = constructor_body(ctor, [_Binding(field_var, field_type)])
                    if isinstance(ctor, _UnionCtor) and motive_body is not None:
                        pair = _term("pair", field_type, _UNIT, field_var, unit_var)
                        unit_motive = self.substitute(
                            motive_body, root_var_id, self.substitute(pattern_term, col_var_id, pair),
                        )
                        body = _term("unit_match", _term("lam", _UNIT, unit_motive, value=unit_var.value), unit_var, body)
                    motive = column_result_type()
                    branch = _term("lam", field_type, _term("lam", _UNIT, body, value=unit_var.value), value=field_var.value)
                    return _term("pair_match", _term("lam", col_type, motive, value=col_var_id), col_scrutinee, branch)
                return product_branch(ctor, generics, col_scrutinee, col_var_id, col_type)

            if union_info is not None:
                inst_payload_types = [
                    self._instantiate_generic_type(union_info.generic_vars, col_type_args, c.payload_type)
                    for c in union_info.constructors
                ]
                inst_suffix_types = [
                    self._instantiate_generic_type(union_info.generic_vars, col_type_args, st)
                    for st in union_info.suffix_types
                ]
                num_ctors = len(union_info.constructors)

                def suffix_inj(from_idx: int, inner_term: _Term) -> _Term:
                    acc = inner_term
                    for j in range(from_idx - 1, -1, -1):
                        acc = _term("inr", inst_payload_types[j], inst_suffix_types[j + 1], acc)
                    return acc

                def ctor_inj(ctor_idx: int, payload_term: _Term) -> _Term:
                    base = (
                        _term("inl", inst_payload_types[ctor_idx], inst_suffix_types[ctor_idx + 1], payload_term)
                        if ctor_idx < num_ctors - 1
                        else payload_term
                    )
                    return suffix_inj(ctor_idx, base)

                payload_vars: list[_Term] = []
                payload_branches: list[_Term] = []
                for ctor_idx, ctor_info in enumerate(union_info.constructors):
                    if not ctor_info.fields:
                        pvar = self.fresh(_UNIT)
                        leaf_body = constructor_body(ctor_info, [])
                        if motive_body is None:
                            pbranch = leaf_body
                        else:
                            motive_ret = self.substitute(
                                motive_body,
                                root_var_id,
                                self.substitute(pattern_term, col_var_id, ctor_inj(ctor_idx, pvar)),
                            )
                            pbranch = _term(
                                "unit_match",
                                _term("lam", _UNIT, motive_ret, value=pvar.value),
                                pvar,
                                leaf_body,
                            )
                    elif len(ctor_info.fields) == 1:
                        ft_0 = self._instantiate_generic_type(
                            union_info.generic_vars, col_type_args, ctor_info.fields[0].type
                        )
                        pvar = self.fresh(ft_0)
                        pbranch = constructor_body(ctor_info, [_Binding(pvar, ft_0)])
                    else:
                        payload_type = inst_payload_types[ctor_idx]
                        pvar = self.fresh(payload_type)
                        pbranch = product_branch(
                            ctor_info, union_info.generic_vars, pvar, cast("int", pvar.value), payload_type,
                            partial(ctor_inj, ctor_idx),
                        )
                    payload_vars.append(pvar)
                    payload_branches.append(pbranch)

                sum_vars = [self.fresh(inst_suffix_types[i]) for i in range(1, num_ctors - 1)]
                acc_body = payload_branches[-1]
                acc_var = payload_vars[-1]
                for i in range(num_ctors - 2, -1, -1):
                    left_lam = _term("lam", inst_payload_types[i], payload_branches[i], value=payload_vars[i].value)
                    right_lam = _term("lam", inst_suffix_types[i + 1], acc_body, value=acc_var.value)
                    if i == 0:
                        scrut = col_scrutinee
                        scrut_var_id = col_var_id
                        scrut_type = col_type
                        motive_return = column_result_type()
                    else:
                        scrut = sum_vars[i - 1]
                        scrut_var_id = cast("int", scrut.value)
                        scrut_type = inst_suffix_types[i]
                        motive_return = (
                            self.substitute(
                                motive_body,
                                root_var_id,
                                self.substitute(pattern_term, col_var_id, suffix_inj(i, scrut)),
                            )
                            if motive_body is not None
                            else cast("_Term", inferred_result)
                        )
                    motive_lam = _term("lam", scrut_type, motive_return, value=scrut_var_id)
                    acc_body = _term("sum_match", motive_lam, scrut, left_lam, right_lam)
                    if i > 0:
                        acc_var = sum_vars[i - 1]
                return acc_body

            if col_type == _NAT:
                zero_term = _term("nat", value=0)
                zero_body = compile_matrix(
                    subst_cols(without_index, col_var_id, zero_term),
                    specialize_rows(active_rows, index, "zero", zero_term, col_var_id, _NAT, 0),
                    self.substitute(pattern_term, col_var_id, zero_term),
                )
                pred_var = self.fresh(_NAT)
                pred_var_id = cast("int", pred_var.value)
                for r_id, s_set in self.smaller_vars.items():
                    if (
                        col_var_id == r_id
                        or col_var_id in s_set
                        or (
                            col_scrutinee.kind == "var"
                            and (
                                cast("int", col_scrutinee.value) == r_id
                                or cast("int", col_scrutinee.value) in s_set
                            )
                        )
                    ):
                        s_set.add(pred_var_id)
                succ_term = _app(_constant("Succ"), pred_var)
                sub_columns = [(pred_var, pred_var, _NAT)]
                succ_body = compile_matrix(
                    subst_cols(columns[:index], col_var_id, succ_term)
                    + sub_columns
                    + subst_cols(columns[index + 1:], col_var_id, succ_term),
                    specialize_rows(active_rows, index, "succ", succ_term, col_var_id, _NAT, 1),
                    self.substitute(pattern_term, col_var_id, succ_term),
                )
                motive_return = column_result_type()
                motive_lam = _term("lam", _NAT, motive_return, value=col_var_id)
                succ_lam = _term("lam", _NAT, succ_body, value=pred_var.value)
                return _term("nat_match", motive_lam, col_scrutinee, zero_body, succ_lam)

            raise self.fail("type", "match column must have type Nat, bool, Unit, a product or a record", node)

        term = compile_matrix([(root_var, scrutinee.term, scrutinee_type)], rows, root_var)
        result_type = (self.substitute(motive_body, root_var_id, scrutinee.term)
                       if motive_body is not None else cast("_Term", inferred_result))
        if not synthetic:
            for arm_index, arm in enumerate(cases):
                if arm_index in local_visited:
                    continue
                arm_env = dict(environment)
                for bname, bval in arm_pattern_bindings[arm_index].items():
                    self.bind_local(arm_env, bname, bval)
                self.site = arm
                if expression_arms:
                    self.check(self.node(arm["value"]), result_type, arm_env)
                else:
                    block_node = {"kind": "block", "span": arm["span"], "statements": arm["statements"]}
                    self.uninitialized_out_params = set(initial_uninit_out)
                    self.block(block_node, arm_env, result_type, facts=facts)
                    arm_uninit_sets.append(set(self.uninitialized_out_params))
                pattern = rows[arm_index].patterns[0]
                for previous in rows[:arm_index]:
                    covering = previous.patterns[0]
                    if self._pattern_covers(covering, pattern):
                        reason = f"earlier arm {previous.arm_index + 1} covers this pattern"
                        if covering.kind == "wild" and covering.names:
                            binder = covering.names[0]
                            reason = f"earlier pattern '{binder}' binds every value"
                        raise self.fail("type", f"unreachable match arm: {reason}", pattern.node)
        if arm_uninit_sets:
            merged_uninit: set[str] = set()
            for s in arm_uninit_sets:
                merged_uninit |= s
            self.uninitialized_out_params = merged_uninit
        if forwardable:
            observe(self, "HOLDFAST126", node, "match reconstructs its scrutinee unchanged"
                    if len(forwarded_arms) == 2 and self.resolve(result_type) == self.resolve(scrutinee.type) else None)
        return _Binding(term, result_type)
