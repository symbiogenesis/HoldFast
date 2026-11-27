# SPDX-License-Identifier: Apache-2.0
"""Advisory findings for checked memory effects, places, and loan modes."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from toolchain import loans
from toolchain.elaborate_lints import node_offset, report_lint
from toolchain.elaborate_protocol import syntax_nodes as _walk
from toolchain.elaborate_types import _BOOL, _CHAR, _NAT, _UNIT, _parse_numeric_magnitude

if TYPE_CHECKING:
    from collections.abc import Iterator

    from toolchain.elaborate import _Elaborator
    from toolchain.elaborate_types import Node, _Binding, _RecordInfo, _RecordInvariant

_report = report_lint


def _effect_entries(elab: _Elaborator, clause: Node) -> Iterator[tuple[str, str, Node]]:
    for item in elab.nodes(clause["values"]):
        if item["kind"] == "name":
            yield "none", "", item
            continue
        kind = elab.name(elab.node(item["callee"])["name"])
        for arg in elab.nodes(item["arguments"]):
            target = elab._unwrap_group(elab.node(arg["value"]))
            path = elab._dotted_member_path(target)
            if path is not None:
                yield kind, path, target


def lint_effect_entries(elab: _Elaborator, clause: Node) -> None:
    entries = list(_effect_entries(elab, clause))
    has_effects = any(kind != "none" for kind, _, _ in entries)
    seen: set[tuple[str, str]] = set()
    for kind, target, site in entries:
        if kind == "none" and has_effects:
            _report(elab, "HOLDFAST118", site, "'none' adds nothing to this effect bound")
        elif (kind, target) in seen:
            name = "none" if kind == "none" else f"{kind}({target})"
            _report(elab, "HOLDFAST118", site, f"duplicate effect allowance '{name}'")
        seen.add((kind, target))


def lint_unused_effects(
    elab: _Elaborator, clause: Node, body: Node, reads: set[str], writes: set[str], *, public: bool,
) -> None:
    # With no calls or member access in the body, no opaque invocation or
    # getter can account for an effect absent from the checked footprint.
    if any(node["kind"] in {"call", "member", "lambda", "typed_lambda"} for node in _walk(body)):
        return
    code = "HOLDFAST134" if public else "HOLDFAST119"
    for kind, target, site in _effect_entries(elab, clause):
        if ("HOLDFAST118", node_offset(site)) in elab.semantic_lints:
            continue
        if kind == "calls" or (kind == "reads" and target not in reads) or (kind == "writes" and target not in writes):
            _report(elab, code, site, f"effect allowance '{kind}({target})' is unused by the checked body")


def _stable_bound(elab: _Elaborator, expression: Node, stable: set[str]) -> str | None:
    expression = elab._unwrap_group(expression)
    if expression["kind"] == "name":
        name = elab.name(expression["name"])
        return name if name in stable else None
    if expression["kind"] == "nat":
        suffix = cast("str", expression["suffix"])
        literal_type = suffix or elab.contextual_literal_types.get(node_offset(expression), "")
        return f"{_parse_numeric_magnitude(cast('str', expression['value']))}:{literal_type}"
    return None


def _projection(
    elab: _Elaborator, expression: Node, stable: set[str], *, slice_intrinsic: bool,
) -> tuple[str, tuple[tuple[str, str], ...], bool] | None:
    current = elab._unwrap_group(expression)
    if current["kind"] == "call":
        callee = elab._unwrap_group(elab.node(current["callee"]))
        path = elab._dotted_member_path(callee)
        args = elab.nodes(current["arguments"])
        if any(arg["label"] is not None for arg in args):
            return None
        if path == "old" and len(args) == 1:
            before = _projection(elab, elab.node(args[0]["value"]), stable, slice_intrinsic=slice_intrinsic)
            if before is not None and not before[2]:
                return before[0], before[1], True
        if path == "Span.Slice" and slice_intrinsic and len(args) == 3:
            base = _projection(elab, elab.node(args[0]["value"]), stable, slice_intrinsic=slice_intrinsic)
            offset = _stable_bound(elab, elab.node(args[1]["value"]), stable)
            length = _stable_bound(elab, elab.node(args[2]["value"]), stable)
            if base is not None and offset is not None and length is not None:
                return base[0], (*base[1], ("slice", f"{offset},{length}")), base[2]
        return None
    if current["kind"] == "name":
        return elab.name(current["name"]), (), False
    if current["kind"] not in {"member", "index"}:
        return None
    base = _projection(elab, elab.node(current["value"]), stable, slice_intrinsic=slice_intrinsic)
    if base is None:
        return None
    if current["kind"] == "member":
        return base[0], (*base[1], ("field", elab.name(current["name"]))), base[2]
    index = _stable_bound(elab, elab.node(current["index"]), stable)
    if index is not None:
        return base[0], (*base[1], ("index", index)), base[2]
    return None


def lint_read_only_frames(
    elab: _Elaborator, ensures: list[Node], parameters: list[Node], environment: dict[str, _Binding],
) -> None:
    stable: set[str] = set()
    shared: set[str] = set()
    for parameter in parameters:
        if parameter["name"] is None:
            continue
        name = elab.name(parameter["name"])
        if name == "result":
            continue
        mode = elab.node(parameter["type"]).get("modifier")
        if mode == "in":
            shared.add(name)
        elif mode is None:
            stable.add(name)
    if not shared or "old" in environment:
        return
    for clause in ensures:
        terms = elab._conjuncts(elab.node(clause["value"]))
        if any(term["kind"] == "is" for term in terms):
            continue
        for term in terms:
            if term["kind"] != "binary" or elab.operator(term["operator"]) != "==":
                continue
            left = _projection(elab, elab.node(term["left"]), stable, slice_intrinsic="Span" not in environment)
            right = _projection(elab, elab.node(term["right"]), stable, slice_intrinsic="Span" not in environment)
            if (left is not None and right is not None and left[0] in shared and left[1]
                    and left[:2] == right[:2] and left[2] != right[2]):
                head, _ = elab.spine(environment[left[0]].type)
                if head.kind == "const" and head.value in {"Span", "Slots"} and left[1][0][0] == "field" and left[1][0][1] != "Model":
                    continue
                _report(elab, "HOLDFAST120", term, f"frame equality follows from the shared loan '{left[0]}' and write-free footprint")


def _invariant_fields(
    elab: _Elaborator, record: _RecordInfo, invariant: _RecordInvariant,
) -> set[str] | None:
    by_projection = {field.proj_const: field.name for field in record.fields}
    fields: set[str] = set()
    pending = [invariant.term, invariant.type]
    while pending:
        term = pending.pop()
        if term == invariant.self_var:
            return None
        head, args = elab.spine(term)
        if (head.kind == "const" and isinstance(head.value, str) and head.value in by_projection
                and len(args) == len(record.generic_vars) + 1 and args[-1] == invariant.self_var):
            fields.add(by_projection[head.value])
            pending.extend(args[:-1])
        else:
            pending.extend(term.args)
    return fields


def lint_extra_lifts(elab: _Elaborator, statement: Node, target: str, record: _RecordInfo) -> None:
    if record.is_dependent:
        return
    body = elab.node(statement["body"])
    writes: set[str] = set()
    for step in elab.nodes(body["statements"]):
        if step["kind"] != "assignment":
            return
        place = elab._unwrap_group(elab.node(step["target"]))
        if place["kind"] != "member":
            return
        receiver = elab._unwrap_group(elab.node(place["value"]))
        if receiver["kind"] != "name" or elab.name(receiver["name"]) != target:
            return
        if any(node["kind"] in {"call", "lambda", "typed_lambda", "block", "propagate"} for node in _walk(elab.node(step["value"]))):
            return
        writes.add(elab.name(place["name"]))
    invariants = {invariant.name: invariant for invariant in record.invariants}
    for name in cast("list[Node]", statement["lifts"]):
        label = elab.name(name)
        fields = _invariant_fields(elab, record, invariants[label])
        if fields is not None and fields.isdisjoint(writes):
            _report(elab, "HOLDFAST121", name, f"invariant '{label}' does not depend on the fields written in this block")


_IMPLICIT_WRITE_TARGETS = {
    "CopyRepresentation": (1,),
    "Slots.CopyRepresentation": (1,),
    "Slots.TransferType": (0, 1),
    "TransferType": (0, 1),
    "Slots.Write": (0,),
    "Span.Write": (0,),
    "Span.Fill": (0,),
    "Span.CopyPrefix": (0,),
    "Span.Restore": (0,),
    "Format.Write": (0,),
}


def _place_root(elab: _Elaborator, place: Node) -> str | None:
    current = elab._unwrap_group(place)
    while current["kind"] in {"member", "index", "unary"}:
        current = elab._unwrap_group(elab.node(current["value"]))
    return elab.name(current["name"]) if current["kind"] == "name" else None


def _mutable_places(elab: _Elaborator, nodes: Iterator[Node]) -> set[str]:
    places: set[str] = set()
    for node in nodes:
        kind = node["kind"]
        targets: list[Node] = []
        if kind in {"assignment", "next"}:
            targets.append(elab.node(node["target"]))
        elif kind == "unary" and cast("Node", node["operator"])["text"] in {"ref", "shared_ref", "out", "move"}:
            targets.append(elab.node(node["value"]))
        elif kind == "foreach_collection" and node["mode"] == "ref":
            targets.append(elab.node(node["collection"]))
        elif kind == "call":
            callee = elab._unwrap_group(elab.node(node["callee"]))
            if callee["kind"] == "generic_application":
                callee = elab._unwrap_group(elab.node(callee["value"]))
            if callee["kind"] == "member":
                targets.append(elab.node(callee["value"]))
            path = elab._dotted_member_path(callee)
            args = elab.nodes(node["arguments"])
            targets.extend(elab.node(args[i]["value"]) for i in _IMPLICIT_WRITE_TARGETS.get(path or "", ()) if i < len(args))
        for target in targets:
            if (root := _place_root(elab, target)) is not None:
                places.add(root)
    return places


def lint_local_modes(elab: _Elaborator, body: Node) -> None:
    for node in _walk(body):
        if node["kind"] == "block":
            mutable_uses: set[str] = set()
            has_capture = False
            for statement in reversed(elab.nodes(node["statements"])):
                if statement["kind"] in {"var", "let"} and statement["name"] is not None:
                    site = cast("Node", statement["name"])
                    name = elab.name(site)
                    if name != "_" and name not in mutable_uses and not has_capture:
                        annotation = statement["type"]
                        if isinstance(annotation, dict) and annotation.get("modifier") == "ref":
                            unqualified = {**annotation, "modifier": None}
                            if loans._is_scalar_value_type(unqualified):
                                _report(elab, "HOLDFAST122", site, f"local '{name}' can use a shared 'in' loan")
                        elif statement["kind"] == "var":
                            _report(elab, "HOLDFAST124", site, f"local '{name}' can be declared with 'let'")
                has_capture |= any(sub["kind"] in {"lambda", "typed_lambda"} for sub in _walk(statement))
                mutable_uses.update(_mutable_places(elab, _walk(statement)))
        elif node["kind"] == "foreach_collection" and node["mode"] == "ref":
            loop_body = elab.node(node["body"])
            name = elab.name(node["name"])
            if name not in _mutable_places(elab, _walk(loop_body)) and all(
                sub["kind"] not in {"lambda", "typed_lambda", "return"} for sub in _walk(loop_body)
            ):
                _report(elab, "HOLDFAST122", cast("Node", node["name"]), f"element '{name}' can use a shared 'in' loan")


def lint_private_refs(
    elab: _Elaborator, declaration: Node, parameters: list[Node], body: Node, writes: set[str],
) -> None:
    body_nodes = list(_walk(body))
    if any(node["kind"] in {"call", "lambda", "typed_lambda"} for node in body_nodes):
        return
    mutable_uses = _mutable_places(elab, iter(body_nodes))
    statements = elab.nodes(body["statements"]) if body["kind"] == "block" else []
    first = statements[0] if statements else None
    init_name: str | None = None
    if first is not None and first["kind"] == "assignment" and cast("Node", first["operator"])["text"] == "=":
        target = elab._unwrap_group(elab.node(first["target"]))
        rhs = list(_walk(elab.node(first["value"])))
        if target["kind"] == "name":
            candidate = elab.name(target["name"])
            if all(
                item["kind"] not in {"block", "propagate"}
                and (item["kind"] != "name" or elab.name(item["name"]) != candidate) for item in rhs
            ):
                init_name = candidate
    input_terms = [
        elab.node(declaration["result"]),
        *(elab.node(parameter["type"]) for parameter in parameters),
        *(clause for clause in elab.nodes(declaration["contracts"]) if clause["kind"] != "effects"),
        *elab.nodes(declaration["generics"]),
    ]
    input_mentions = {
        elab.name(term["name"]) for input_term in input_terms for term in _walk(input_term) if term["kind"] == "name"
    }
    for index, parameter in enumerate(parameters):
        if parameter["name"] is None or elab.node(parameter["type"]).get("modifier") != "ref":
            continue
        site = cast("Node", parameter["name"])
        name = elab.name(site)
        ty = elab.entry_env[name].type
        if ty not in {_NAT, _BOOL, _CHAR, _UNIT} and elab._int_spec(ty) is None:
            continue
        if name not in writes and name not in mutable_uses:
            _report(elab, "HOLDFAST122", site, f"parameter '{name}' can use a shared 'in' loan")
        if name == init_name and name not in input_mentions:
            declaration_offset = cast("list[int]", declaration["span"])[0]
            elab.out_lint_candidates[declaration_offset, index] = cast("list[int]", site["span"])[0]
            _report(elab, "HOLDFAST123", site, f"parameter '{name}' is fully initialized before any use and can use 'out'")
