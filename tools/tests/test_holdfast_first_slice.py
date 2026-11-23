# SPDX-License-Identifier: Apache-2.0
"""Behavioral tests for the Span<byte> carrier and holdfast-first-slice lowering."""

import copy
import hashlib
import re
import subprocess
import tempfile
from pathlib import Path
from typing import cast

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import compiler_diff as cd
from toolchain import (
    elaborate as holdfast_elaborate,
)
from toolchain import (
    first_slice as holdfast_first_slice,
)
from toolchain import parser, solver_ledger
from toolchain.ast import HoldFastError

INDEPENDENT_CASES = True

type Node = dict[str, object]


class _Builder:
    """Minimal exact-source schema-2 AST builder for Span<byte> and contract tests."""

    def __init__(self, module: str) -> None:
        self.text = f"module {module};"
        self.module: Node = {"text": module, "span": [len("module "), len("module ") + len(module)]}
        self.declarations: list[Node] = []

    @property
    def offset(self) -> int:
        return len(self.text.encode("utf-8"))

    def write(self, chunk: str) -> None:
        self.text += chunk

    def name(self, text: str) -> Node:
        start = self.offset
        self.write(text)
        return {"text": text, "span": [start, self.offset]}

    def type_simple(self, name: str, *args: str) -> Node:
        start = self.offset
        name_node = self.name(name)
        arg_nodes: list[Node] = []
        if args:
            self.write("<")
            for idx, arg in enumerate(args):
                if idx:
                    self.write(", ")
                a_start = self.offset
                a_name = self.name(arg)
                arg_nodes.append({"kind": "type", "span": [a_start, self.offset], "name": a_name, "arguments": []})
            self.write(">")
        return {"kind": "type", "span": [start, self.offset], "name": name_node, "arguments": arg_nodes}

    def type_modified(self, modifier: str, name: str, *args: str) -> Node:
        start = self.offset
        self.write(modifier + " ")
        inner = self.type_simple(name, *args)
        return {
            "kind": "modified_type",
            "span": [start, self.offset],
            "modifier": modifier,
            "lifetime": None,
            "type": inner,
        }

    def nat_lit(self, digits: str, suffix: str) -> Node:
        start = self.offset
        self.write(digits + suffix)
        return {"kind": "nat", "span": [start, self.offset], "value": digits, "suffix": suffix}

    def bool_lit(self, val: bool) -> Node:
        start = self.offset
        self.write("true" if val else "false")
        return {"kind": "bool", "span": [start, self.offset], "value": val}

    def var(self, name: str) -> Node:
        start = self.offset
        n = self.name(name)
        return {"kind": "name", "span": [start, self.offset], "name": n}

    def member(self, recv_fn: object, field: str) -> Node:
        start = self.offset
        recv = cast("Node", recv_fn(self) if callable(recv_fn) else recv_fn)
        self.write(".")
        fname = self.name(field)
        return {"kind": "member", "span": [start, self.offset], "value": recv, "name": fname}

    def call_span(self, method: str, *arg_fns: object) -> Node:
        start = self.offset
        c_start = self.offset
        span_name = self.name("Span")
        recv: Node = {"kind": "name", "span": [c_start, self.offset], "name": span_name}
        self.write(".")
        m_name = self.name(method)
        callee: Node = {"kind": "member", "span": [c_start, self.offset], "value": recv, "name": m_name}
        self.write("(")
        args: list[Node] = []
        for idx, afn in enumerate(arg_fns):
            if idx:
                self.write(", ")
            a_start = self.offset
            val = cast("Node", afn(self) if callable(afn) else afn)
            args.append({"kind": "argument", "span": [a_start, self.offset], "label": None, "value": val})
        self.write(")")
        return {"kind": "call", "span": [start, self.offset], "callee": callee, "arguments": args}

    def binary(self, op: str, left_fn: object, right_fn: object) -> Node:
        start = self.offset
        left = cast("Node", left_fn(self) if callable(left_fn) else left_fn)
        self.write(" ")
        op_node = self.name(op)
        self.write(" ")
        right = cast("Node", right_fn(self) if callable(right_fn) else right_fn)
        return {"kind": "binary", "span": [start, self.offset], "operator": op_node, "left": left, "right": right}

    def let_expr(self, var_name: str, val_fn: object, body_fn: object) -> Node:
        start = self.offset
        b_start = self.offset
        self.write("let ")
        vname = self.name(var_name)
        self.write(" = ")
        val = cast("Node", val_fn(self) if callable(val_fn) else val_fn)
        binding: Node = {
            "kind": "let",
            "span": [b_start, self.offset],
            "name": vname,
            "type": None,
            "grade": None,
            "value": val,
        }
        self.write(" in ")
        body = cast("Node", body_fn(self) if callable(body_fn) else body_fn)
        return {"kind": "let_expression", "span": [start, self.offset], "binding": binding, "body": body}

    def envelope(self) -> tuple[bytes, Node]:
        raw = self.text.encode("utf-8")
        return raw, {
            "schema": 2,
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "ast": {
                "kind": "surface_file",
                "span": [0, len(raw)],
                "name": self.module,
                "declarations": self.declarations,
            },
        }


def _build_cap_gate_ast(cap_lit: str) -> tuple[bytes, Node]:
    b = _Builder("CapGate")
    b.write("\n")
    d_start = b.offset
    b.write("public ")
    ret_ty = b.type_simple("Span", "byte")
    b.write(" ")
    fn_name = b.name("PrepareHeader")
    b.write("(")
    p_start = b.offset
    p_ty = b.type_modified("ref", "Span", "byte")
    b.write(" ")
    p_name = b.name("dst")
    param: Node = {"kind": "parameter", "span": [p_start, b.offset], "name": p_name, "type": p_ty, "grade": None}
    b.write(")")

    contracts: list[Node] = []
    b.write(" ")
    eff_start = b.offset
    b.write("effects ")
    w_start = b.offset
    w_name = b.name("writes")
    b.write("(")
    a_start = b.offset
    dst_arg = b.var("dst")
    b.write(")")
    writes_call: Node = {
        "kind": "call",
        "span": [w_start, b.offset],
        "callee": {"kind": "name", "span": w_name["span"], "name": w_name},
        "arguments": [{"kind": "argument", "span": [a_start, b.offset - 1], "label": None, "value": dst_arg}],
    }
    contracts.append({"kind": "effects", "span": [eff_start, b.offset], "values": [writes_call]})

    for role, expr_fn in (
        ("requires", lambda x: x.member(lambda y: y.var("dst"), "CanRead")),
        ("requires", lambda x: x.member(lambda y: y.var("dst"), "CanWrite")),
        (
            "requires",
            lambda x: x.binary(
                "==",
                lambda y: y.member(lambda z: z.var("dst"), "Length"),
                lambda y: y.nat_lit(cap_lit, "usize"),
            ),
        ),
        (
            "ensures",
            lambda x: x.binary(
                "==",
                lambda y: y.member(lambda z: z.var("result"), "Length"),
                lambda y: y.nat_lit("4", "usize"),
            ),
        ),
    ):
        b.write(" ")
        c_start = b.offset
        b.write(role + " ")
        c_val = expr_fn(b)
        contracts.append({"kind": "contract", "span": [c_start, b.offset], "role": role, "value": c_val})

    b.write(" ")
    blk_start = b.offset
    b.write("{ ")
    fe_start = b.offset
    b.write("foreach (let ")
    i_name = b.name("i")
    b.write(" in ")
    rng_start = b.offset
    r_lo = b.nat_lit("0", "usize")
    b.write("..")
    r_hi = b.member(lambda x: x.var("dst"), "Length")
    rng_node: Node = {"kind": "range", "span": [rng_start, b.offset], "start": r_lo, "end": r_hi}
    b.write(")")
    fe_contracts: list[Node] = []
    for role, expr_fn in (
        ("invariant", lambda x: x.binary("<=", lambda y: y.var("i"), lambda y: y.member(lambda z: z.var("dst"), "Length"))),
        (
            "invariant",
            lambda x: x.binary(
                "&&",
                lambda y: y.binary(
                    "&&",
                    lambda z: z.member(lambda w: w.var("dst"), "CanRead"),
                    lambda z: z.member(lambda w: w.var("dst"), "CanWrite"),
                ),
                lambda y: y.binary(
                    "==",
                    lambda z: z.member(lambda w: w.var("dst"), "Length"),
                    lambda z: z.nat_lit(cap_lit, "usize"),
                ),
            ),
        ),
        (
            "decreases",
            lambda x: x.binary("-", lambda y: y.member(lambda z: z.var("dst"), "Length"), lambda y: y.var("i")),
        ),
    ):
        b.write(" ")
        lc_start = b.offset
        b.write(role + " ")
        lc_val = expr_fn(b)
        fe_contracts.append({"kind": "contract", "span": [lc_start, b.offset], "role": role, "value": lc_val})

    b.write(" ")
    lbody_start = b.offset
    b.write("{ ")
    asgn_start = b.offset
    idx_start = b.offset
    dst_v = b.var("dst")
    b.write("[")
    idx_i = b.var("i")
    b.write("]")
    idx_node: Node = {"kind": "index", "span": [idx_start, b.offset], "value": dst_v, "index": idx_i}
    b.write(" ")
    eq_op = b.name("=")
    b.write(" ")
    z_lit = b.nat_lit("0x00", "u8")
    b.write("; ")
    asgn_stmt: Node = {
        "kind": "assignment",
        "span": [asgn_start, b.offset - 1],
        "target": idx_node,
        "operator": eq_op,
        "value": z_lit,
    }
    b.write("}")
    lbody_node: Node = {"kind": "block", "span": [lbody_start, b.offset], "statements": [asgn_stmt]}
    fe_stmt: Node = {
        "kind": "foreach",
        "span": [fe_start, b.offset],
        "name": i_name,
        "range": rng_node,
        "contracts": fe_contracts,
        "body": lbody_node,
    }

    b.write(" ")
    let_start = b.offset
    b.write("let ")
    ro_name = b.name("roView")
    b.write(" = ")
    ro_val = b.call_span(
        "ReadOnly",
        lambda x: x.call_span(
            "Slice",
            lambda y: y.var("dst"),
            lambda y: y.nat_lit("0", "usize"),
            lambda y: y.nat_lit("4", "usize"),
        ),
    )
    b.write(";")
    let_stmt: Node = {
        "kind": "let",
        "span": [let_start, b.offset],
        "name": ro_name,
        "type": None,
        "grade": None,
        "value": ro_val,
    }
    b.write(" ")
    ret_start = b.offset
    b.write("return ")
    ret_val = b.var("roView")
    b.write(";")
    ret_stmt: Node = {"kind": "return", "span": [ret_start, b.offset], "value": ret_val}
    b.write(" }")
    body_block: Node = {
        "kind": "block",
        "span": [blk_start, b.offset],
        "statements": [fe_stmt, let_stmt, ret_stmt],
    }

    b.declarations.append({
        "kind": "function",
        "span": [d_start, b.offset],
        "name": fn_name,
        "result": ret_ty,
        "generics": [],
        "parameters": [param],
        "contracts": contracts,
        "body": body_block,
        "cancel": None,
        "modifiers": ["public"],
    })
    return b.envelope()


def _capacity_invariance_and_contracts() -> None:
    small_src, small_ast = _build_cap_gate_ast("8")
    large_src, large_ast = _build_cap_gate_ast("1_000_000_000")
    small_elab, small_state = holdfast_elaborate._checked_elaboration(small_src, small_ast)
    large_elab, large_state = holdfast_elaborate._checked_elaboration(large_src, large_ast)

    ensure(
        len(small_state.output) == len(large_state.output) == 8,
        "expected 8 emitted definitions (1 body + 1 post-state image + 5 restores + 1 ensures), "
        f"got {len(small_state.output)}",
    )
    ensure(
        small_state.work == large_state.work and small_state.reductions == large_state.reductions,
        "capacity-invariance gate failed: work or reduction steps differed between N=8 and N=1,000,000,000",
    )
    ensure(
        len(small_elab.gallina) == len(large_elab.gallina),
        "capacity-invariance gate failed: emitted Gallina size differed between N=8 and N=1,000,000,000",
    )
    holdfast_first_slice._check_capacity_structure(small_state, large_state)
    mismatched = list(large_state.output)
    mismatched[-1] = mismatched[-1].replace("ensures_0", "ensures_1")
    ensure(mismatched != large_state.output, "capacity fixture should include its named ensures obligation")
    large_state.output = mismatched
    with raises(ValueError,
                msg="capacity gate accepted different obligation names of equal encoded size") as raised:
        holdfast_first_slice._check_capacity_structure(small_state, large_state)
    ensure("proof structure" in str(raised.exception), "changed capacity proof should identify its structural mismatch")
    for field_tag in ("Base", "Length", "Tag", "PermRead", "PermWrite"):
        ensure(
            f"holdfast_d0_PrepareHeader_restores_0_{field_tag}" in small_elab.gallina,
            f"missing restores obligation for {field_tag}",
        )
    ensure("holdfast_d0_PrepareHeader_ensures_0" in small_elab.gallina, "missing ensures_0 obligation")
    ensure(
        "Corelib.Init.Datatypes.bool Corelib.Init.Datatypes.true Corelib.Init.Datatypes.true" not in small_elab.gallina,
        "an obligation reached the kernel as true = true",
    )
    for line in small_elab.gallina.splitlines():
        if line.startswith("Definition holdfast_d0_PrepareHeader_restores_0_"):
            ensure(
                "holdfast_d0_PrepareHeader_post_dst" in line,
                f"restores obligation does not state the callable's post-state image: {line[:120]}",
            )


def _negative_span_refusals() -> None:
    def single_def(body_fn: object, *, param_mod: str | None = None, is_fn: bool = False) -> tuple[bytes, Node]:
        b = _Builder("Neg")
        b.write("\n")
        d_start = b.offset
        b.write("public " if is_fn else "public definition ")
        ret_ty = b.type_simple("Span", "byte")
        b.write(" ")
        fn_name = b.name("Bad")
        params: list[Node] = []
        b.write("(")
        if param_mod is not None:
            p_start = b.offset
            p_ty = b.type_modified(param_mod, "Span", "byte")
            b.write(" ")
            p_name = b.name("s")
            params.append({"kind": "parameter", "span": [p_start, b.offset], "name": p_name, "type": p_ty, "grade": None})
        b.write(")")
        contracts: list[Node] = []
        if param_mod is not None:
            for expr_fn in (
                lambda x: x.member(lambda y: y.var("s"), "CanRead"),
                lambda x: x.member(lambda y: y.var("s"), "CanWrite"),
                lambda x: x.binary(">=", lambda y: y.member(lambda z: z.var("s"), "Length"), lambda y: y.nat_lit("8", "usize")),
            ):
                b.write(" ")
                c_start = b.offset
                b.write("requires ")
                c_val = expr_fn(b)
                contracts.append({"kind": "contract", "span": [c_start, b.offset], "role": "requires", "value": c_val})
        if is_fn:
            b.write(" ")
            blk_start = b.offset
            b.write("{ ")
            ret_start = b.offset
            b.write("return ")
            val = cast("Node", body_fn(b) if callable(body_fn) else body_fn)
            b.write(";")
            ret_stmt: Node = {"kind": "return", "span": [ret_start, b.offset], "value": val}
            b.write(" }")
            b.declarations.append({
                "kind": "function",
                "span": [d_start, b.offset],
                "name": fn_name,
                "result": ret_ty,
                "generics": [],
                "parameters": params,
                "contracts": contracts,
                "body": {"kind": "block", "span": [blk_start, b.offset], "statements": [ret_stmt]},
                "cancel": None,
                "modifiers": ["public"],
            })
        else:
            b.write(" => ")
            body = cast("Node", body_fn(b) if callable(body_fn) else body_fn)
            b.write(";")
            b.declarations.append({
                "kind": "definition",
                "span": [d_start, b.offset],
                "name": fn_name,
                "result": ret_ty,
                "generics": [],
                "parameters": params,
                "contracts": contracts,
                "value": body,
                "modifiers": ["public"],
            })
        return b.envelope()

    cases = (
        (
            "oob-write",
            single_def(
                lambda b: b.call_span(
                    "Write",
                    lambda x: x.call_span("AllocZeroed", lambda y: y.nat_lit("64", "usize"), lambda y: y.nat_lit("8", "usize")),
                    lambda x: x.nat_lit("8", "usize"),
                    lambda x: x.nat_lit("1", "u8"),
                )
            ),
            "cannot prove Span.Write index is within Span.Length bounds",
        ),
        (
            "mutate-in-borrow",
            single_def(
                lambda b: b.call_span("Write", lambda x: x.var("s"), lambda x: x.nat_lit("0", "usize"), lambda x: x.nat_lit("1", "u8")),
                param_mod="in",
            ),
            "cannot mutate a read-only 'in Span<byte>' borrow",
        ),
        (
            "broken-restores",
            single_def(
                lambda b: b.call_span("Slice", lambda x: x.var("s"), lambda x: x.nat_lit("0", "usize"), lambda x: x.nat_lit("4", "usize")),
                param_mod="ref",
            ),
            "assertion could not be established",
        ),
        (
            "capability-fabrication",
            single_def(
                lambda b: b.call_span("AllocZeroed", lambda x: x.nat_lit("64", "usize"), lambda x: x.nat_lit("8", "usize")),
                is_fn=True,
            ),
            "Span.AllocZeroed(base, length) is a specification constructor",
        ),
    )
    for label, (raw, ast), expected_msg in cases:
        with raises(HoldFastError, msg=f"{label} was unexpectedly accepted") as raised:
            holdfast_elaborate.elaborate(raw, ast)
        error = raised.exception
        ensure(
            error.kind == "type" and expected_msg in error.message,
            f"{label}: expected type error '{expected_msg}', got {error.kind}: {error.message}",
        )


def _clight_lowering_and_purecap_assembly() -> None:
    source = (TOOLS.parent / "examples/first_slice.hf").read_bytes()
    inv = holdfast_first_slice.build_foundation_inventory()
    ensure(len(cast("list[str]", inv["carrier_laws"])) == 12, "expected 12 carrier laws in foundation inventory")
    ensure(
        cast("list[str]", inv["validator_contract_obligations"])
        == [*(f"restores_0_{field}" for field in ("Base", "Length", "Tag", "PermRead", "PermWrite")),
            *(f"ensures_{index}" for index in range(10))],
        "foundation inventory omitted a validator obligation",
    )
    ensure(len(cast("list[str]", inv["scenario_theorems"])) == 7, "expected 7 scenario theorems in foundation inventory")
    blocking = cast("dict[str, str]", inv["blocking_dependencies"])
    for key in ("Q35b / Q35o / Q35p", "Q35c / Q35m / Q35k / Q35l", "Q2b", "Q35d / M1.2g / Q35j"):
        ensure(key in blocking, f"missing blocking dependency {key} in foundation inventory")

    incomplete_ast = {"schema": 2, "source_sha256": hashlib.sha256(source).hexdigest(),
                      "ast": {"kind": "surface_file", "declarations": []}}
    with raises(HoldFastError, msg="incomplete AST was accepted by lower_to_c") as raised:
        holdfast_first_slice.lower_to_c(source, incomplete_ast)
    err = raised.exception
    ensure(err.kind == "protocol", f"unexpected error on incomplete AST: {err}")

    with tempfile.TemporaryDirectory(prefix="holdfast-slice-asm-") as tmp:
        workdir = Path(tmp)
        for mode in ("pass", "bounds-trap", "tag-trap", "perm-trap"):
            stream = holdfast_first_slice._purecap_cheri_asm_stream(mode)
            elf = workdir / f"purecap_{mode}.elf"
            refusals, size = cd.assemble(stream, f"purecap_{mode}", elf)
            ensure(not refusals and size > 0 and elf.is_file(), f"purecap_{mode} failed assembly: {refusals}")


def _purecap_error_branch_profile() -> None:
    stream = holdfast_first_slice._purecap_cheri_asm_stream("pass")
    with tempfile.TemporaryDirectory(prefix="holdfast-control-profile-") as temporary:
        elf = Path(temporary) / "control.elf"
        refusals, _ = cd.assemble(stream, "control", elf)
        ensure(not refusals, f"control refused: {refusals}")
        original = elf.read_bytes()
        holdfast_first_slice._check_purecap_control_image(original)
        for word in (0x022180D7, 0x0000200F):  # vadd.vv v1,v2,v3; lc with a forbidden zero destination
            mutation, pc = holdfast_first_slice._cold_branch_image(original, word)
            with raises(ValueError,
                        msg=f"out-of-profile word {word:#010x} at the error exit was accepted") as raised:
                holdfast_first_slice._check_purecap_control_image(mutation)
            error = raised.exception
            ensure(f"instruction {word:#010x} at PC {pc:#x}" in str(error),
                   f"control profile reported the wrong word or site: {error}")


def _ordered_scalar_calls() -> None:
    def call(name: str, *values: Node) -> Node:
        return {"kind": "call", "callee": {"kind": "name", "name": {"text": name}},
                "arguments": [{"kind": "argument", "value": v} for v in values]}

    bool_type = {"kind": "type", "name": {"text": "bool"}}
    results = {"Probe": "bool", "First": "bool", "Second": "bool", "Both": "bool"}
    condition = {"kind": "binary", "operator": {"text": "&&"},
                 "left": {"kind": "name", "name": {"text": "holdfast_eval_0"}},
                 "right": call("Both", call("First"), call("Second"))}
    declaration: Node = {"name": {"text": "Probe"}, "result": bool_type,
                         "parameters": [{"name": {"text": "holdfast_eval_0"}, "type": bool_type}],
                         "body": {"kind": "block", "statements": [{"kind": "return", "value": condition}]}}
    code = holdfast_first_slice._lower_function_to_c(declaration, {}, {}, lambda _: "usize", results,
                                                lambda node: holdfast_first_slice._node_text(node["callee"]),
                                                lambda _: ("&&", "bool"))
    expected = """    holdfast_eval_3 = holdfast_eval_0;
    if (holdfast_eval_3) {
        holdfast_eval_1 = First();
        holdfast_eval_2 = Second();
        holdfast_eval_3 = Both(holdfast_eval_1, holdfast_eval_2);
    }
    return holdfast_eval_3;"""
    ensure(expected in code, "guarded scalar calls must execute once in left-to-right order")


def _first_slice_source_proofs() -> None:
    root = TOOLS.parent
    source = (root / "examples/first_slice.hf").read_bytes()
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, source, surface=True)
    translated = holdfast_elaborate.elaborate(source, parsed)
    ensure(not solver_ledger.ledger(translated.gallina),
           "first-slice contracts or scenario theorems exhausted the fixed proof-search budget")
    for name in (*holdfast_first_slice.EXPECTED_CONTRACT_OBLIGATIONS, "ValidateEmptyPacketOk"):
        ensure(f"_{name} :" in translated.gallina, f"first-slice proof export {name} disappeared")

    # Check the public contract before any of the separate scenario theorems enter scope.
    validator = source.split(b"public theorem ValidateEmptyPacketOk(", 1)[0]
    copy = b"Span.CopyPrefix(ref payloadView, pktPayload, payloadLen);"
    ensure(validator.count(copy) == 1, "payload-copy mutation no longer targets the validator")
    mutant = validator.replace(copy, b"Span.CopyPrefix(ref payloadView, pktPayload, 0usize);")
    with parser.cached_build(root) as compiled:
        parsed_mutant = parser.parse_source(compiled, mutant, surface=True)
    try:
        wrong = holdfast_elaborate.elaborate(mutant, parsed_mutant)
    except HoldFastError as error:
        ensure(error.line >= validator[:validator.index(b"    ensures (result is Err(FramingShort))")].count(b"\n") + 1,
               f"missing-copy control failed before its public contract: {error}")
    else:
        ensure(any("PrepareAndValidatePacket_ensures_" in item.export
                   for item in solver_ledger.ledger(wrong.gallina)), "public contract accepted an absent payload copy")


def _first_slice_recursion_boundary() -> None:
    root = TOOLS.parent
    packet = (root / holdfast_first_slice.EXAMPLE).read_bytes()
    math_source = b"""
public definition Type<1> SmallUniverse() => type Type;
public definition Nat CountDown(Nat n) decreases n => match (n) { 0 => 0, Succ(k) => CountDown(k) };
public lemma Erased() ensures CountDown(3) == 0 proof { assert CountDown(3) == 0; }
"""
    with parser.cached_build(root) as compiled:
        proof_source = packet + math_source
        parsed = parser.parse_source(compiled, proof_source, surface=True)
        checked = holdfast_elaborate.elaborate(proof_source, parsed)
        generated, _ = holdfast_first_slice.lower_to_c(proof_source, parsed, checked=checked)
        ensure("_SmallUniverse :" in checked.gallina and "_CountDown :" in checked.gallina,
               "mathematical universe or structural recursion disappeared from the proof module")
        ensure("SmallUniverse" not in generated and "CountDown" not in generated,
               "mathematical declarations consumed executable representation")
        recursive = packet.replace(b"WritePacket8", b"OriginalWritePacket8") + b"""
public Nat WritePacket8(Nat n) decreases n {
    match (n) { 0 => return 0; Succ(k) => return WritePacket8(k); }
}
"""
        parsed = parser.parse_source(compiled, recursive, surface=True)
        checked = holdfast_elaborate.elaborate(recursive, parsed)
        with raises(ValueError, msg="packet lowering emitted recursion with unbounded call depth") as raised:
            holdfast_first_slice.lower_to_c(recursive, parsed, checked=checked)
        error = raised.exception
        ensure("WritePacket8' is recursive and has no admitted stack bound" in str(error),
               f"recursive executable lost its resource-bound diagnostic: {error}")


def _execute_generated_packet_c() -> None:
    root = TOOLS.parent
    source = (root / holdfast_first_slice.EXAMPLE).read_bytes()
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, source, surface=True)
    checked = holdfast_elaborate.elaborate(source, parsed)
    with tempfile.TemporaryDirectory() as temporary:
        c_file = Path(temporary) / "packet.c"
        executable = Path(temporary) / "packet"
        def check_program(program: str, expected: int) -> None:
            c_file.write_text(program, encoding="utf-8")
            for optimization in ("-O0", "-O2"):
                subprocess.run(["cc", "-std=c11", optimization, str(c_file), "-o", str(executable)],
                               check=True, timeout=30)
                observed = subprocess.run([str(executable)], check=False, timeout=5).returncode
                ensure(observed == expected, f"packet C {optimization} returned {observed}, expected {expected}")

        generated, checks = holdfast_first_slice.lower_to_c(source, parsed, checked=checked)
        ensure(checks == 20, "emitted packet scenario check count changed")
        check_program(generated, 0)
        bad_header = "out->err = VOS_ERR_BadMagicOrFlags;"
        ensure(generated.count(bad_header) == 1, "missing lowered bad-header return")
        check_program(generated.replace(bad_header, """
            if (payloadLen > 4UL) { out->err = VOS_ERR_LengthOutOfBounds; }
            else { out->err = VOS_ERR_BadMagicOrFlags; }"""), 20)
        returned = "holdfast_span_copy_meta(&out->ok.PayloadView, &payloadView);"
        ensure(generated.count(returned) == 1, "packet regression lost the returned view assignment")
        for change, expected in (
            ("if (out->ok.PayloadView.length == 4UL) out->ok.PayloadView.ptr = pkt->ptr + 4UL;", 6),
            ("if (out->ok.PayloadView.length == 2UL) out->ok.PayloadView.perm_write = 1;", 10),
        ):
            check_program(generated.replace(returned, returned + "\n    " + change), expected)
        for expected, _ in holdfast_first_slice.PERTURBED_CASES:
            perturbed, _ = holdfast_first_slice.lower_to_c(source, parsed, checked=checked, perturb_check=expected)
            check_program(perturbed, expected)


def _check_packet_statements(statements: str, start: bytes = b"    var u8 acc = 0x5A ^ rawLen;",
                             *, replace: bool = False) -> None:
    root = TOOLS.parent
    original = (root / holdfast_first_slice.EXAMPLE).read_bytes()
    ensure(original.count(start) == 1, "checksum regression fixture lost its insertion point")
    source = original.replace(start, statements.encode() if replace else statements.encode() + start)
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, source, surface=True)
    checked = holdfast_elaborate.elaborate(source, parsed)
    ensure(not solver_ledger.ledger(checked.gallina), "inserted checksum statements changed the proved contract")
    operations: list[dict[str, object]] = []
    generated, _ = holdfast_first_slice.lower_to_c(source, parsed, checked=checked, observations=operations)
    observed_widths = {row["width"] for row in operations if row["kind"] == "nat"}
    ensure({"u8", "usize"} <= observed_widths, "lowering provenance omitted one of the packet literal widths")
    if "+=" in statements:
        ensure(any(row["kind"] == "assignment" and row["operation"] == "+" and row["width"] == "u8"
                   and "+=" in source[slice(*cast("list[int]", row["span"]))].decode()
                   and str(row["c_expression"]) in generated for row in operations),
               "compound addition did not retain its source, checked width and emitted C")
    with tempfile.TemporaryDirectory() as temporary:
        executable = Path(temporary) / "packet"
        for optimization in ("-O0", "-O2"):
            subprocess.run(["cc", "-std=c11", optimization, "-x", "c", "-", "-o", str(executable)],
                           input=generated.encode(), check=True, timeout=30)
            ensure(subprocess.run([str(executable)], check=False, timeout=5).returncode == 0,
                   f"lowered checksum statements changed the packet verdict at {optimization}")


def _packet_word_xor() -> None:
    _check_packet_statements(
        "    let high = 256usize ^ 0usize;\n"
        "    if (high == 0usize) { return 0u8; }\n"
    )


def _packet_complement_widening() -> None:
    _check_packet_statements(
        "    let inverted = usize.From(~0u8);\n"
        "    if (inverted != 255usize) { return 0u8; }\n"
    )


def _packet_compound_updates() -> None:
    _check_packet_statements(
        "    var u8 probe = 1u8;\n"
        "    probe += 1u8;\n"
        "    if (probe == 1u8) { return 0u8; }\n"
    )
    _check_packet_statements(
        "    pkt[0usize] = 1u8;\n"
        "    pkt[0usize] += 1u8;\n"
        "    if (pkt[0usize] != 2u8) { return; }\n",
        b"    pkt[0usize] = b0;",
    )


def _packet_affine_index_and_neutral_update() -> None:
    _check_packet_statements(
        "            acc = acc ^ pkt[i + 4usize];\n            acc += 0u8;",
        b"            acc = acc ^ pkt[4usize + i];",
        replace=True,
    )


def _packet_contextual_literals() -> None:
    root = TOOLS.parent
    source = (root / "examples/first_slice.hf").read_bytes()
    explicit = source
    for inferred, suffixed in (
        (b"magic = pkt[0];", b"magic = pkt[0usize];"),
        (b"magic != 0x56 ||", b"magic != 0x56u8 ||"),
        (b"0..4usize", b"0usize..4usize"),
        (b"0x5A ^ rawLen", b"0x5Au8 ^ rawLen"),
        (b"Span.Fill(ref dst, 0, 8, 0x00)", b"Span.Fill(ref dst, 0usize, 8usize, 0x00u8)"),
    ):
        ensure(inferred in explicit, f"missing contextual packet example {inferred!r}")
        explicit = explicit.replace(inferred, suffixed)

    outputs: list[tuple[str, str, int]] = []
    with parser.cached_build(root) as compiled:
        for variant in (source, explicit):
            parsed = parser.parse_source(compiled, variant, surface=True)
            checked = holdfast_elaborate.elaborate(variant, parsed)
            generated, checks = holdfast_first_slice.lower_to_c(variant, parsed, checked=checked)
            outputs.append((checked.gallina.replace(checked.source_sha256, "SOURCE"),
                            generated.replace(checked.source_sha256, "SOURCE"), checks))
        parsed = parser.parse_source(compiled, source, surface=True)
        checked = holdfast_elaborate.elaborate(source, parsed)
        generated, count = holdfast_first_slice.lower_to_c(source, parsed)
        ensure(count == 20 and generated != holdfast_first_slice.lower_to_c(source, parsed, checked=checked, perturb_check=7)[0],
               "kernel-subject packet failed to emit the behavioral harness and its seventh perturbation")
        ensure("holdfast_span_restore(dst, dst, &payloadView);" in generated and "CopyPacketToDst(" in generated,
               "checked lowering lost the mutating helper or the inferred restoration")

        stale = copy.deepcopy(parsed)
        declarations = holdfast_first_slice._extract_decl_map(stale)
        body = cast("Node", declarations["ComputePacketChecksum"]["body"])
        statements = cast("list[Node]", body["statements"])
        statements.pop(0)
        with raises(ValueError,
                    msg="checked facts for the original tree admitted a substituted function body") as raised:
            holdfast_first_slice.lower_to_c(source, stale, checked=checked)
        ensure("different source or syntax" in str(raised.exception), "substituted syntax lost its diagnostic")

        explicit_source = bytearray(source)
        for start, width in sorted(checked.contextual_literal_types.items(), reverse=True):
            literal = re.match(rb"(?:0[xX][0-9A-Fa-f_]+|0[bB][01_]+|[0-9][0-9_]*)", source[start:])
            if literal is None:
                raise AssertionError("checked literal offset did not identify a numeral")
            end = start + literal.end()
            explicit_source[end:end] = width.encode()
        invalid = bytes(explicit_source).replace(b"acc = acc ^ pkt[4usize + i];", b"acc = true;")
        ensure(invalid != explicit_source, "missing fully suffixed source neighbor")
        parsed = parser.parse_source(compiled, invalid, surface=True)
        with raises(HoldFastError, msg="fully suffixed source bypassed semantic checking") as raised:
            holdfast_first_slice.lower_to_c(invalid, parsed)
        error = raised.exception
        ensure(error.kind == "type", f"fully suffixed program lost its type error: {error}")
        for replaced, replacement, message in (
            (b"magic != 0x56 ||", b"magic != 256 ||", "out of range for 'u8'"),
            (b"magic = pkt[0];", b"magic = pkt[0u8];", "not definitionally equal"),
        ):
            bad = source.replace(replaced, replacement)
            parsed = parser.parse_source(compiled, bad, surface=True)
            with raises(HoldFastError, msg=f"packet lowering accepted {replacement!r}") as raised:
                holdfast_first_slice.lower_to_c(bad, parsed)
            error = raised.exception
            ensure(error.kind == "type" and message in error.message, f"unexpected literal error: {error}")
        untyped = source.replace(b"let magic = pkt[0];", b"let count = 0; let magic = pkt[0];")
        parsed = parser.parse_source(compiled, untyped, surface=True)
        with raises(ValueError,
                    msg="packet lowering assigned an implicit runtime width to a Nat local") as raised:
            holdfast_first_slice.lower_to_c(untyped, parsed)
        error = raised.exception
        ensure("requires an explicit type annotation or suffix" in str(error), f"unexpected width error: {error}")

    ensure(outputs[0] == outputs[1], "contextual literals changed the packet proof terms, C body or checks")
    _, generated, _ = outputs[0]
    ensure("magic = holdfast_span_read(pkt, 0UL);" in generated and "(magic != 0x56U)" in generated,
           "packet lowering lost contextual index or byte widths")


def cases() -> list[Case]:
    return [
        Case("capacity-invariance-and-restores-ensures-obligations", _capacity_invariance_and_contracts),
        Case("semantic-negative-span-refusals", _negative_span_refusals),
        Case("ordered-scalar-calls-under-short-circuit", _ordered_scalar_calls),
        Case("clight-lowering-and-purecap-cheri-assembly", _clight_lowering_and_purecap_assembly),
        Case("purecap-profile-checks-the-untaken-error-branch", _purecap_error_branch_profile),
        Case("first-slice-constructive-source-proofs-with-fixed-budgets", _first_slice_source_proofs, lane="guest"),
        Case("first-slice-mathematical-and-executable-recursion", _first_slice_recursion_boundary, lane="guest"),
        Case("execute-generated-packet-c-and-perturbed-scenarios", _execute_generated_packet_c, lane="guest"),
        Case("packet-word-xor-retains-high-bits", _packet_word_xor, lane="guest"),
        Case("packet-byte-complement-before-widening", _packet_complement_widening, lane="guest"),
        Case("packet-compound-updates-read-before-writing", _packet_compound_updates, lane="guest"),
        Case("packet-affine-index-and-neutral-accumulator", _packet_affine_index_and_neutral_update, lane="guest"),
        Case("packet-contextual-literals-match-explicit-representations", _packet_contextual_literals, lane="guest"),
    ]
