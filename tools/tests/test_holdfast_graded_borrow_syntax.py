# SPDX-License-Identifier: Apache-2.0
"""Verify graded patterns/motives/loops, shared ref borrows, FnMut/FnOnce, and GAT syntax."""

import copy
from pathlib import Path
from typing import cast

from tests.harness import Case, ensure, raises
from toolchain import HoldFastError, parser, surface
from toolchain import syntax_campaigns as campaigns
from toolchain.elaborate_protocol import _Protocol, syntax_nodes
from toolchain.elaborate_types import Node

ROOT = Path(__file__).resolve().parents[2]


def _parse_surface(compiled: parser.Build, source: bytes, *, protocol: bool = True) -> dict[str, parser.Json]:
    result = parser.parse_source(compiled, source, surface=True)
    if protocol:
        _Protocol(source).decode(result)
    return result


def _nodes(tree: object, kind: str) -> list[Node]:
    return [
        node
        for node in syntax_nodes(cast("Node", tree))
        if node.get("kind") == kind
    ]


def _span_bytes(source: bytes, node: Node) -> bytes:
    raw_span = node["span"]
    if not isinstance(raw_span, list) or len(raw_span) != 2:
        raise TypeError(f"invalid span: {raw_span!r}")
    start, end = raw_span
    if not isinstance(start, int) or not isinstance(end, int):
        raise TypeError(f"invalid span indices: {raw_span!r}")
    return source[start:end]


def _node_name_text(node: Node) -> str:
    raw_name = node["name"]
    if not isinstance(raw_name, dict):
        raise TypeError(f"expected dict name, got {raw_name!r}")
    text = raw_name["text"]
    if not isinstance(text, str):
        raise TypeError(f"expected str name text, got {text!r}")
    return text


def _graded_patterns_motives_and_loops() -> None:
    source = b"""module GradedSyntax;
public Nat Check(
    Nat p1 @ (s, r),
    Nat p2 @ q + r,
    Nat p3 @ q * r,
    Nat p4 @ _,
    Nat p5 @ Domain(s, r),
    Box<Nat> box,
    Pair<Nat, Nat> pair,
    Vec<Nat, 4> vec,
) {
    let Nat a @ (s, r) = 1;
    let Nat b @ q + r = 1;
    let Nat c @ q * r = 1;
    let Nat d @ _ = 1;
    let Nat e @ Domain(s, r) = 1;
    let f = (Nat l1 @ (s, r), Nat l2 @ q + r, Nat l3 @ q * r, Nat l4 @ _, Nat l5 @ Domain(s, r)) => l1;
    let g = (u1 @ (s, r), u2 @ q + r, u3 @ q * r, u4 @ _, u5 @ Domain(s, r)) => u1;
    let Box(localBound @ q) = box;
    var Pair(varLeft @ s, varRight @ r) = pair;
    let (tupA @ (s, r), tupB @ Domain(s, r)) = pair;
    foreach (let item @ q in vec) {
        Inspect(item);
    }
    foreach (let byte typedItem @ q + r in vec) {
        Inspect(typedItem);
    }
    foreach (in byte inItem @ q * r in vec) {
        Inspect(inItem);
    }
    foreach (ref byte refItem @ Domain(s, r) in vec) {
        Inspect(refItem);
    }
    foreach (let idx @ q in 0..4) {
        Inspect(idx);
    }
    foreach (let idxWild @ _ in 0..4) {
        Inspect(idxWild);
    }
    foreach (let plain in vec) {
        Inspect(plain);
    }
    foreach (let plainRange in 0..4) {
        Inspect(plainRange);
    }
    let exprMatch = match (box) as whole @ k : Nat {
        Box(inner @ q) => inner,
    };
    let tupleMatch = match (pair) {
        Pair(px @ s, py @ s) => px,
    };
    let bareMatch = match (a) {
        patA @ (s, r) => patA,
    };
    match (box) as stmtWhole @ (s, r) : Unit {
        Box(stmtInner @ Domain(s, r)) => return stmtInner;
    }
    let emptyMatch = (match (box) as emptyWhole @ _ : Nat {});
    let plainMotive = match (box) as plainWhole : Nat {
        Box(plainInner) => plainInner,
    };
    if (box is Box(isInner @ q) && a is isBare @ q + r && true) {
        return exprMatch;
    }
    return tupleMatch;
}
"""
    struct_source = b"""module GradedStructFields;
public struct GradedStruct<grade s : NatExact, grade r : NatExact, grade q : NatExact> {
    Nat f1 @ (s, r);
    Nat f2 @ q + r;
    Nat f3 @ q * r;
    Nat f4 @ _;
    Nat f5 @ Domain(s, r);
}
"""
    with parser.cached_build(ROOT) as compiled:
        result = _parse_surface(compiled, source)
        struct_result = _parse_surface(compiled, struct_source, protocol=False)
    ast = result["ast"]
    fields = {_node_name_text(node): node for node in _nodes(struct_result["ast"], "field")}
    for fname, expected_bytes in (
        ("f1", b"Nat f1 @ (s, r);"),
        ("f2", b"Nat f2 @ q + r;"),
        ("f3", b"Nat f3 @ q * r;"),
        ("f4", b"Nat f4 @ _;"),
        ("f5", b"Nat f5 @ Domain(s, r);"),
    ):
        ensure(fname in fields and _span_bytes(struct_source, fields[fname]) == expected_bytes,
               f"wrong graded struct field span for {fname}")

    # Pattern binders with and without grades
    binders = {_node_name_text(node): node for node in _nodes(ast, "binding_pattern")}
    for name, expected_bytes in (
        ("localBound", b"localBound @ q"),
        ("varLeft", b"varLeft @ s"),
        ("varRight", b"varRight @ r"),
        ("tupA", b"tupA @ (s, r)"),
        ("tupB", b"tupB @ Domain(s, r)"),
        ("inner", b"inner @ q"),
        ("px", b"px @ s"),
        ("py", b"py @ s"),
        ("patA", b"patA @ (s, r)"),
        ("stmtInner", b"stmtInner @ Domain(s, r)"),
        ("isInner", b"isInner @ q"),
        ("isBare", b"isBare @ q + r"),
    ):
        ensure(name in binders and "grade" in binders[name], f"missing graded binding_pattern for {name}")
        ensure(_span_bytes(source, binders[name]) == expected_bytes, f"wrong span for {name}")
    ensure("plainInner" in binders and "grade" not in binders["plainInner"],
           "ungraded binding_pattern should omit 'grade' for backward compatibility")

    # Match motives with and without grades
    motives = {_node_name_text(node): node for node in _nodes(ast, "match_motive")}
    ensure(_span_bytes(source, motives["whole"]) == b"as whole @ k : Nat", "wrong graded expression motive span")
    ensure(_span_bytes(source, motives["stmtWhole"]) == b"as stmtWhole @ (s, r) : Unit", "wrong graded statement motive span")
    ensure(_span_bytes(source, motives["emptyWhole"]) == b"as emptyWhole @ _ : Nat", "wrong graded empty motive span")
    ensure("grade" not in motives["plainWhole"], "ungraded match_motive should omit 'grade'")

    # Foreach and foreach_collection with and without grades
    colls = {_node_name_text(node): node for node in _nodes(ast, "foreach_collection")}
    ranges = {_node_name_text(node): node for node in _nodes(ast, "foreach")}
    for name in ("item", "typedItem", "inItem", "refItem"):
        ensure("grade" in colls[name], f"foreach_collection {name} missing grade")
    for name in ("idx", "idxWild"):
        ensure("grade" in ranges[name], f"foreach {name} missing grade")
    ensure("grade" not in colls["plain"], "ungraded foreach_collection should omit 'grade'")
    ensure("grade" not in ranges["plainRange"], "ungraded foreach should omit 'grade'")

    # Protocol tamper checks for new optional grade fields
    for kind in ("binding_pattern", "match_motive", "foreach", "foreach_collection"):
        tampered = copy.deepcopy(result)
        target = next(n for n in _nodes(tampered["ast"], kind) if "grade" in n)
        target["grade"] = {"kind": "name", "span": [0, 1], "name": {"text": "x", "span": [0, 1]}}
        with raises(HoldFastError, msg=f"forged {kind} grade escaped _Protocol") as raised:
            _Protocol(source).decode(tampered)
        ensure(raised.exception.kind == "protocol", f"wrong error kind for forged {kind} grade")


def _shared_ref_fnmut_fnonce_and_gats() -> None:
    source = b"""module SharedRefAndGats;
public interface LendingIterator<Self> {
    type Item<region 'next>;
    type Plain;
    shared ref<'next> Self.Item<'next> Next<region 'next>(ref<'next> Self self);
}
public impl<T> LendingIterator<SliceIter<T>> {
    type Item<region 'next> = ref<'next> byte;
    type SharedItem<region 'next> = shared ref<'next> T;
    type Plain = T;
}
alias MutCallback<T> = FnMut<region 'a>(shared ref<'a> T item @ q) -> shared ref<'a> byte;
alias OnceCallback<T> = FnOnce<region 'a>(owned T item, shared ref<'a> byte slot) -> Unit;
alias PlainMut = FnMut(shared ref byte) -> Unit;
public shared ref<'a> byte UseSharedRef<region 'a>(
    shared ref<'a> Vec<byte, 4> vec,
    shared ref byte plainVec,
    Nat shared,
) {
    let x = shared ref vec;
    let y = shared ref vec[0];
    let z = shared /* comment */ ref vec[shared];
    let shared ref<'a> byte typed = shared ref vec[0];
    let shared ref byte untagged = shared ref plainVec;
    let shared ref<'a> byte graded @ (s, r) = shared ref vec[0];
    let cb = (shared ref<'a> byte param @ q) => param;
    let mutLambda = FnMut<region 'b>(shared ref<'b> byte slot) -> Unit => { return; };
    let onceLambda = FnOnce<region 'b>(owned byte val, shared ref<'b> byte slot) -> Unit => { return; };
    let sharedVar = 1;
    let Nat sharedTyped @ q = sharedVar;
    var shared = sharedVar + sharedTyped;
    shared = shared + 1;
    return typed;
}
"""
    with parser.cached_build(ROOT) as compiled:
        result = _parse_surface(compiled, source)
    ast = result["ast"]

    # Check shared_ref modified_type nodes
    mod_types = _nodes(ast, "modified_type")
    shared_mods = [node for node in mod_types if node.get("modifier") == "shared_ref"]
    ensure(len(shared_mods) >= 9, f"expected >= 9 shared_ref modified_type nodes, got {len(shared_mods)}")
    ensure(any(node.get("lifetime") is None for node in shared_mods), "expected unlifetimed shared ref type")
    ensure(any(node.get("lifetime") is not None for node in shared_mods), "expected lifetimed shared ref<'a> type")

    # Check shared_ref unary nodes
    unaries = sorted(
        (
            node for node in _nodes(ast, "unary")
            if isinstance(node["operator"], dict) and node["operator"].get("text") == "shared_ref"
        ),
        key=lambda node: cast("list[int]", node["span"])[0] if isinstance(node["span"], list) else 0,
    )
    ensure(len(unaries) == 6, f"expected 6 shared ref unary expressions, got {len(unaries)}")
    ensure(_span_bytes(source, unaries[0]) == b"shared ref vec", "wrong span for shared ref vec")
    ensure(_span_bytes(source, unaries[1]) == b"shared ref vec[0]", "wrong span for shared ref vec[0]")
    ensure(_span_bytes(source, unaries[2]) == b"shared /* comment */ ref vec[shared]",
           "wrong span for commented shared ref vec[shared]")

    # Check FnMut / FnOnce with region telescopes
    fn_types = _nodes(ast, "function_type")
    modes = {node["mode"] for node in fn_types if isinstance(node["mode"], str)}
    ensure({"FnMut", "FnOnce"} <= modes, f"missing FnMut/FnOnce modes: {modes}")
    for mode in ("FnMut", "FnOnce"):
        with_region = [
            node for node in fn_types
            if node.get("mode") == mode and isinstance(node["generics"], list) and len(node["generics"]) == 1
        ]
        ensure(bool(with_region), f"expected {mode}<region ...> function_type")

    # Check GAT associated_type in interface & impl
    assoc = _nodes(ast, "associated_type")
    ensure(len(assoc) == 5, f"expected 5 associated_type declarations, got {len(assoc)}")
    iface = _nodes(ast, "interface")[0]
    impl = _nodes(ast, "impl")[0]
    iface_item = next(n for n in _nodes(iface, "associated_type") if _node_name_text(n) == "Item")
    impl_item = next(n for n in _nodes(impl, "associated_type") if _node_name_text(n) == "Item")
    ensure(
        iface_item.get("definition") is None
        and isinstance(iface_item["generics"], list)
        and len(iface_item["generics"]) == 1,
        "interface GAT Item mismatch",
    )
    ensure(
        impl_item.get("definition") is not None
        and isinstance(impl_item["generics"], list)
        and len(impl_item["generics"]) == 1,
        "impl GAT Item mismatch",
    )

    # Forged shared_ref from literal 'shared_ref' identifier must fail protocol
    bad_source = b"module Bad; void F() { let x = shared_ref; }"
    with parser.cached_build(ROOT) as compiled:
        bad_res = parser.parse_source(compiled, bad_source, surface=True)
    bad_res_forged = copy.deepcopy(bad_res)
    let_node = _nodes(bad_res_forged["ast"], "let")[0]
    raw_name_expr = let_node["value"]
    if not isinstance(raw_name_expr, dict):
        raise TypeError(f"expected dict let value, got {raw_name_expr!r}")
    let_node["value"] = {
        "kind": "unary",
        "span": raw_name_expr["span"],
        "operator": raw_name_expr["name"],
        "value": raw_name_expr,
    }
    with raises(HoldFastError, msg="forged shared_ref unary escaped _Protocol") as raised:
        _Protocol(bad_source).decode(bad_res_forged)
    ensure(raised.exception.kind == "protocol", "wrong error kind for forged shared_ref")


def _refusals_and_surface_and_campaigns() -> None:
    refusals: tuple[tuple[bytes, str], ...] = (
        (b"module M; Nat F() => match (x) { None @ q => 0, };", "syntax"),
        (b"module M; Nat F() => match (x) { _ @ q => 0, };", "syntax"),
        (b"module M; Nat F() => match (x) { Box(y) @ q => 0, };", "syntax"),
        (b"module M; Nat F() => match (x) { Box(y @) => 0, };", "syntax"),
        (b"module M; Nat F() => match (x) as whole @ : Nat { _ => 0, };", "syntax"),
        (b"module M; void F() { foreach (let x @ in xs) {} }", "syntax"),
        (b"module M; void F() { let x = shared ref; }", "syntax"),
        (b"module M; void F(shared ref) {}", "syntax"),
        (b"module M; void F(shared T x) {}", "syntax"),
    )
    with parser.cached_build(ROOT) as compiled:
        for src, expected_kind in refusals:
            with raises(HoldFastError, msg=f"refusal unexpectedly parsed: {src!r}") as raised:
                parser.parse_source(compiled, src, surface=True)
            ensure(raised.exception.kind == expected_kind,
                   f"expected {expected_kind}, got {raised.exception.kind} for {src!r}")

        passed = surface.qualify(lambda raw: _parse_surface(compiled, raw, protocol=False))
        ensure("surface:graded-patterns-shared-ref-and-gats" in passed,
               "surface qualification omitted graded-patterns-shared-ref-and-gats")

    # Verify pure entry continues to treat 'shared' as an ordinary identifier
    pure_src = b"module SharedPure; public Nat Identity(Nat shared) { let x = shared; return x; }"
    pure_env = campaigns.IndependentPureAstOracle.parse(pure_src)
    ensure(pure_env["schema"] == 1, "pure oracle schema mismatch for 'shared' identifier")


def cases() -> list[Case]:
    return [
        Case("graded-patterns-motives-and-loops", _graded_patterns_motives_and_loops, lane="toolchain"),
        Case("shared-ref-fnmut-fnonce-and-gats", _shared_ref_fnmut_fnonce_and_gats, lane="toolchain"),
        Case("refusals-surface-and-pure-campaigns", _refusals_and_surface_and_campaigns, lane="toolchain"),
    ]
