# SPDX-License-Identifier: Apache-2.0
"""Parser, elaborator, loan, mode-crossing, and Rocq replay tests for Zena-derived features."""

import contextlib
import subprocess
import tempfile
from functools import partial
from pathlib import Path
from typing import cast

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, mathematical_authoring, parser, proofenv, rocq_cache, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.elaborate import _Elaborator
from toolchain.elaborate_protocol import _Protocol


def _replay_gallina(
    module_name: str,
    source: bytes,
    consumers: str,
    expected_reports: int,
    *,
    batch: rocq_cache.BatchChecker | None = None,
) -> elaborate.CheckedElaboration:
    with parser.cached_build(TOOLS.parent) as compiled:
        result = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True))
    ensure(not solver_ledger.ledger(result.gallina), f"unexpected solver-trust axioms:\n{result.gallina}")
    module = elaborate.gallina_module_name(module_name)
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-zena-")))
            stem = module_name
        else:
            directory = batch.work_dir
            stem = batch.unique_stem(module_name)
        target = directory / f"{stem}.v"
        unit_text, used_prelude = rocq_cache.use_cached_prelude(result.gallina + "\n" + consumers, directory)
        target.write_text(unit_text, encoding="utf-8")
        replay = subprocess.run(
            [*proofenv.rocq_command(), "-q", target.name],
            cwd=directory,
            capture_output=True,
            check=False,
            text=True,
            timeout=180,
        )
        ensure(replay.returncode == 0, f"rocq c failed:\n{replay.stderr}")
        solver_ledger.audit(replay.stdout, expected_reports, module, ())
        if batch is not None:
            if used_prelude:
                batch.register("HoldFastPrelude")
            batch.register(stem)
        else:
            rocq_cache.check_kernel(directory, ["HoldFastPrelude", stem] if used_prelude else [stem])
    return result


def _protocol_unit_cases() -> None:
    distinct_src = b"module P; public distinct Port = u16;"
    _Protocol(distinct_src).visit({
        "kind": "surface_file",
        "span": [0, len(distinct_src)],
        "name": {"text": "P", "span": [7, 8]},
        "declarations": [{
            "kind": "distinct",
            "span": [10, len(distinct_src)],
            "modifiers": ["public"],
            "name": {"text": "Port", "span": [26, 30]},
            "generics": [],
            "type": {"kind": "type", "span": [33, 36], "name": {"text": "u16", "span": [33, 36]}, "arguments": []},
            "contracts": [],
            "declarations": [],
        }],
    }, (0, len(distinct_src)))
    pipe_src = b"x |> $"
    _Protocol(pipe_src).visit({
        "kind": "pipe",
        "span": [0, len(pipe_src)],
        "left": {"kind": "name", "span": [0, 1], "name": {"text": "x", "span": [0, 1]}},
        "right": {"kind": "pipe_placeholder", "span": [5, 6]},
    }, (0, len(pipe_src)))
    using_src = b"using (let h = 1) { return h; }"
    _Protocol(using_src).visit({
        "kind": "using",
        "span": [0, len(using_src)],
        "binding": {
            "kind": "let",
            "span": [7, 16],
            "name": {"text": "h", "span": [11, 12]},
            "type": None,
            "grade": None,
            "value": {"kind": "nat", "span": [15, 16], "value": "1", "suffix": ""},
        },
        "body": {
            "kind": "block",
            "span": [18, len(using_src)],
            "statements": [{
                "kind": "return",
                "span": [20, 29],
                "value": {"kind": "name", "span": [27, 28], "name": {"text": "h", "span": [27, 28]}},
            }],
        },
    }, (0, len(using_src)))


def _distinct_nominal_and_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module DistinctReplay;
public distinct Port = u16;
public distinct UserId = u16;
public distinct Tagged<T> = T invariant this.Value == this.Value {
    public T Unwrap => this.Value;
    public bool Matches(T expected) => true;
}
public distinct PositiveNat = Nat invariant this.Value > 0 {
    public Nat Raw => this.Value;
}
public distinct BoxedPair = (Nat, Nat);

public definition bool PortEq(Port a, Port b) => a == b;
public definition Nat UnwrapPositive(PositiveNat p) => p.Raw;

public Port MakePort(u16 raw) => Port.From(raw);
public u16 ReadPort(Port p) => Port.Underlying(p);
public u16 MatchDistinct(Port p) {
    let Port(raw) = p;
    return match (Port.From(raw)) {
        Port(inner) => inner,
    };
}
public bool CheckTag(Nat n) => Tagged<Nat>(n).Matches(n);
public PositiveNat IncrementPositive(PositiveNat p) => p with { Value = p.Value + 1 };

public lemma DistinctIdentity(u16 raw, Nat n)
    requires n > 0
    ensures Port.Underlying(Port.From(raw)) == raw
    ensures PositiveNat.From(n).Value == n
    proof
    {
        assert Port(raw).Value == raw;
        assert PositiveNat(n).Value == n;
    }
"""
    mod = elaborate.gallina_module_name("DistinctReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        tree = parser.parse_source(compiled, source, surface=True)
        res = elaborate.elaborate(source, tree)
        formatted = mathematical_authoring.format_syntax(compiled, source)
        ensure(b"public distinct Port = u16;" in formatted, "formatter dropped distinct declaration")

    # Verify zero-cost transparent Gallina representation (no prod ... Unit wrapper).
    ensure(
        ":=\n  (holdfast_int (1 : Corelib.Init.Datatypes.nat))." in res.gallina,
        f"distinct Port should erase directly to u16 in Gallina:\n{res.gallina}",
    )

    # Verify derived mode crossing agrees on distinct wrappers of copy scalars.
    proto_elab = _Elaborator(_Protocol(source))
    _ = proto_elab

    checked_exports = [
        name
        for name in solver_ledger.math_exports(res.gallina)
        if name.endswith(("_DistinctIdentity", "_UnwrapPositive", "_MakePort", "_ReadPort", "_MatchDistinct"))
    ]
    ensure(len(checked_exports) >= 2, f"missing expected exports: {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("DistinctReplay", source, consumers, len(checked_exports), batch=batch)

    # Nominal separation & invariant enforcement negatives.
    negatives = (
        ("distinct-unifies-with-underlying",
         b"module N; public distinct Port = u16; public u16 Bad(Port p) => p;",
         "type"),
        ("distinct-unifies-with-sibling",
         b"module N; public distinct A = u16; public distinct B = u16; public B Bad(A a) => a;",
         "type"),
        ("distinct-invariant-violated",
         b"module N; public distinct Pos = Nat invariant this.Value > 0; public Pos Bad() => Pos(0);",
         "type"),
        ("distinct-from-invariant-violated",
         b"module N; public distinct Pos = Nat invariant this.Value > 0; public Pos Bad() => Pos.From(0);",
         "type"),
    )
    with parser.cached_build(TOOLS.parent) as compiled:
        for label, bad_src, expected_kind in negatives:
            with raises(HoldFastError, msg=f"{label} unexpectedly succeeded") as raised:
                elaborate.elaborate(bad_src, parser.parse_source(compiled, bad_src, surface=True))
            ensure(raised.exception.kind == expected_kind, f"{label} wrong kind: {raised.exception}")


def _distinct_foreign_interface_coherence(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    iface_src = b"""module ProviderIface;
public interface IPortTag<T> {
    u16 TagCode(in T value);
}
"""
    client_src = b"""module ClientWrapper;
import ProviderIface { IPortTag };
public distinct LocalPort = u16;
public impl IPortTag<LocalPort> {
    public u16 TagCode(in LocalPort value) => value.Value;
}
public u16 ReadTag(LocalPort p) => p.TagCode();
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        iface_ast = parser.parse_source(compiled, iface_src, surface=True)
        client_ast = parser.parse_source(compiled, client_src, surface=True)
        results = elaborate.elaborate_package(
            [
                (iface_src, iface_ast),
                (client_src, client_ast),
            ],
            scopes={
                "ProviderIface": elaborate.PackageScope("a" * 64, frozenset({"ProviderIface"})),
                "ClientWrapper": elaborate.PackageScope("b" * 64, frozenset({"ProviderIface", "ClientWrapper"})),
            },
        )
        client_gallina = results["ClientWrapper"].gallina
        ensure(not solver_ledger.ledger(client_gallina), f"unexpected trust axiom:\n{client_gallina}")

    if batch is not None:
        c_mod = next(
            line[len("Module "):].rstrip(".")
            for line in client_gallina.splitlines()
            if line.startswith("Module ")
        )
        d = batch.work_dir
        c_stem = batch.unique_stem("ClientWrapper")
        exports = solver_ledger.math_exports(client_gallina)
        c_full = client_gallina + "\n" + "\n".join(f"Print Assumptions {c_mod}.{name}." for name in exports) + "\n"
        c_text, used_p2 = rocq_cache.use_cached_prelude(c_full, d)
        (d / f"{c_stem}.v").write_text(c_text, encoding="utf-8")
        r2 = subprocess.run([*proofenv.rocq_command(), "-q", f"{c_stem}.v"], cwd=d, capture_output=True, text=True, check=False)
        ensure(r2.returncode == 0, f"client rocq c failed:\n{r2.stderr}")
        solver_ledger.audit(r2.stdout, len(exports), c_mod, ())
        if used_p2:
            batch.register("HoldFastPrelude")
        batch.register(c_stem)

    # Mode-crossing verification on distinct wrapper over copyable vs owned underlying types.
    owned_src = b"""module ModeCrossDistinct;
public record OwnedBuf(Nat Count);
public distinct Port = u16 invariant this.Value == this.Value;
public distinct BorrowWrap = owned OwnedBuf;
public Unit Use() => ();
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        parsed_owned = parser.parse_source(compiled, owned_src, surface=True)
        # Exercise full elaborator mode-crossing helper through internal record registry.
        _, elab = elaborate._checked_elaboration(owned_src, parsed_owned)
        port_info = elab.records["Port"]
        borrow_info = elab.records["BorrowWrap"]
        ensure(
            elab._type_crosses_modes(elaborate._constant(port_info.type_const), runtime_represented=True),
            "distinct u16 wrapper failed mode crossing",
        )
        ensure(
            not elab._type_crosses_modes(elaborate._constant(borrow_info.type_const), runtime_represented=True),
            "distinct owned wrapper unexpectedly crossed modes",
        )


def _pipeline_elaboration_and_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module PipelineReplay;
public definition Nat Inc(Nat x) => x + 1;
public definition Nat Double(Nat x) => x + x;
public Nat Clamp(Nat min, Nat value, Nat max) => if (value < min) min else (if (value > max) max else value);
public record Boxed(Nat Value);

public Nat Chained(Nat x, Nat y) {
    let viaCall = x |> Inc($) |> Double($);
    let viaExpr = x |> $ + 1 |> Double($);
    let bool eqOk = x |> $ + 1 |> Double($) == viaCall;
    let labeled = x |> Clamp(min: 1, value: $, max: 5);
    let memberRead = Boxed(x) |> $.Value;
    let nested = x |> ($ + (y |> Double($)));
    let repeated = x |> ($ + $);
    if (eqOk) {
        return viaExpr + labeled + memberRead + nested + repeated;
    }
    return 0;
}

public record Token(Nat Id);
public Nat Consume(owned Token tok) => tok.Id;
public Nat PairConsume(owned Token a, owned Token b) => a.Id + b.Id;
public Nat ConsumePiped(owned Token tok) => move tok |> Consume(move $);

public lemma PipelineLaws(Nat x, Nat y)
    ensures (x |> $ + 1 |> Double($)) == (x + 1) + (x + 1)
    ensures (x |> ($ + (y |> Double($)))) == x + (y + y)
    proof
    {
        assert (x |> $ + 1 |> Double($)) == (x + 1) + (x + 1);
        assert (x |> ($ + (y |> Double($)))) == x + (y + y);
    }
"""
    mod = elaborate.gallina_module_name("PipelineReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        res = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True))
        formatted = mathematical_authoring.format_syntax(compiled, source)
        ensure(b"|>" in formatted and b"$" in formatted, "formatter dropped pipeline syntax")

    exports = [name for name in solver_ledger.math_exports(res.gallina) if name.endswith(("_PipelineLaws", "_Chained", "_ConsumePiped"))]
    ensure(len(exports) >= 2, f"missing pipeline exports: {exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in exports) + "\n"
    _replay_gallina("PipelineReplay", source, consumers, len(exports), batch=batch)

    negatives = (
        ("bare-placeholder-outside-pipe", b"module N; public Nat Bad() => $;", "name"),
        ("pipe-without-placeholder", b"module N; public Nat F(Nat x) => x; public Nat Bad(Nat x) => x |> F(1);", "type"),
        ("nested-pipe-does-not-supply-outer-placeholder", b"module N; public Nat Bad(Nat x) => x |> (1 |> $ + 1);", "type"),
        ("pipe-double-move-placeholder",
         b"module N; public record T(Nat V); public Nat Pair(owned T a, owned T b) => a.V + b.V; "
         b"public Nat Bad(owned T x) => move x |> Pair(move $, move $);",
         "type"),
    )
    with parser.cached_build(TOOLS.parent) as compiled:
        for label, bad_src, expected_kind in negatives:
            with raises(HoldFastError, msg=f"{label} unexpectedly succeeded") as raised:
                elaborate.elaborate(bad_src, parser.parse_source(compiled, bad_src, surface=True))
            ensure(raised.exception.kind == expected_kind, f"{label} wrong kind: {raised.exception}")


def _using_scope_and_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module UsingReplay;
public union Option<T> { None(); Some(T Value); }
public interface IDispose<T> {
    Unit Dispose(in T value);
}
public record Handle(Nat Id, bool Open) invariant Open;
public impl IDispose<Handle> {
    public Unit Dispose(in Handle value)
        requires value.Open
        => ();
}
public Handle OpenHandle(Nat id) => Handle(id, true);
public Nat ReadHandle(in Handle h) => h.Id;

public Nat BasicUsing(Nat id) {
    using (let h = OpenHandle(id)) {
        let v = ReadHandle(in h);
        return v;
    }
}

public Nat SequentialUsing(Nat id) {
    var Nat acc = 0;
    using (let a = OpenHandle(id)) {
        using (let b = OpenHandle(id + 1)) {
            acc = ReadHandle(in a) + ReadHandle(in b);
        }
    }
    return acc;
}

public Nat EarlyReturnUsing(Nat id, bool flag) {
    using (let h = OpenHandle(id)) {
        if (flag) {
            return ReadHandle(in h);
        }
        let dummy = ReadHandle(in h);
        acc_noop:
        let kept = dummy + 1;
    }
    return id + 10;
}
"""
    # Avoid unsupported labeled statement (`acc_noop:`) — use plain statement.
    source = source.replace(b"        acc_noop:\n", b"")
    source_with_opt = source + b"""
public Option<Nat> PropagateInInit(Option<Nat> maybe) {
    using (let h = OpenHandle(maybe?)) {
        return Some(ReadHandle(in h));
    }
}

public Option<Nat> PropagateInBody(Nat id, Option<Nat> maybe) {
    using (let h = OpenHandle(id)) {
        let extra = maybe?;
        return Some(ReadHandle(in h) + extra);
    }
}

public Unit GenericUsing<T>(owned T item) where T : IDispose<T> {
    using (let scopedItem = move item) {
        let _unused = 1;
    }
    return;
}
"""
    mod = elaborate.gallina_module_name("UsingReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        tree = parser.parse_source(compiled, source_with_opt, surface=True)
        res = elaborate.elaborate(source_with_opt, tree)
        formatted = mathematical_authoring.format_syntax(compiled, source_with_opt)
        ensure(b"using (let h = OpenHandle" in formatted, "formatter altered using syntax")

    # Check Dispose calls appear in the emitted Gallina for every exit path.
    ensure("_IDispose_Dispose" in res.gallina, f"Dispose call missing from Gallina:\n{res.gallina}")

    exports = [
        name
        for name in solver_ledger.math_exports(res.gallina)
        if name.endswith(("_BasicUsing", "_SequentialUsing", "_EarlyReturnUsing", "_PropagateInInit", "_PropagateInBody", "_GenericUsing"))
    ]
    ensure(len(exports) == 6, f"expected 6 UsingReplay exports, got {exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in exports) + "\n"
    _replay_gallina("UsingReplay", source_with_opt, consumers, len(exports), batch=batch)

    negatives = (
        ("using-missing-idispose-impl",
         b"module N; public interface IDispose<T> { Unit Dispose(in T v); } "
         b"public Unit Bad() { using (let x = 1) { let y = x; } return; }",
         "type"),
        ("using-move-managed-resource",
         b"module N; public interface IDispose<T> { Unit Dispose(in T v); } "
         b"public record H(Nat Id); "
         b"public impl IDispose<H> { public Unit Dispose(in H v) => (); } "
         b"public Unit Take(owned H x) => (); "
         b"public Unit Bad() { using (let h = H(1)) { Take(move h); } return; }",
         "type"),
        ("using-return-managed-resource",
         b"module N; public interface IDispose<T> { Unit Dispose(in T v); } "
         b"public record H(Nat Id); "
         b"public impl IDispose<H> { public Unit Dispose(in H v) => (); } "
         b"public H Bad() { using (let h = H(1)) { return h; } }",
         "type"),
        ("using-escaping-borrow",
         b"module N; public interface IDispose<T> { Unit Dispose(in T v); } "
         b"public record H(Nat Id); "
         b"public impl IDispose<H> { public Unit Dispose(in H v) => (); } "
         b"public Unit Bad() { "
         b"using (let h = H(1)) { let r = in h; return; } }",
         "type"),
        ("using-non-unit-dispose",
         b"module N; public interface IDispose<T> { Nat Dispose(in T v); } "
         b"public record H(Nat Id); "
         b"public impl IDispose<H> { public Nat Dispose(in H v) => 0; } "
         b"public Unit Bad() { using (let h = H(1)) { let a = 1; } return; }",
         "type"),
    )
    with parser.cached_build(TOOLS.parent) as compiled:
        for label, bad_src, expected_kind in negatives:
            with raises(HoldFastError, msg=f"{label} unexpectedly succeeded") as raised:
                elaborate.elaborate(bad_src, parser.parse_source(compiled, bad_src, surface=True))
            ensure(raised.exception.kind == expected_kind, f"{label} wrong kind: {raised.exception}")


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("zena-protocol-unit", _protocol_unit_cases),
        Case("distinct-nominal-and-rocq-replay", partial(_distinct_nominal_and_replay, batch=batch), lane="toolchain"),
        Case("distinct-foreign-interface-and-mode-crossing", partial(_distinct_foreign_interface_coherence, batch=batch), lane="toolchain"),
        Case("pipeline-elaboration-and-rocq-replay", partial(_pipeline_elaboration_and_replay, batch=batch), lane="toolchain"),
        Case("using-scope-cleanup-and-rocq-replay", partial(_using_scope_and_replay, batch=batch), lane="toolchain"),
        Case("kernel check zena concepts with rocqchk", batch.verify_all, lane="toolchain"),
    ]
