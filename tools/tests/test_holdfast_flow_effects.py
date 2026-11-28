# SPDX-License-Identifier: Apache-2.0
"""Parser, elaborator, package policy, contract-diff, and Rocq 9.3.0 replay tests for Flow Effects."""

import contextlib
import json
import re
import subprocess
import tempfile
from functools import partial
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from tests.test_holdfast_elaboration_cli import _invoke
from tests.test_holdfast_packages import _write
from toolchain import (
    elaborate,
    mathematical_authoring,
    packages,
    parser,
    proofenv,
    rocq_cache,
    solver_ledger,
)
from toolchain.ast import HoldFastError
from toolchain.elaborate_protocol import _Protocol

ROOT = TOOLS.parent


def _replay_gallina(
    module_name: str,
    gallina: str,
    consumers: str,
    expected_reports: int,
    *,
    batch: rocq_cache.BatchChecker | None = None,
    rocq_module: str | None = None,
) -> None:
    ensure(not solver_ledger.ledger(gallina), f"unexpected solver-trust axioms:\n{gallina}")
    module = rocq_module or elaborate.gallina_module_name(module_name)
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-flow-")))
            stem = module_name
        else:
            directory = batch.work_dir
            stem = batch.unique_stem(module_name)
        target = directory / f"{stem}.v"
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + "\n" + consumers, directory)
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


def _protocol_unit_cases() -> None:
    set_src = b"module P; public effect Raw = calls(Print) canceled by calls(Log);"
    _Protocol(set_src).visit({
        "kind": "surface_file",
        "span": [0, len(set_src)],
        "name": {"text": "P", "span": [7, 8]},
        "declarations": [{
            "kind": "effect_set",
            "span": [10, len(set_src)],
            "modifiers": ["public"],
            "name": {"text": "Raw", "span": [24, 27]},
            "value": {
                "kind": "call",
                "span": [30, 42],
                "callee": {"kind": "name", "span": [30, 35], "name": {"text": "calls", "span": [30, 35]}},
                "arguments": [{
                    "kind": "argument",
                    "span": [36, 41],
                    "label": None,
                    "value": {"kind": "name", "span": [36, 41], "name": {"text": "Print", "span": [36, 41]}},
                }],
            },
            "canceled_by": {
                "kind": "call",
                "span": [55, 65],
                "callee": {"kind": "name", "span": [55, 60], "name": {"text": "calls", "span": [55, 60]}},
                "arguments": [{
                    "kind": "argument",
                    "span": [61, 64],
                    "label": None,
                    "value": {"kind": "name", "span": [61, 64], "name": {"text": "Log", "span": [61, 64]}},
                }],
            },
        }],
    }, (0, len(set_src)))

    block_src = b"effects (!writes(x)) { let a = 1; }"
    _Protocol(block_src).visit({
        "kind": "effects_block",
        "span": [0, len(block_src)],
        "values": [{
            "kind": "unary",
            "span": [9, 19],
            "operator": {"text": "!", "span": [9, 10]},
            "value": {
                "kind": "call",
                "span": [10, 19],
                "callee": {"kind": "name", "span": [10, 16], "name": {"text": "writes", "span": [10, 16]}},
                "arguments": [{
                    "kind": "argument",
                    "span": [17, 18],
                    "label": None,
                    "value": {"kind": "name", "span": [17, 18], "name": {"text": "x", "span": [17, 18]}},
                }],
            },
        }],
        "body": {
            "kind": "block",
            "span": [21, len(block_src)],
            "statements": [{
                "kind": "let",
                "span": [23, 33],
                "name": {"text": "a", "span": [27, 28]},
                "type": None,
                "grade": None,
                "value": {"kind": "nat", "span": [31, 32], "value": "1", "suffix": ""},
            }],
        },
    }, (0, len(block_src)))


def _effect_sets_cancellation_and_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module FlowSetsReplay;

public Nat RawPrint(Nat code) effects none => code;
public Nat RawNet(Nat code) effects none => code + 1;

public Nat SafeLog(Nat code)
    effects calls(RawPrint)
    ensures result == code
    => RawPrint(code);

public Nat LeakyHelper(Nat code)
    effects calls(RawPrint)
    => RawPrint(code);

public Nat Untracked(Nat code) => code;

public effect PrintEff = calls(RawPrint) canceled by calls(SafeLog);
public effect NetEff = calls(RawNet);
public effect RiskyIO = PrintEff | NetEff;

public Nat SafeHandler(Nat x)
    effects calls(SafeLog), !PrintEff
    ensures result == x
    => SafeLog(x);

public Nat SafeUnionHandler(Nat x)
    effects calls(SafeLog), !RiskyIO
    ensures result == x
    => SafeLog(x);
"""
    with parser.cached_build(ROOT) as compiled:
        formatted = mathematical_authoring.format_syntax(compiled, source)
        ensure(b"canceled by" in formatted and b"!PrintEff" in formatted, "formatter dropped effect set syntax")
        ensure(mathematical_authoring.format_syntax(compiled, formatted) == formatted, "formatting not idempotent")
        res = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True))

    mod = elaborate.gallina_module_name("FlowSetsReplay")
    exports = [
        name for name in solver_ledger.math_exports(res.gallina)
        if name.endswith(("_SafeHandler_ensures_0", "_SafeUnionHandler_ensures_0"))
    ]
    ensure(len(exports) == 2, f"missing FlowSetsReplay ensures exports: {exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in exports) + "\n"
    _replay_gallina("FlowSetsReplay", res.gallina, consumers, len(exports), batch=batch)

    prefix = """module NegSets;
public Nat RawPrint(Nat x) effects none => x;
public Nat RawNet(Nat x) effects none => x + 1;
public Nat SafeLog(Nat x) effects calls(RawPrint) => RawPrint(x);
public Nat LeakyHelper(Nat x) effects calls(RawPrint) => RawPrint(x);
public Nat Untracked(Nat x) => x;
public effect PrintEff = calls(RawPrint) canceled by calls(SafeLog);
public effect NetEff = calls(RawNet);
public effect RiskyIO = PrintEff | NetEff;
"""
    negatives = (
        ("direct-forbidden", "public Nat Bad(Nat x) effects calls(RawPrint), !PrintEff => RawPrint(x);", "type"),
        ("direct-forbidden-only", "public Nat Bad(Nat x) effects !PrintEff => RawPrint(x);", "type"),
        ("transitive-forbidden", "public Nat Bad(Nat x) effects calls(LeakyHelper), !PrintEff => LeakyHelper(x);", "type"),
        ("union-cancel-isolation", "public Nat Bad(Nat x) effects calls(RawNet), !RiskyIO => RawNet(x);", "type"),
        ("contradictory-calls", "public Nat Bad(Nat x) effects calls(RawPrint), !calls(RawPrint) => RawPrint(x);", "type"),
        ("negated-none", "public Nat Bad(Nat x) effects !none => x;", "type"),
        ("untracked-under-forbid", "public Nat Bad(Nat x) effects calls(Untracked), !PrintEff => Untracked(x);", "type"),
    )
    with parser.cached_build(ROOT) as compiled:
        for label, tail, expected_kind in negatives:
            bad = (prefix + tail).encode("utf-8")
            with raises(HoldFastError, msg=f"{label} unexpectedly succeeded") as raised:
                elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))
            ensure(raised.exception.kind == expected_kind, f"{label} wrong kind: {raised.exception}")


def _local_effects_blocks_and_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module FlowBlocksReplay;

public Nat RawPrint(Nat code) effects none => code;
public Nat SafeLog(Nat code) effects calls(RawPrint) => RawPrint(code);
public effect PrintEff = calls(RawPrint) canceled by calls(SafeLog);

public Nat PreserveFrame(ref Nat x, Nat delta)
    effects writes(x), calls(SafeLog)
    ensures result == old(x) + delta
{
    let saved = x;
    effects (!writes(x), !PrintEff) {
        let seen = SafeLog(x);
        assert seen == saved;
    }
    x += delta;
    assert x == saved + delta;
    return x;
}

public Nat ReturningScope(ref Nat x)
    effects reads(x), !calls(RawPrint)
    ensures result == x + 1
{
    effects (!writes(x)) {
        return x + 1;
    }
}
"""
    with parser.cached_build(ROOT) as compiled:
        formatted = mathematical_authoring.format_syntax(compiled, source)
        ensure(b"effects (" in formatted, "formatter lost effects block")
        ensure(mathematical_authoring.format_syntax(compiled, formatted) == formatted, "effects block formatting not idempotent")
        res = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True))

    mod = elaborate.gallina_module_name("FlowBlocksReplay")
    exports = [
        name for name in solver_ledger.math_exports(res.gallina)
        if name.endswith(("_PreserveFrame_ensures_0", "_ReturningScope_ensures_0"))
    ]
    ensure(len(exports) == 2, f"missing FlowBlocksReplay ensures exports: {exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in exports) + "\n"
    _replay_gallina("FlowBlocksReplay", res.gallina, consumers, len(exports), batch=batch)

    prefix = """module NegBlocks;
public Nat RawPrint(Nat x) effects none => x;
public Nat SafeLog(Nat x) effects calls(RawPrint) => RawPrint(x);
public effect PrintEff = calls(RawPrint) canceled by calls(SafeLog);
"""
    negatives = (
        (
            "write-and-restore-in-no-writes",
            "public Nat Bad(ref Nat x) effects writes(x) { let s = x; effects (!writes(x)) { x = 0; x = s; } return x; }",
            "type",
        ),
        (
            "read-in-no-reads",
            "public Nat Bad(in Nat x) effects reads(x) { var Nat y = 0; effects (!reads(x)) { y = x + 1; } return y; }",
            "type",
        ),
        (
            "forbidden-call-in-block",
            "public Nat Bad(Nat x) effects calls(RawPrint) { var Nat y = 0; effects (!calls(RawPrint)) { y = RawPrint(x); } return y; }",
            "type",
        ),
        (
            "widen-enclosing-bound",
            "public Nat Bad(Nat x) effects none { var Nat y = 0; effects (calls(RawPrint)) { y = RawPrint(x); } return y; }",
            "type",
        ),
        (
            "forbid-write-on-function",
            "public Nat Bad(ref Nat x) effects !writes(x) { x = x + 1; return x; }",
            "type",
        ),
    )
    with parser.cached_build(ROOT) as compiled:
        for label, tail, expected_kind in negatives:
            bad = (prefix + tail).encode("utf-8")
            with raises(HoldFastError, msg=f"{label} unexpectedly succeeded") as raised:
                elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))
            ensure(raised.exception.kind == expected_kind, f"{label} wrong kind: {raised.exception}")


def _package_policy_and_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    with tempfile.TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        raw_dir = _write(workspace, "rawio", "v1", {}, "Raw.Policy")
        app_dir = _write(workspace, "app", "v1", {"rawio": "v1"}, "App.Main")
        (raw_dir / "module.hf").write_text("""module Raw.Policy;
public u32 RawWrite(u32 v) effects none => v;
public u32 SafeWrite(u32 v)
    effects calls(RawWrite)
    ensures result == v
    => RawWrite(v);
public effect RawIO = calls(RawWrite) canceled by calls(SafeWrite);
""", encoding="utf-8")
        app_manifest = app_dir / packages.MANIFEST
        app_manifest.write_text(
            app_manifest.read_text(encoding="utf-8")
            + '\n[policy]\nforbid_effects = ["Raw.Policy.RawIO"]\nrequire_explicit_effects = true\n',
            encoding="utf-8",
        )
        app_file = app_dir / "module.hf"
        safe_app = """module App.Main;
import Raw.Policy as IO;
public u32 Run(u32 v)
    effects calls(IO.SafeWrite)
    => IO.SafeWrite(v);
"""
        app_file.write_text(safe_app, encoding="utf-8")
        lock, bundle = workspace / "lock.json", workspace / "bundle.json"

        def lock_and_build() -> bytes:
            with parser.cached_build(ROOT) as compiled:
                app_file.write_bytes(mathematical_authoring.format_syntax(compiled, app_file.read_bytes()))
            packages.lock_package(ROOT, workspace, "app", "v1", lock)
            packages.build_package(ROOT, workspace, lock, bundle)
            return bundle.read_bytes()

        initial = lock_and_build()
        gallina = json.loads(initial)["modules"]["App.Main"]
        [safe_post] = re.findall(r"^Definition (\w+_SafeWrite_ensures_0)\b", gallina, re.MULTILINE)
        [run_fn] = re.findall(r"^Definition (\w+_Run)\b", gallina, re.MULTILINE)
        [pkg_mod] = re.findall(r"^Module (HoldFastPackage_\w+)\.$", gallina, re.MULTILINE)
        _replay_gallina(
            "PkgPolicy",
            gallina,
            f"Example pkg_ok v : {pkg_mod}.{run_fn} v = v :=\n  {pkg_mod}.{safe_post} v.\nPrint Assumptions pkg_ok.\n",
            1,
            batch=batch,
            rocq_module=pkg_mod,
        )

        # Editing [policy] without relocking must fail stale lock check.
        saved_manifest = app_manifest.read_text(encoding="utf-8")
        app_manifest.write_text(
            saved_manifest.replace("require_explicit_effects = true", "require_explicit_effects = false"),
            encoding="utf-8",
        )
        with raises(ValueError, msg="policy edit reused stale lock") as stale:
            packages.build_package(ROOT, workspace, lock, bundle)
        ensure("stale package lock" in str(stale.exception), f"unexpected stale message: {stale.exception}")
        app_manifest.write_text(saved_manifest, encoding="utf-8")

        # Calling unencapsulated RawWrite violates policy.forbid_effects.
        app_file.write_text("""module App.Main;
import Raw.Policy as IO;
public u32 Run(u32 v) effects calls(IO.RawWrite) => IO.RawWrite(v);
""", encoding="utf-8")
        with raises(HoldFastError, msg="policy allowed forbidden RawWrite") as refused:
            lock_and_build()
        ensure(refused.exception.kind == "type" and "RawIO" in refused.exception.message,
               f"wrong policy refusal: {refused.exception}")

        # Omitting effects clause violates policy.require_explicit_effects.
        app_file.write_text("""module App.Main;
import Raw.Policy as IO;
public u32 Run(u32 v) => IO.SafeWrite(v);
""", encoding="utf-8")
        with raises(HoldFastError, msg="policy allowed omitted effects") as missing_eff:
            lock_and_build()
        ensure(missing_eff.exception.kind == "type" and "explicit effects clause" in missing_eff.exception.message,
               f"wrong explicit-effects refusal: {missing_eff.exception}")

        # Unknown policy target must fail explicitly.
        app_file.write_text(safe_app, encoding="utf-8")
        app_manifest.write_text(saved_manifest.replace("Raw.Policy.RawIO", "Raw.Policy.NoSuchSet"), encoding="utf-8")
        with raises(HoldFastError, msg="unknown policy target accepted") as bad_target:
            lock_and_build()
        ensure(bad_target.exception.kind == "name", f"wrong unknown-target error: {bad_target.exception}")


def _contract_diff_human_and_summary() -> None:
    old_src = b"""module Audit;
public effect RawPrint = calls(Print);
public Nat Check(Nat value)
    requires value > 0
    ensures result > 0
    effects !RawPrint
    => value;
"""
    new_src = b"""module Audit;
public effect RawPrint = calls(Print) canceled by calls(SafeLog);
public Nat Check(Nat value)
    requires value > 2
    ensures result >= 0
    effects calls(SafeLog)
    => value;
"""
    with tempfile.TemporaryDirectory() as temporary:
        old, new = Path(temporary) / "old.hf", Path(temporary) / "new.hf"
        old.write_bytes(old_src)
        new.write_bytes(new_src)
        code, out, err = _invoke(["diff-contract", str(old), str(new)])
        ensure(code == 0 and not err, f"diff-contract json failed: {err}")
        report = json.loads(out)
        summary = report["review_summary"]
        ensure(summary["compatibility_verdict"] == "unverified-syntax-diff", f"unexpected verdict: {summary}")
        flags = set(summary["risk_flags"])
        ensure(
            {"precondition-changed", "postcondition-changed", "effects-changed", "prohibition-removed", "effect-set-changed"}
            <= flags,
            f"missing audit risk flags: {flags}",
        )
        code_h, out_h, err_h = _invoke(["diff-contract", "--human", str(old), str(new)])
        ensure(code_h == 0 and not err_h, f"diff-contract --human failed: {err_h}")
        ensure("Contract audit for module Audit" in out_h and "prohibition-removed" in out_h and "unverified-syntax-diff" in out_h,
               f"human output missing audit details:\n{out_h}")


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("flow-effects-protocol-unit", _protocol_unit_cases),
        Case("flow-effects-sets-cancellation-and-replay", partial(_effect_sets_cancellation_and_replay, batch=batch), lane="toolchain"),
        Case("flow-effects-local-blocks-and-replay", partial(_local_effects_blocks_and_replay, batch=batch), lane="toolchain"),
        Case("flow-effects-package-policy-and-replay", partial(_package_policy_and_replay, batch=batch), lane="toolchain"),
        Case("flow-effects-contract-diff-summary-and-human", _contract_diff_human_and_summary, lane="toolchain"),
        Case("kernel check flow effects with rocqchk", batch.verify_all, lane="toolchain"),
    ]
