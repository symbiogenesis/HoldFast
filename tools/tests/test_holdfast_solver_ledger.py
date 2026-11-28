# SPDX-License-Identifier: Apache-2.0
"""Behavioral tests for the HoldFast solver-trust ledger and its assumption audit."""

import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from toolchain import rocq_cache, solver_ledger

INDEPENDENT_CASES = True

_MODULE = "HoldFast_M"
_GALLINA = (
    "(* holdfast-solver-trust: holdfast_d3_Law at 7:5; theorem proof step discharged by the untrusted solver *)\n"
    "Axiom holdfast_solver_holdfast_d3_Law : forall (x : nat), x = x.\n"
    "Definition holdfast_d3_Law :=\n  holdfast_solver_holdfast_d3_Law.\n"
    "Definition holdfast_d4_Closed : nat := 0.\n"
)


def _ledger_reads_markers() -> None:
    entries = solver_ledger.ledger(_GALLINA)
    ensure(len(entries) == 1, f"expected one ledger entry, got {entries}")
    entry = entries[0]
    ensure(
        (entry.export, entry.axiom, entry.line, entry.column) == ("holdfast_d3_Law", "holdfast_solver_holdfast_d3_Law", 7, 5),
        f"unexpected ledger entry {entry}",
    )
    ensure(solver_ledger.ledger("Definition holdfast_d0_X : nat := 0.\n") == (), "closed output must have an empty ledger")


def _ledger_refuses_unmarked_axioms() -> None:
    for text in (
        "Axiom holdfast_solver_holdfast_d0_X : True.\nDefinition holdfast_d0_X := holdfast_solver_holdfast_d0_X.\n",
        _GALLINA + "Axiom hidden : False.\n",
        _GALLINA.replace("Axiom holdfast_solver_holdfast_d3_Law", "Axiom holdfast_solver_holdfast_d9_Other"),
    ):
        try:
            solver_ledger.ledger(text)
        except ValueError:
            continue
        raise AssertionError(f"ledger accepted an unmarked or misnamed axiom:\n{text}")


def _audit_matches_kernel_report() -> None:
    entries = solver_ledger.ledger(_GALLINA)
    report = (
        "Axioms:\n"
        "HoldFast_M.holdfast_solver_holdfast_d3_Law : forall x : nat, x = x\n"
        "Closed under the global context\n"
    )
    ensure(
        solver_ledger.audit(report, 2, _MODULE, entries) == ["HoldFast_M.holdfast_solver_holdfast_d3_Law"],
        "audit did not report the ledger axiom",
    )
    refusals = {
        "unledgered assumption": "Axioms:\nHoldFast_M.hidden : False\nClosed under the global context\n",
        "missing report": "Axioms:\nHoldFast_M.holdfast_solver_holdfast_d3_Law : forall x : nat, x = x\n",
        "unused ledger axiom": "Closed under the global context\nClosed under the global context\n",
    }
    for label, text in refusals.items():
        try:
            solver_ledger.audit(text, 2, _MODULE, entries)
        except ValueError:
            continue
        raise AssertionError(f"audit accepted a report with an {label}")


def _audit_refuses_malformed_reports() -> None:
    for report in (
        "Axioms:\n",
        "Axioms:\n  hidden : False\n",
        "Axioms:\nhidden\n  : False\n",
        "Axioms:\n\u00c9vidence : False\n",
        "Axioms:\nClosed under the global context\n",
        "Closed under the global context\ntrailing output\n",
        "Closed under the global context\n  hidden : False\n",
        "hidden : False\nClosed under the global context\n",
    ):
        audited = report.count("Closed under the global context") + report.count("Axioms:")
        try:
            solver_ledger.audit(report, audited, _MODULE, ())
        except ValueError:
            continue
        raise AssertionError(f"malformed output supplied an empty assumption verdict: {report!r}")
    entries = solver_ledger.ledger(_GALLINA)
    wrapped = "Axioms:\nHoldFast_M.holdfast_solver_holdfast_d3_Law :\n  forall x : nat,\n  x = x\n"
    ensure(solver_ledger.audit(wrapped, 1, _MODULE, entries)
           == ["HoldFast_M.holdfast_solver_holdfast_d3_Law"],
           "a supported wrapped proposition lost its assumption identity")
    with raises(ValueError, msg="a valid report hid an empty later report"):
        solver_ledger.audit(wrapped + "Axioms:\n", 2, _MODULE, entries)


def _ledger_refuses_kernel_and_proof_bypasses() -> None:
    base = "Definition holdfast_d0_X : nat := 0.\n"
    for snippet in (
        "Parameter hidden : False.\n",
        "Parameters a b : Prop.\n",
        "Variable v : nat.\n",
        "Variables x y : nat.\n",
        "Hypothesis h : False.\n",
        "Hypotheses h1 h2 : False.\n",
        "Conjecture c : False.\n",
        "Axioms a1 a2 : False.\n",
        "Lemma bad : False. Proof. Admitted.\n",
        "Lemma bad : False. Proof. admit. Qed.\n",
        "Unset Guard Checking.\n",
        "Unset Positivity Checking.\n",
        "Unset Universe Checking.\n",
        "Unset Strict Universe Declaration.\n",
        "Set Type in Type.\n",
        "Set Universe Checking Off.\n",
        "Set Allow Rewrite Rules.\n",
        "Rewrite Rule bad := | plus 0 ?x => ?x.\n",
        "#[enable_rewrite_rules] Symbol f : nat -> nat.\n",
        "Symbol f : nat -> nat.\n",
        "Symbols a b : nat.\n",
        "Admit Obligations.\n",
        "#[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n.\n",
        "Bypass_check fixpoint.\n",
        'Declare ML Module "rocq-runtime.plugins.ltac".\n',
        "Unsafe Definition u : nat := 0.\n",
    ):
        with raises(ValueError, msg=f"ledger accepted prohibited snippet: {snippet!r}"):
            solver_ledger.ledger(base + snippet)
    commented = (
        "(* outer comment (* Unset Guard Checking. Admitted. Parameter p : False. "
        "Rewrite Rule r := ... Symbol f : nat. *) *)\n"
        + base
        + "Definition holdfast_d1_Use (symbol : nat) : nat := symbol.\n"
    )
    ensure(solver_ledger.ledger(commented) == (), "nested Rocq comment or benign identifier caused a false refusal")


def _prover_version_guard() -> None:
    ensure(
        solver_ledger.check_prover_version("The Rocq Prover, version 9.3.0") == (9, 3, 0),
        "patched 9.3.0 prover rejected",
    )
    ensure(
        solver_ledger.check_prover_version("The Rocq Prover, version 9.4.1") == (9, 4, 1),
        "newer 9.4.1 prover rejected",
    )
    for bad in (
        "The Rocq Prover, version 9.2.0",
        "The Coq Proof Assistant, version 8.20.1",
        "unknown output",
    ):
        with raises(ValueError, msg=f"unsafe or unparsed prover version accepted: {bad!r}"):
            solver_ledger.check_prover_version(bad)


def _prover_flag_guard() -> None:
    solver_ledger.check_prover_flags(["rocq", "c", "-q", "Unit.v"])
    solver_ledger.check_prover_flags(["rocqchk", "-silent", "-o", "Unit"])
    solver_ledger.check_prover_flags(["rocqchk", "-bytecode-compiler", "no", "-native-compiler=no", "Unit"])
    for bad_flag in (
        "-allow-rewrite-rules",
        "--allow-rewrite-rules",
        "-type-in-type",
        "--type-in-type",
        "-impredicative-set",
        "--impredicative-set",
        "-bypass-qed",
        "--bypass-qed",
        "-admit",
        "--admit",
        "-norec",
        "--norec",
        "-bytecode-compiler=yes",
        "--bytecode-compiler=yes",
        "-native-compiler=yes",
        "-native-compiler=ondemand",
    ):
        with raises(ValueError, msg=f"prohibited prover flag accepted: {bad_flag!r}"):
            solver_ledger.check_prover_flags(["rocq", "c", bad_flag, "Unit.v"])
    for split_bad in (
        ["rocqchk", "-bytecode-compiler", "yes", "Unit"],
        ["rocqchk", "-bytecode-compiler"],
        ["rocq", "c", "-native-compiler", "ondemand", "Unit.v"],
        ["rocq", "c", "-native-compiler", "yes", "Unit.v"],
    ):
        with raises(ValueError, msg=f"prohibited split prover flag accepted: {split_bad!r}"):
            solver_ledger.check_prover_flags(split_bad)
    with tempfile.TemporaryDirectory(prefix="holdfast-flag-guard-") as tmp, raises(
        ValueError, msg="rocq_cache accepted -allow-rewrite-rules"
    ):
        rocq_cache.materialize_units(
            Path(tmp),
            [("Unit.v", b"Definition x := 0.\n")],
            compiler=["rocq", "c", "-allow-rewrite-rules"],
            use_default_cache=False,
        )


def _kernel_profile_guard() -> None:
    benign = (
        '(* SProp Polymorphic Register Primitive Module Type CoFixpoint vm_cast_no_check *)\n'
        'From Stdlib Require Import String.\n'
        'Definition holdfast_d0_Register : nat := 0.\n'
        'Definition holdfast_d1_Msg : string := "SProp vm_cast_no_check CoFixpoint".\n'
        'Lemma holdfast_d2_Comp : 1 + 1 = 2. Proof. vm_compute. reflexivity. Qed.\n'
    )
    solver_ledger.check_kernel_profile(benign)
    ensure(solver_ledger.ledger(benign) == (), "benign minimal-CIC module was refused")

    for bad in (
        "Lemma bad : 1 = 1. Proof. exact_no_check (@eq_refl nat 1). vm_cast_no_check (@eq_refl nat 1). Qed.\n",
        "Lemma bad : 1 = 1. Proof. native_cast_no_check (@eq_refl nat 1). Qed.\n",
        "Lemma bad : 1 = 1. Proof. native_compute. reflexivity. Qed.\n",
        "Definition s : SProp := True.\n",
        "Polymorphic Definition id@{u} (A : Type@{u}) (x : A) := x.\n",
        "#[universes(polymorphic)] Definition id (A : Type) (x : A) := x.\n",
        "Cumulative Inductive Box (A : Type) := box : A -> Box A.\n",
        "Set Universe Polymorphism.\n",
        "Primitive int := #int63_type.\n",
        "Register bool as kernel.ind_bool.\n",
        "Module Type Sig. Parameter T : Type. End Sig.\n",
        "CoInductive stream := Cons : nat -> stream -> stream.\n",
        "CoFixpoint zeros : stream := Cons 0 zeros.\n",
    ):
        with raises(ValueError, msg=f"excluded CIC feature accepted: {bad!r}"):
            solver_ledger.ledger(bad)
    solver_ledger.check_kernel_profile("CoFixpoint eof := eof.\n", allow_cofixpoint=True)


def _rocqchk_context_audit() -> None:
    clean = (
        "\nCONTEXT SUMMARY\n===============\n\n"
        "* Theory: Set is predicative\n  \n"
        "* Theory: Rewrite rules are not allowed\n  \n"
        "* Axioms: <none>\n  \n"
        "* Constants/Inductives relying on type-in-type: <none>\n  \n"
        "* Constants/Inductives relying on unsafe (co)fixpoints: <none>\n  \n"
        "* Inductives whose positivity is assumed: <none>\n  \n"
        "* Inductives relying on indices not mattering:\n"
        "    Corelib.Init.Logic.eq\n\n"
    )
    ensure(solver_ledger.audit_rocqchk_context(clean) == [], "clean rocqchk summary was refused")
    with_ax = clean.replace("* Axioms: <none>", "* Axioms:\n    Test.Ax.foo")
    ensure(
        solver_ledger.audit_rocqchk_context(with_ax, ["Test.Ax.foo"]) == ["Test.Ax.foo"],
        "allowed rocqchk axiom was refused",
    )
    for bad_msg, bad_out in (
        ("missing summary", "Checked Ok.\n"),
        ("impredicative Set", clean.replace("Set is predicative", "Set is impredicative")),
        ("rewrite rules", clean.replace("Rewrite rules are not allowed", "Rewrite rules are allowed")),
        ("type-in-type", clean.replace("type-in-type: <none>", "type-in-type:\n    Bad.T")),
        ("unsafe fixpoint", clean.replace("unsafe (co)fixpoints: <none>", "unsafe (co)fixpoints:\n    Bad.f")),
        ("assumed positivity", clean.replace("positivity is assumed: <none>", "positivity is assumed:\n    Bad.I")),
        ("unallowed axiom", with_ax),
    ):
        with raises(ValueError, msg=f"unsafe rocqchk summary accepted ({bad_msg})"):
            solver_ledger.audit_rocqchk_context(bad_out)
    with raises(ValueError, msg="missing expected rocqchk axiom was accepted"):
        solver_ledger.audit_rocqchk_context(clean, ["Test.Ax.foo"])


def _canonical_statement_audit() -> None:
    entries = solver_ledger.ledger(_GALLINA)
    script = solver_ledger.build_audit_script(
        "From HoldFastElaboration Require Import Case000.",
        ["Case000.HoldFast_M.holdfast_d3_Law", "Case000.HoldFast_M.holdfast_d4_Closed"],
    )
    ensure(
        "Set Printing All." in script
        and f"Check {solver_ledger.STATEMENT_AUDIT_MARKER}." in script
        and "Check @Case000.HoldFast_M.holdfast_d3_Law." in script,
        f"canonical audit script omitted required checks:\n{script}",
    )
    good_out = (
        "Axioms:\n"
        "HoldFast_M.holdfast_solver_holdfast_d3_Law : forall x : nat, @eq nat x x\n"
        "Closed under the global context\n"
        f"{solver_ledger.STATEMENT_AUDIT_MARKER}\n"
        f"     : {solver_ledger.STATEMENT_AUDIT_TYPE}\n"
        "@HoldFast_M.holdfast_d3_Law\n"
        "     : forall x : nat, @eq nat x x\n"
        "HoldFast_M.holdfast_d4_Closed\n"
        "     : nat\n"
    )
    reported, digest = solver_ledger.parse_full_audit(good_out, 2, _MODULE, entries)
    ensure(reported == ["HoldFast_M.holdfast_solver_holdfast_d3_Law"] and len(digest) == 64,
           "canonical statement audit failed on valid output")
    for bad_out in (
        good_out.replace(f"{solver_ledger.STATEMENT_AUDIT_MARKER}\n", "missing_marker\n"),
        good_out.rsplit("HoldFast_M.holdfast_d4_Closed", 1)[0],
    ):
        with raises(ValueError, msg="malformed canonical statement audit was accepted"):
            solver_ledger.parse_full_audit(bad_out, 2, _MODULE, entries)


def _runtime_tcb_and_bug_register() -> None:
    lock_path = Path(__file__).resolve().parents[2] / "tools/opam/rocq.lock"
    lock_text = lock_path.read_text(encoding="utf-8")
    tcb = solver_ledger.locked_runtime_tcb(lock_text)
    ensure(set(tcb) == {"rocq-core", "rocq-runtime", "ocaml-base-compiler", "zarith", "conf-gmp"},
           f"unexpected TCB package set: {tcb!r}")
    ensure(solver_ledger.verify_critical_bug_register(lock_text) == [],
           "critical-bug register reported unexpected findings on tools/opam/rocq.lock")
    with raises(ValueError, msg="lock missing zarith was accepted"):
        solver_ledger.locked_runtime_tcb(lock_text.replace('"zarith.', '"other.'))
    findings = solver_ledger.verify_critical_bug_register(lock_text.replace('"rocq-core.9.3.0"', '"rocq-core.9.2.0"'))
    ensure(bool(findings), "mismatched rocq-core version passed critical-bug register")


def _rocqchk_isolation_and_context_refusal() -> None:
    scrubbed = rocq_cache.scrubbed_checker_env(
        {"PATH": "/usr/bin", "COQPATH": "/bad", "ROCQPATH": "/bad", "OCAMLPATH": "/bad", "HOME": "/home/u"}
    )
    ensure(scrubbed == {"PATH": "/usr/bin", "HOME": "/home/u"},
           f"ambient prover variables survived scrubbing: {scrubbed!r}")
    with tempfile.TemporaryDirectory(prefix="holdfast-chk-iso-") as tmp:
        src = Path(tmp)
        (src / "Unit.vo").write_bytes(b"vo")
        bad_summary = (
            "\nCONTEXT SUMMARY\n===============\n"
            "* Theory: Set is predicative\n"
            "* Theory: Rewrite rules are not allowed\n"
            "* Axioms:\n    Unit.hidden_axiom\n"
            "* Constants/Inductives relying on type-in-type: <none>\n"
            "* Constants/Inductives relying on unsafe (co)fixpoints: <none>\n"
            "* Inductives whose positivity is assumed: <none>\n"
        )
        fake_chk = src / "fake-rocqchk"
        fake_chk.write_text("#!/bin/sh\n", encoding="utf-8")
        with (
            patch.dict("os.environ", {"VOS_ROCQCHK": str(fake_chk)}),
            patch.object(
                rocq_cache.subprocess,
                "run",
                return_value=subprocess.CompletedProcess([str(fake_chk)], 0, "", bad_summary),
            ),
            raises(ValueError, msg="check_kernel accepted an unexpected axiom in rocqchk CONTEXT SUMMARY"),
        ):
            rocq_cache.check_kernel(src, ["Unit"])


def cases() -> list[Case]:
    return [
        Case("ledger-reads-markers", _ledger_reads_markers),
        Case("ledger-refuses-unmarked-axioms", _ledger_refuses_unmarked_axioms),
        Case("audit-matches-kernel-report", _audit_matches_kernel_report),
        Case("audit-refuses-malformed-reports", _audit_refuses_malformed_reports),
        Case("ledger-refuses-kernel-and-proof-bypasses", _ledger_refuses_kernel_and_proof_bypasses),
        Case("prover-version-guard", _prover_version_guard),
        Case("prover-flag-guard", _prover_flag_guard),
        Case("kernel-profile-guard", _kernel_profile_guard),
        Case("rocqchk-context-audit", _rocqchk_context_audit),
        Case("canonical-statement-audit", _canonical_statement_audit),
        Case("runtime-tcb-and-bug-register", _runtime_tcb_and_bug_register),
        Case("rocqchk-isolation-and-context-refusal", _rocqchk_isolation_and_context_refusal),
    ]
