# SPDX-License-Identifier: Apache-2.0
"""Behavioral tests for the HoldFast solver-trust ledger and its assumption audit."""

from tests.harness import Case, ensure, raises
from toolchain import solver_ledger

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


def cases() -> list[Case]:
    return [
        Case("ledger-reads-markers", _ledger_reads_markers),
        Case("ledger-refuses-unmarked-axioms", _ledger_refuses_unmarked_axioms),
        Case("audit-matches-kernel-report", _audit_matches_kernel_report),
        Case("audit-refuses-malformed-reports", _audit_refuses_malformed_reports),
    ]
