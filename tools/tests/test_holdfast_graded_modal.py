# SPDX-License-Identifier: Apache-2.0
"""Replay exact-natural modal introduction and dependent elimination in Rocq."""

import shutil
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case
from toolchain import proofenv, solver_ledger

_AUDITED = (
    "check_sound",
    "checked_let_box_demands",
    "promotion_scales_term_demand",
    "dependent_elimination_of_abstract_box",
    "dependent_elimination_of_promoted_box",
    "zero_use_keeps_logical_motive",
    "reject_wrong_exact_box_grade",
    "reject_wrong_motive_specialization",
    "reject_bypassing_open",
    "reject_computing_with_zero_use_payload",
)


def _replay() -> None:
    launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
    compile_unit = [*launch, "rocq", "c", "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-modal-") as temporary:
        directory = Path(temporary)
        for name in ("graded_pure.v", "graded_modal.v"):
            shutil.copyfile(TOOLS / "rocq" / name, directory / name)
            subprocess.run([*compile_unit, name], cwd=directory, check=True, timeout=180)
        audit = directory / "ModalAudit.v"
        audit.write_text("Require Import graded_modal.\n" + "".join(
            f"Print Assumptions GradedModal.{name}.\n" for name in _AUDITED), encoding="utf-8")
        report = subprocess.run([*compile_unit, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=180)
        solver_ledger.audit(report.stdout, len(_AUDITED), "GradedModal", ())
        subprocess.run([*launch, "rocqchk", "-silent", "graded_modal"], cwd=directory,
                       check=True, timeout=180)


def cases() -> list[Case]:
    return [Case("exact-natural box promotion and dependent elimination replay", _replay, lane="toolchain")]
