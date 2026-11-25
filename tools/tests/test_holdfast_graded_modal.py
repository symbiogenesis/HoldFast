# SPDX-License-Identifier: Apache-2.0
"""Replay exact-natural modal introduction and dependent elimination in Rocq."""

import contextlib
import hashlib
import io
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from toolchain import proofenv, solver_ledger
from toolchain.cli.holdfast_parser import main as parser_main

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


def _source_command(path: Path, declaration: str) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(["check-grades", str(path), declaration, "--modal"])
    return status, output.getvalue(), error.getvalue()


def _source_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-modal.hf"
    raw = source.read_bytes()
    for declaration, name, computation, type_use in (
        ("OpenTwo", "packed", 1, 2),
        ("PromoteAndOpen", "n", 4, 8),
        ("OpenZero", "packed", 1, 2),
    ):
        status, output, error = _source_command(source, declaration)
        ensure(status == 0, error)
        result = json.loads(output)
        ensure(result["source_sha256"] == hashlib.sha256(raw).hexdigest() and result["dependencies"] == ["Box"],
               "modal replay lost its source bytes or record dependency")
        [binder] = result["binders"]
        ensure(binder["name"] == name and binder["computation"] == computation and binder["type"] == type_use,
               f"wrong modal demands for {declaration}")
        ensure(result["result_type_uses"] == [{"name": name, "uses": type_use, "span": binder["span"]}],
               f"wrong modal result dependencies for {declaration}")

    status, output, error = _source_command(source, "KeepShape")
    ensure(status == 0, error)
    result = json.loads(output)
    packed, values = result["binders"]
    row = [{"name": "packed", "uses": 1, "span": packed["span"]}]
    ensure(packed["computation"] == 0 and packed["type"] == 2 and values["computation"] == 1,
           "wrong modal telescope usage")
    ensure(values["annotation_type_uses"] == row and result["result_type_uses"] == row,
           "modal telescope did not retain the annotation and result rows")

    with tempfile.TemporaryDirectory(prefix="holdfast-graded-modal-controls-") as temporary:
        directory = Path(temporary)
        changed = directory / source.name
        for declaration, original, replacement, failure in (
            ("OpenTwo", b"Box(n) => (n + n,", b"Box(n) => (n,", ": grade: "),
            ("OpenTwo", b"Box<Nat, 2>(n).Value", b"Box<Nat, 1>(n).Value", ": grade: "),
            ("OpenZero", b"Box<Nat, 0>(n).Value", b"n", ": grade: "),
            ("OpenTwo", b"T Value @ q", b"T Value @ NatExact(1)", ": unsupported: "),
        ):
            ensure(raw.count(original) == 1, f"modal control does not identify one occurrence: {original!r}")
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, declaration)
            ensure(status == 1 and not output and failure in error, error)

        compiler = [*proofenv.rocq_command(), "-q"]
        support = ("graded_pure.v", "graded_modal.v", "graded_modal_source.v")
        ensure(set(result["kernel_sha256"]) == set(support), "wrong Rocq support closure")
        for name in support:
            unit = TOOLS / "rocq" / name
            ensure(hashlib.sha256(unit.read_bytes()).hexdigest() == result["kernel_sha256"][name],
                   f"unbound Rocq support {name}")
            shutil.copyfile(unit, directory / name)
            subprocess.run([*compiler, name], cwd=directory, check=True, timeout=30)
        certificate = result["gallina"]
        unit = directory / "ModalSourceProof.v"
        unit.write_text(certificate, encoding="utf-8")
        subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True, check=True, timeout=30)
        audit = directory / "ModalSourceAudit.v"
        audit.write_text("Require Import ModalSourceProof graded_modal_source.\n"
                         "Print Assumptions GradedModalSource.source_check_sound.\n"
                         "Print Assumptions source_rows_match.\n", encoding="utf-8")
        replay = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=30)
        solver_ledger.audit(replay.stdout, 2, "GradedModalSource", ())
        stale = certificate.replace("[0; 0; 2]", "[0; 0; 1]")
        ensure(stale != certificate, "modal certificate control did not replace a type demand")
        unit.write_text(stale, encoding="utf-8")
        refused = subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True,
                                 text=True, encoding="utf-8", check=False, timeout=30)
        ensure(refused.returncode != 0 and "Unable to unify" in refused.stderr, refused.stderr)


def cases() -> list[Case]:
    return [Case("exact-natural box promotion and dependent elimination replay", _replay, lane="toolchain"),
            Case("graded box declaration, motive and telescope source replay", _source_replay, lane="toolchain")]
