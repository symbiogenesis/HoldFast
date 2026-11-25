# SPDX-License-Identifier: Apache-2.0
"""Replay the pure graded kernel trial and audit its principal proofs."""

import contextlib
import hashlib
import io
import json
import shutil
import subprocess
import tempfile
from functools import partial
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from toolchain import proofenv, solver_ledger
from toolchain.cli.holdfast_parser import main as parser_main

_PURE_PROOFS = (
    "check_sound",
    "substitute_telescope_sound",
    "separate_computation_and_type_use",
    "specialize_dependent_function",
    "scale_computation_through_application",
    "reject_wrong_exact_allowance",
    "reject_unbound_type_index",
    "reject_capture_of_nested_type_binder",
    "rewrite_later_telescope_rows",
    "reject_stale_type_use_certificate",
    "reject_stale_substitution_row",
)
_DOMAIN_PROOFS = (
    "NatExact",
    "NatBound",
    "Presence",
    "exact_to_bound",
    "bound_to_presence",
    "substitution_commutes_with_translation",
    "exact_substitution_agrees_with_pure",
    "check_rows_spec",
    "exact_reconstructs_containing_telescope",
    "exact_rejects_relaxation",
    "bound_accepts_relaxation",
    "exact_rejects_stale_dependency",
    "bound_rejects_stale_dependency",
    "presence_reconstructs_dependency",
    "presence_cannot_recover_counts",
)


def _replay(unit: str, module: str, proofs: tuple[str, ...], dependencies: tuple[str, ...] = ()) -> None:
    launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
    compile_unit = [*launch, "rocq", "c", "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-") as temporary:
        directory = Path(temporary)
        for name in (*dependencies, unit):
            source = TOOLS / "rocq" / f"{name}.v"
            shutil.copyfile(source, directory / source.name)
            subprocess.run([*compile_unit, source.name], cwd=directory, check=True, timeout=180)
        audit = directory / "GradeAudit.v"
        audit.write_text(f"Require Import {unit}.\n" + "".join(
            f"Print Assumptions {module}.{name}.\n" for name in proofs), encoding="utf-8")
        report = subprocess.run([*compile_unit, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=180)
        solver_ledger.audit(report.stdout, len(proofs), module, ())
        subprocess.run([*launch, "rocqchk", "-silent", unit], cwd=directory,
                       check=True, timeout=180)


def _source_command(path: Path, declaration: str) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(["check-grades", str(path), declaration])
    return status, output.getvalue(), error.getvalue()


def _demand(bindings: list[dict[str, object]]) -> list[tuple[object, object, object]]:
    return [(binding["name"], binding["computation"], binding["type"]) for binding in bindings]


def _source_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-dependent.hf"
    raw = source.read_bytes()
    for declaration, expected in (
        ("PreserveLength", [("length", 0, 2), ("values", 1, 0)]),
        ("Quadruple", [("n", 4, 0)]),
    ):
        status, output, error = _source_command(source, declaration)
        ensure(status == 0, error)
        ensure(_demand(json.loads(output)["binders"]) == expected, f"wrong usage in {declaration}")
    status, output, error = _source_command(source, "Specialize")
    ensure(status == 0, error)
    result = json.loads(output)
    ensure(result["source_sha256"] == hashlib.sha256(raw).hexdigest(), "source bytes were lost")
    n, values = result["binders"]
    ensure(_demand([n, values]) == [("n", 0, 4), ("values", 1, 0)], "wrong specialized grades")
    row = [{"name": "n", "uses": 2, "span": n["span"]}]
    ensure(n["annotation_type_uses"] == [] and values["annotation_type_uses"] == row
           and result["result_type_uses"] == row, "specialized domain and codomain dependencies differ")
    ensure(result["dependencies"] == ["PreserveLength"], "source dependency was lost")

    with tempfile.TemporaryDirectory(prefix="holdfast-graded-source-controls-") as temporary:
        directory = Path(temporary)
        changed = directory / source.name
        for original, replacement, failure in (
            (b"Nat size @ NatExact(0)", b"Nat size @ NatExact(1)", "exact computation demand"),
            (b"PreserveLength()(n + n)", b"PreserveLength()(n)", "declared dependent type"),
            (b"Vec<Nat, (n + n)> values", b"Vec<Nat, n> values", "declared dependent type"),
        ):
            ensure(raw.count(original) == 1, f"source control does not identify one occurrence: {original!r}")
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, "Specialize")
            ensure(status == 1 and not output and ": grade: " in error and failure in error, error)
        for original, replacement in (
            (b"Nat n @ NatExact(0)", b"const Nat n @ NatExact(0)"),
            (b"PreserveLength()(n + n)", b"PreserveLength()(length: n + n)"),
            (b"Vec<Nat, (n + n)> values", b"owned Vec<Nat, (n + n)> values"),
        ):
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, "Specialize")
            ensure(status == 1 and not output and ": unsupported: " in error, error)
        for declaration in (
            b"definition Nat Invalid(Nat _ @ NatExact(1)) => _;",
            b"definition Nat Invalid(Nat x @ NatExact(0)) => ((Nat x @ NatExact(1)) => x)(0);",
        ):
            changed.write_bytes(b"module Invalid;\n" + declaration + b"\n")
            status, output, error = _source_command(changed, "Invalid")
            ensure(status == 1 and not output and "duplicate or invalid graded binder" in error, error)

        compiler = [*proofenv.rocq_command(), "-q"]
        for name, digest in result["kernel_sha256"].items():
            unit = TOOLS / "rocq" / name
            ensure(hashlib.sha256(unit.read_bytes()).hexdigest() == digest, f"unbound Rocq support {name}")
            shutil.copyfile(unit, directory / name)
            subprocess.run([*compiler, name], cwd=directory, check=True, timeout=30)
        certificate = result["gallina"]
        unit = directory / "SourceProof.v"
        unit.write_text(certificate, encoding="utf-8")
        subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True, check=True, timeout=30)
        audit = directory / "SourceAudit.v"
        audit.write_text("Require Import SourceProof graded_source.\n"
                         "Print Assumptions GradedSource.source_check_sound.\n"
                         "Print Assumptions source_rows_match.\n", encoding="utf-8")
        replay = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=30)
        solver_ledger.audit(replay.stdout, 2, "GradedSource", ())
        stale = certificate.replace("[0; 0; 4]", "[0; 0; 3]")
        ensure(stale != certificate, "certificate control left the alleged type demand unchanged")
        unit.write_text(stale, encoding="utf-8")
        refused = subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True,
                                 text=True, encoding="utf-8", check=False, timeout=30)
        ensure(refused.returncode != 0 and "Unable to unify" in refused.stderr, refused.stderr)


def cases() -> list[Case]:
    return [Case("pure dependent usage and telescope substitution replay",
                 partial(_replay, "graded_pure", "GradedPure", _PURE_PROOFS), lane="toolchain"),
            Case("ordered grade domains and dependent row certificates",
                 partial(_replay, "graded_domains", "GradedDomains", _DOMAIN_PROOFS, ("graded_pure",)),
                 lane="toolchain"),
            Case("source-bound exact grades and dependent partial application replay", _source_replay, lane="toolchain")]
