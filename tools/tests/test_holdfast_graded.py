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
    "substitute_type_telescope_sound",
    "separate_computation_and_type_use",
    "specialize_dependent_function",
    "scale_computation_through_application",
    "reject_wrong_exact_allowance",
    "reject_unbound_type_index",
    "reject_capture_of_nested_type_binder",
    "rewrite_later_telescope_rows",
    "reject_stale_type_use_certificate",
    "reject_stale_substitution_row",
    "type_valued_identity_demands",
    "specialize_type_identity",
    "reject_type_in_its_own_universe",
    "reject_type_identity_computation_allowance",
    "rewrite_later_type_telescope_rows",
    "reject_stale_type_telescope_row",
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


def _replay(unit: str, module: str, proofs: tuple[str, ...], dependencies: tuple[str, ...] = (),
            generated: tuple[tuple[str, str], ...] = ()) -> None:
    launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
    compile_unit = [*launch, "rocq", "c", "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-") as temporary:
        directory = Path(temporary)
        for name, gallina in generated:
            source = directory / f"{name}.v"
            source.write_text(gallina, encoding="utf-8")
            subprocess.run([*compile_unit, source.name], cwd=directory, check=True, timeout=180)
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


def _source_command(path: Path, declaration: str, *options: str) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(["check-grades", str(path), declaration, *options])
    return status, output.getvalue(), error.getvalue()


def _elaborate_command(path: Path) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(["elaborate", str(path)])
    return status, output.getvalue(), error.getvalue()


def _default_source_replay() -> None:
    fixtures = TOOLS / "tests" / "fixtures"
    definitions = {
        "graded-dependent.hf": ("Specialize NatExact", "Quadruple NatExact"),
        "graded-bounded.hf": ("Specialize NatBound",),
        "graded-dependent-pair.hf": ("OpenStereo NatExact", "OpenBounded NatBound"),
    }
    closed_box = """module ClosedBox;
record Box<T, grade q : NatExact>(T Value @ q);
definition Nat ReadTwice(Nat n @ NatExact(4)) =>
    match (Box<Nat, 2>(n + n)) as whole : Nat {
        Box(x) => x + x,
    };
"""
    with tempfile.TemporaryDirectory(prefix="holdfast-default-grades-") as temporary:
        directory = Path(temporary)
        source = directory / "Candidate.hf"
        proof = directory / "Generated.v"
        cases = [(fixtures / name, labels) for name, labels in definitions.items()]
        for domain, allowance in (("NatExact", "4"), ("NatBound", "5")):
            candidate = directory / f"Closed{domain}.hf"
            candidate.write_text(closed_box.replace("NatExact(4)", f"{domain}({allowance})")
                                 .replace("NatExact", domain), encoding="utf-8")
            cases.append((candidate, (f"ReadTwice {domain}",)))
        for candidate, labels in cases:
            status, output, error = _elaborate_command(candidate)
            ensure(status == 0 and all(f"Graded replay {label}: SHA256" in output for label in labels), error)
            proof.write_text(output, encoding="utf-8")
            kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
            ensure(kernel.returncode == 0, kernel.stderr)
        callback_header = "module Callback;\ndefinition Nat Call(Fn(Nat n @ NatExact(1)) -> Nat f @ NatExact(1)) => f(0);\n"
        callback_positive = directory / "CallbackPositive.hf"
        callback_positive.write_text(callback_header, encoding="utf-8")
        status, output, error = _elaborate_command(callback_positive)
        ensure(status == 0 and "Graded replay Call NatExact: SHA256" in output, error)
        proof.write_text(output, encoding="utf-8")
        kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
        ensure(kernel.returncode == 0, kernel.stderr)
        box_interface = (
            closed_box
            + "definition Box<Nat, 2> Escape(Nat n @ NatExact(2)) => Box<Nat, 2>(n);\n"
            + "definition Nat UseEscape(Nat n @ NatExact(2)) => match (Escape(n)) as whole : Nat { Box(x) => x + x, };\n"
        )
        box_positive = directory / "BoxInterfacePositive.hf"
        box_positive.write_text(box_interface, encoding="utf-8")
        status, output, error = _elaborate_command(box_positive)
        ensure(status == 0 and all(f"Graded replay {name} NatExact: SHA256" in output
                                   for name in ("ReadTwice", "Escape", "UseEscape")), error)
        proof.write_text(output, encoding="utf-8")
        kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
        ensure(kernel.returncode == 0, kernel.stderr)
        for candidate, message in (
            ((fixtures / "graded-dependent.hf").read_text(encoding="utf-8")
             .replace("NatExact(4)", "NatExact(3)"), "fails exact computation demand"),
            (closed_box.replace("NatExact(4)", "NatBound(3)").replace("NatExact", "NatBound"),
             "fails bounded computation demand"),
            (closed_box + "definition Nat Unchecked(Nat n) => Box<Nat, 2>(n).Value;\n",
             "graded Box operations require an annotated pure definition"),
            (box_interface + "definition Nat Unchecked(Nat n) => Escape(n).Value;\n",
             "uses a graded Box interface and requires a checked caller"),
            (box_interface.replace("UseEscape(Nat n @ NatExact(2))", "UseEscape(Nat n @ NatExact(1))"),
             "fails exact computation demand"),
            (callback_header + "definition Nat Unchecked() => Call((Nat n) => n);\n",
             "accepts a graded callback and requires a checked caller"),
            (callback_header + "definition Nat BadGrade(Nat x @ NatExact(0)) => Call((Nat n @ NatExact(2)) => n + n);\n",
             "fails exact computation demand"),
        ):
            source.write_text(candidate, encoding="utf-8")
            status, output, error = _elaborate_command(source)
            ensure(status == 1 and not output and message in error, error)


def _demand(bindings: list[dict[str, object]]) -> list[tuple[object, object, object]]:
    return [(binding["name"], binding["computation"], binding["type"]) for binding in bindings]


def _value_application() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-application.hf"
    raw = source.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-application-") as temporary:
        directory = Path(temporary)
        candidate = directory / source.name
        proof = directory / "Generated.v"
        for domain, spelling in (("NatExact", "Preserve"), ("NatBound", "(Preserve)")):
            text = raw.replace("NatExact", domain).replace("Preserve(n + n, values)", f"{spelling}(n + n, values)")
            candidate.write_text(text, encoding="utf-8")
            status, output, error = _elaborate_command(candidate)
            ensure(status == 0 and all(f"Graded replay {name} {domain}: SHA256" in output
                                       for name in ("Preserve", "Route", "Run")), error)
            proof.write_text(output + """
Import HoldFast_GradedApplication.
Example route_preserves_samples : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d1_Route n values = values.
Proof. reflexivity. Qed.
Example run_doubles_seed : forall n, holdfast_d2_Run n = n + n.
Proof. reflexivity. Qed.
""", encoding="utf-8")
            kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, check=False, timeout=30)
            ensure(kernel.returncode == 0, kernel.stderr)

            status, output, error = _source_command(candidate, "Route", "--domain", domain)
            ensure(status == 0, error)
            result = json.loads(output)
            n, values = result["binders"]
            ensure(_demand([n, values]) == [("n", 0, 4), ("values", 1, 0)], "wrong dependent call demands")
            row = [{"name": "n", "uses": 2, "span": n["span"]}]
            ensure(values["annotation_type_uses"] == result["result_type_uses"] == row,
                   "application did not preserve the vector dependency")
            ensure(result["dependencies"] == ["Preserve"], "named call lost its checked dependency")

            status, output, error = _source_command(candidate, "Run", "--domain", domain)
            ensure(status == 0 and _demand(json.loads(output)["binders"]) == [("seed", 2, 0)], error)

        for before, after in (
            ("Preserve(n + n, values)", "Preserve(n, values)"),
            ("(Nat argument @ NatExact(2)) => argument + argument", "(Nat argument @ NatExact(1)) => argument"),
        ):
            candidate.write_text(raw.replace(before, after), encoding="utf-8")
            status, output, error = _elaborate_command(candidate)
            ensure(status == 1 and not output and "fails exact computation demand" in error, error)


def _graded_let() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-let.hf"
    raw = source.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-let-") as temporary:
        directory = Path(temporary)
        candidate = directory / source.name
        proof = directory / "Generated.v"
        for domain, local_allowance in (("NatExact", 2), ("NatBound", 3)):
            text = raw.replace("local @ NatExact(2)", f"local @ {domain}({local_allowance})").replace("NatExact", domain)
            candidate.write_text(text, encoding="utf-8")
            status, output, error = _elaborate_command(candidate)
            ensure(status == 0 and all(f"Graded replay {name} {domain}: SHA256" in output
                                       for name in ("Repeat", "Unused", "Shape")), error)
            proof.write_text(output + """
Import HoldFast_GradedLet.
Example repeat_value : forall n, holdfast_d0_Repeat n = (n + n) + (n + n).
Proof. reflexivity. Qed.
Example unused_value : forall n, holdfast_d1_Unused n = 7.
Proof. reflexivity. Qed.
Example keep_shape : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d2_Shape n values = values.
Proof. reflexivity. Qed.
""", encoding="utf-8")
            replay = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, check=False, timeout=30)
            ensure(replay.returncode == 0, replay.stderr)

            for name in ("Repeat", "Unused"):
                status, output, error = _source_command(candidate, name, "--domain", domain)
                ensure(status == 0, error)
                result = json.loads(output)
                ensure(_demand(result["binders"]) == [("n", 2, 0)] and "LetNat" in result["gallina"],
                       f"{name} lost the initializer's demand")
            status, output, error = _source_command(candidate, "Shape", "--domain", domain)
            ensure(status == 0, error)
            result = json.loads(output)
            n, values = result["binders"]
            ensure(_demand([n, values]) == [("n", 2, 4), ("values", 1, 0)], "wrong specialized let demands")
            row = [{"name": "n", "uses": 2, "span": n["span"]}]
            ensure(values["annotation_type_uses"] == result["result_type_uses"] == row,
                   "let substitution did not preserve the dependent rows")

            for change, failure in (
                (text.replace(f"local @ {domain}({local_allowance})", f"local @ {domain}(1)"), "computation demand"),
                (text.replace(f"Unused(Nat n @ {domain}(2))", f"Unused(Nat n @ {domain}(0))"), "computation demand"),
                (text.replace("(n + n)>", "n>"), "differs from the declared dependent type"),
            ):
                candidate.write_text(change, encoding="utf-8")
                status, output, error = _elaborate_command(candidate)
                ensure(status == 1 and not output and failure in error, error)


def _verify_source_certificate(directory: Path, kernel_hashes: dict[str, str], certificate: str,
                               soundness_theorem: str, stale_row: tuple[str, str]) -> None:
    compiler = [*proofenv.rocq_command(), "-q"]
    support = ("graded_pure.v", "graded_domains.v", "graded_source.v")
    ensure(set(kernel_hashes) == set(support), "wrong Rocq support closure")
    for name in support:
        unit = TOOLS / "rocq" / name
        ensure(hashlib.sha256(unit.read_bytes()).hexdigest() == kernel_hashes[name], f"unbound Rocq support {name}")
        shutil.copyfile(unit, directory / name)
        subprocess.run([*compiler, name], cwd=directory, check=True, timeout=30)
    unit = directory / "SourceProof.v"
    unit.write_text(certificate, encoding="utf-8")
    subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True, check=True, timeout=30)
    audit = directory / "SourceAudit.v"
    audit.write_text("Require Import SourceProof graded_source.\n"
                     f"Print Assumptions GradedSource.{soundness_theorem}.\n"
                     "Print Assumptions source_rows_match.\n", encoding="utf-8")
    replay = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                            text=True, encoding="utf-8", check=True, timeout=30)
    solver_ledger.audit(replay.stdout, 2, "GradedSource", ())
    stale = certificate.replace(*stale_row)
    ensure(stale != certificate, "certificate control left the alleged demand unchanged")
    unit.write_text(stale, encoding="utf-8")
    refused = subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True,
                             text=True, encoding="utf-8", check=False, timeout=30)
    ensure(refused.returncode != 0 and "Unable to unify" in refused.stderr, refused.stderr)


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
    ensure(result["domain"] == "NatExact", "default source grade domain changed")
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

        _verify_source_certificate(directory, result["kernel_sha256"], result["gallina"],
                                   "source_check_sound", ("[0; 0; 4]", "[0; 0; 3]"))


def _bounded_source_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-bounded.hf"
    raw = source.read_bytes()
    domain = ("--domain", "NatBound")
    status, output, error = _source_command(source, "Specialize", *domain)
    ensure(status == 0, error)
    result = json.loads(output)
    ensure(result["domain"] == "NatBound" and result["source_sha256"] == hashlib.sha256(raw).hexdigest(),
           "bounded certificate lost its grade domain or source bytes")
    n, values = result["binders"]
    ensure(_demand([n, values]) == [("n", 0, 4), ("values", 2, 0)], "wrong bounded signature")
    row = [{"name": "n", "uses": 2, "span": n["span"]}]
    ensure(values["annotation_type_uses"] == row and result["result_type_uses"] == row,
           "bounded checking changed exact type dependencies")
    ensure(result["dependencies"] == ["PreserveLength"], "bounded source dependency was lost")

    status, output, error = _source_command(source, "ScalePublishedBound", *domain)
    ensure(status == 0, error)
    ensure(_demand(json.loads(output)["binders"]) == [("n", 4, 0)], "wrong published application bound")
    status, output, error = _source_command(source, "Specialize")
    ensure(status == 1 and not output and "explicit @ NatExact(n) allowance" in error, error)

    with tempfile.TemporaryDirectory(prefix="holdfast-bounded-source-controls-") as temporary:
        directory = Path(temporary)
        changed = directory / source.name
        for declaration, original, replacement, failure in (
            ("Specialize", b"Nat size @ NatBound(0)", b"Nat size @ NatExact(0)", "explicit @ NatBound(n) allowance"),
            ("Specialize", b"items @ NatBound(2)", b"items @ NatBound(0)", "bounded computation demand"),
            ("ScalePublishedBound", b"=> x)(n + n)", b"=> x + x + x)(n + n)", "bounded computation demand"),
            ("ScalePublishedBound", b"Nat n @ NatBound(4)", b"Nat n @ NatBound(3)", "bounded computation demand"),
        ):
            ensure(raw.count(original) == 1, f"source control does not identify one occurrence: {original!r}")
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, declaration, *domain)
            ensure(status == 1 and not output and failure in error, error)

        changed.write_bytes(raw.replace(b"NatBound", b"NatExact"))
        status, output, error = _source_command(changed, "Specialize")
        ensure(status == 1 and not output and "exact computation demand" in error, error)
        _verify_source_certificate(directory, result["kernel_sha256"], result["gallina"],
                                   "bounded_source_check_sound", ("[0; 0; 4]", "[0; 0; 3]"))


def _type_identity_source_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-type-identity.hf"
    raw = source.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-type-identity-") as temporary:
        directory = Path(temporary)
        candidate = directory / source.name
        proof = directory / "Generated.v"
        for domain in ("NatExact", "NatBound"):
            text = raw.replace("NatExact", domain)
            candidate.write_text(text, encoding="utf-8")

            status, output, error = _source_command(candidate, "Identity", "--domain", domain)
            ensure(status == 0, error)
            id_report = json.loads(output)
            a, x = id_report["binders"]
            ensure(_demand([a, x]) == [("a", 0, 2), ("x", 1, 0)], f"wrong Identity demands: {id_report}")
            a_row = [{"name": "a", "uses": 1, "span": a["span"]}]
            ensure(x["annotation_type_uses"] == id_report["result_type_uses"] == a_row,
                   "type-valued identity lost type dependency rows")

            status, output, error = _source_command(candidate, "KeepDouble", "--domain", domain)
            ensure(status == 0, error)
            keep_report = json.loads(output)
            n, values = keep_report["binders"]
            ensure(_demand([n, values]) == [("n", 0, 4), ("values", 1, 0)],
                   f"wrong KeepDouble demands: {keep_report}")
            n_row = [{"name": "n", "uses": 2, "span": n["span"]}]
            ensure(values["annotation_type_uses"] == keep_report["result_type_uses"] == n_row,
                   "type-identity specialization lost vector dependency rows")
            ensure(keep_report["dependencies"] == ["Identity"], "KeepDouble lost Identity dependency")

            status, output, error = _source_command(candidate, "Relay", "--domain", domain)
            ensure(status == 0, error)
            relay_report = json.loads(output)
            ensure(_demand(relay_report["binders"]) == [("a", 0, 2), ("x", 1, 0)],
                   f"wrong Relay demands: {relay_report}")

            status, gallina, error = _elaborate_command(candidate)
            ensure(status == 0 and all(f"Graded replay {name} {domain}: SHA256" in gallina
                                       for name in ("Identity", "KeepDouble", "Relay")), error)
            proof.write_text(gallina + """
Import HoldFast_GradedTypeIdentity.
Theorem keep_double_returns_values : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d1_KeepDouble n values = values.
Proof. reflexivity. Qed.
Print Assumptions keep_double_returns_values.
""", encoding="utf-8")
            kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
            ensure(kernel.returncode == 0, kernel.stderr)
            solver_ledger.audit(kernel.stdout, 1, f"GradedTypeIdentity_{domain}", ())

        for declaration, original, replacement, failure in (
            ("KeepDouble", "Identity(type Vec<Nat, (n + n)>, values)", "Identity(type Type, values)", "computation demand"),
            ("Identity", "Type a @ NatExact(0)", "Type a @ NatExact(1)", "exact computation demand"),
            ("Identity", "a x @ NatExact(1)", "a x @ NatExact(2)", "exact computation demand"),
            ("KeepDouble", "Identity(type Vec<Nat, (n + n)>, values)", "Identity(type Vec<Nat, n>, values)",
             "natural-index checking"),
            ("KeepDouble", "public definition Vec<Nat, (n + n)> KeepDouble",
             "public definition Vec<Nat, n> KeepDouble", "declared dependent type"),
        ):
            ensure(original in raw, f"missing type-identity control: {original!r}")
            candidate.write_text(raw.replace(original, replacement), encoding="utf-8")
            status, output, error = _source_command(candidate, declaration)
            ensure(status == 1 and not output and ": grade: " in error and failure in error, error)

        _verify_source_certificate(directory, keep_report["kernel_sha256"], keep_report["gallina"],
                                   "bounded_source_check_sound", ("[0; 0; 4]", "[0; 0; 3]"))


def cases() -> list[Case]:
    return [Case("pure dependent usage and telescope substitution replay",
                 partial(_replay, "graded_pure", "GradedPure", _PURE_PROOFS), lane="toolchain"),
            Case("ordered grade domains and dependent row certificates",
                 partial(_replay, "graded_domains", "GradedDomains", _DOMAIN_PROOFS, ("graded_pure",)),
                 lane="toolchain"),
            Case("source-bound exact grades and dependent partial application replay", _source_replay, lane="toolchain"),
            Case("source-bound natural bounds and exact type dependencies", _bounded_source_replay, lane="toolchain"),
            Case("graded type-valued identity and universe specialization replay", _type_identity_source_replay,
                 lane="toolchain"),
            Case("graded value application preserves dependent and callable argument types", _value_application,
                 lane="toolchain"),
            Case("graded let sequences the initializer and substitutes independent type demand", _graded_let,
                 lane="toolchain"),
            Case("default elaboration checks source grades before Gallina emission", _default_source_replay, lane="toolchain")]
