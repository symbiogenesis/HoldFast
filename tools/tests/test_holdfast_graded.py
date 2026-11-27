# SPDX-License-Identifier: Apache-2.0
"""Replay the pure graded kernel trial and audit its principal proofs."""

import contextlib
import hashlib
import io
import json
import subprocess
import tempfile
import time
from pathlib import Path
from unittest.mock import patch

from tests.harness import TOOLS, Case, ensure
from toolchain import elaborate as hf_elaborate
from toolchain import graded_source, proofenv, rocq_cache, solver_ledger
from toolchain import parser as hf_parser
from toolchain.cli.holdfast_parser import main as parser_main

INDEPENDENT_CASES = True

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
            generated: tuple[tuple[str, str], ...] = (), *,
            batch: rocq_cache.BatchChecker | None = None) -> None:
    compile_unit = [*proofenv.rocq_command(), "-q"]
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-graded-")))
        else:
            directory = batch.work_dir
        units = [
            *((f"{name}.v", gallina.encode("utf-8")) for name, gallina in generated),
            *((f"{name}.v", (TOOLS / "rocq" / f"{name}.v").read_bytes()) for name in (*dependencies, unit)),
        ]
        rocq_cache.materialize_units(directory, units, compiler=compile_unit)
        audit_stem = batch.unique_stem(f"GradeAudit_{unit}") if batch is not None else "GradeAudit"
        audit = directory / f"{audit_stem}.v"
        audit.write_text(f"Require Import {unit}.\n" + "".join(
            f"Print Assumptions {module}.{name}.\n" for name in proofs), encoding="utf-8")
        report = subprocess.run([*compile_unit, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=180)
        solver_ledger.audit(report.stdout, len(proofs), module, ())
        if batch is not None:
            batch.register(unit)
        else:
            rocq_cache.check_kernel(directory, [unit])


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
            unit_text, _ = rocq_cache.use_cached_prelude(output, directory)
            proof.write_text(unit_text, encoding="utf-8")
            kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
            ensure(kernel.returncode == 0, kernel.stderr)
        callback_header = "module Callback;\ndefinition Nat Call(Fn(Nat n @ NatExact(1)) -> Nat f @ NatExact(1)) => f(0);\n"
        callback_positive = directory / "CallbackPositive.hf"
        callback_positive.write_text(callback_header, encoding="utf-8")
        status, output, error = _elaborate_command(callback_positive)
        ensure(status == 0 and "Graded replay Call NatExact: SHA256" in output, error)
        unit_text, _ = rocq_cache.use_cached_prelude(output, directory)
        proof.write_text(unit_text, encoding="utf-8")
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
        unit_text, _ = rocq_cache.use_cached_prelude(output, directory)
        proof.write_text(unit_text, encoding="utf-8")
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
            unit_text, _ = rocq_cache.use_cached_prelude(output + """
Import HoldFast_GradedApplication.
Example route_preserves_samples : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d1_Route n values = values.
Proof. reflexivity. Qed.
Example run_doubles_seed : forall n, holdfast_d2_Run n = n + n.
Proof. reflexivity. Qed.
""", directory)
            proof.write_text(unit_text, encoding="utf-8")
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
        for domain, repeat_n, local_allowance in (("NatExact", 4, 2), ("NatBound", 6, 3)):
            text = (
                raw.replace("Repeat(Nat n @ NatExact(4))", f"Repeat(Nat n @ {domain}({repeat_n}))")
                .replace("local @ NatExact(2)", f"local @ {domain}({local_allowance})")
                .replace("NatExact", domain)
            )
            candidate.write_text(text, encoding="utf-8")
            status, output, error = _elaborate_command(candidate)
            ensure(status == 0 and all(f"Graded replay {name} {domain}: SHA256" in output
                                       for name in ("Repeat", "Unused", "Shape")), error)
            unit_text, _ = rocq_cache.use_cached_prelude(output + """
Import HoldFast_GradedLet.
Example repeat_value : forall n, holdfast_d0_Repeat n = (n + n) + (n + n).
Proof. reflexivity. Qed.
Example unused_value : forall n, holdfast_d1_Unused n = 7.
Proof. reflexivity. Qed.
Example keep_shape : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d2_Shape n values = values.
Proof. reflexivity. Qed.
""", directory)
            proof.write_text(unit_text, encoding="utf-8")
            replay = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, check=False, timeout=30)
            ensure(replay.returncode == 0, replay.stderr)

            for name, expected_n in (("Repeat", ("n", repeat_n, 0)), ("Unused", ("n", 0, 0))):
                status, output, error = _source_command(candidate, name, "--domain", domain)
                ensure(status == 0, error)
                result = json.loads(output)
                ensure(_demand(result["binders"]) == [expected_n] and "CLet" in result["gallina"],
                       f"{name} lost the initializer's demand")
            status, output, error = _source_command(candidate, "Shape", "--domain", domain)
            ensure(status == 0, error)
            result = json.loads(output)
            n, values = result["binders"]
            ensure(_demand([n, values]) == [("n", 0, 4), ("values", 1, 0)], "wrong specialized let demands")
            row = [{"name": "n", "uses": 2, "span": n["span"]}]
            ensure(values["annotation_type_uses"] == result["result_type_uses"] == row,
                   "let substitution did not preserve the dependent rows")

            negative_cases = [
                (text.replace(f"local @ {domain}({local_allowance})", f"local @ {domain}(1)"), "computation demand"),
                (
                    text.replace("(n + n)>", "n>"),
                    "type-use demand" if domain == "NatExact" else "differs from the declared dependent type",
                ),
            ]
            if domain == "NatExact":
                negative_cases.append(
                    (text.replace("Unused(Nat n @ NatExact(0))", "Unused(Nat n @ NatExact(2))"), "computation demand")
                )
            for change, failure in negative_cases:
                candidate.write_text(change, encoding="utf-8")
                status, output, error = _elaborate_command(candidate)
                ensure(status == 1 and not output and failure in error, error)


def _verify_source_certificate(directory: Path, kernel_hashes: dict[str, str], certificate: str,
                               soundness_theorem: str, stale_row: tuple[str, str]) -> None:
    _ = stale_row
    compiler = [*proofenv.rocq_command(), "-q"]
    support = ("graded_pure.v", "graded_domains.v", "graded_core.v", "graded_core_source.v")
    ensure(set(kernel_hashes) == set(support), f"wrong Rocq support closure: {set(kernel_hashes)}")
    for name in support:
        unit = TOOLS / "rocq" / name
        ensure(hashlib.sha256(unit.read_bytes()).hexdigest() == kernel_hashes[name], f"unbound Rocq support {name}")
    rocq_cache.materialize_repo_units(TOOLS.parent, directory, support, compiler=compiler)
    core_thm = (
        "source_check_core_sound"
        if soundness_theorem == "source_check_sound"
        else "source_check_core_sub_sound"
    )
    unit = directory / "SourceProof.v"
    unit.write_text(certificate, encoding="utf-8")
    subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True, check=True, timeout=30)
    audit = directory / "SourceAudit.v"
    audit.write_text("Require Import SourceProof graded_core_source.\n"
                     f"Print Assumptions GradedCoreSource.{core_thm}.\n"
                     "Print Assumptions source_rows_match.\n", encoding="utf-8")
    replay = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                            text=True, encoding="utf-8", check=True, timeout=30)
    solver_ledger.audit(replay.stdout, 2, "GradedCoreSource", ())
    marker = "Example source_rows_match : source_reports = "
    head, tail = certificate.split(marker, 1)
    stale = head + marker + (
        tail.replace("Ok [", "Err (ErrBranchMismatch 99) :: [", 1)
        if "Ok [" in tail
        else tail.replace("source_reports = [", "source_reports = [", 1)
    )
    if stale == certificate:
        stale = certificate.replace("source_reports = [", "source_reports = [Err (ErrBranchMismatch 99); ", 1)
    ensure(stale != certificate, "certificate control left the alleged demand unchanged")
    unit.write_text(stale, encoding="utf-8")
    refused = subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True,
                             text=True, encoding="utf-8", check=False, timeout=30)
    ensure(refused.returncode != 0, refused.stderr)


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
            unit_text, _ = rocq_cache.use_cached_prelude(gallina + """
Import HoldFast_GradedTypeIdentity.
Theorem keep_double_returns_values : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d1_KeepDouble n values = values.
Proof. reflexivity. Qed.
Print Assumptions keep_double_returns_values.
""", directory)
            proof.write_text(unit_text, encoding="utf-8")
            kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                    capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
            ensure(kernel.returncode == 0, kernel.stderr)
            solver_ledger.audit(kernel.stdout, 1, f"GradedTypeIdentity_{domain}", ())

        for declaration, original, replacement, failure in (
            ("KeepDouble", "Identity(type Vec<Nat, (n + n)>, values)", "Identity(type Type, values)", "declared dependent type"),
            ("Identity", "Type a @ NatExact(0)", "Type a @ NatExact(1)", "exact computation demand"),
            ("Identity", "a x @ NatExact(1)", "a x @ NatExact(2)", "exact computation demand"),
            ("KeepDouble", "Identity(type Vec<Nat, (n + n)>, values)", "Identity(type Vec<Nat, n>, values)",
             "declared dependent type"),
            ("KeepDouble", "public definition Vec<Nat, (n + n)> KeepDouble",
             "public definition Vec<Nat, n> KeepDouble", "declared dependent type"),
        ):
            ensure(original in raw, f"missing type-identity control: {original!r}")
            candidate.write_text(raw.replace(original, replacement), encoding="utf-8")
            status, output, error = _source_command(candidate, declaration)
            ensure(status == 1 and not output and ": grade: " in error and failure in error, error)

        _verify_source_certificate(directory, keep_report["kernel_sha256"], keep_report["gallina"],
                                   "bounded_source_check_sound", ("[0; 0; 4]", "[0; 0; 3]"))


def _support_cache_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-support-cache-") as temporary:
        base = Path(temporary)
        repo = base / "repo"
        rocq_dir = repo / "tools" / "rocq"
        rocq_dir.mkdir(parents=True)
        (rocq_dir / "graded_pure.v").write_text("(* pure *)\n", encoding="utf-8")
        (rocq_dir / "graded_domains.v").write_text("(* domains *)\n", encoding="utf-8")
        cache = base / "cache"
        files = ("graded_pure.v", "graded_domains.v")
        compiled_calls: list[str] = []

        def fake_rocq(_compiler: list[str], directory: Path, name: str) -> subprocess.CompletedProcess[str]:
            compiled_calls.append(name)
            (directory / f"{Path(name).stem}.vo").write_bytes(b"vo:" + (directory / name).read_bytes())
            return subprocess.CompletedProcess(["rocq"], 0, "", "")

        with (patch.object(graded_source, "_support_cache_root", return_value=cache),
              patch.object(graded_source, "_compiler_sha256", return_value="c" * 64),
              patch.object(graded_source, "_run_rocq", side_effect=fake_rocq)):
            out1 = base / "out1"
            out1.mkdir()
            graded_source._support(repo, ["rocq", "c"], out1, files)
            ensure(len(compiled_calls) == 2 and (out1 / "graded_pure.vo").is_file(),
                   "cold support build did not compile and materialize .vo artifacts")

            out2 = base / "out2"
            out2.mkdir()
            graded_source._support(repo, ["rocq", "c"], out2, files)
            ensure(len(compiled_calls) == 2 and (out2 / "graded_domains.vo").is_file(),
                   "warm support hit recompiled unchanged .v files")

            entries = [entry for entry in cache.iterdir() if entry.is_dir()]
            ensure(len(entries) == 1, f"expected one cache entry, found {len(entries)}")
            (entries[0] / "graded_pure.vo").write_bytes(b"corrupted")
            out3 = base / "out3"
            out3.mkdir()
            graded_source._support(repo, ["rocq", "c"], out3, files)
            ensure(len(compiled_calls) == 4 and (out3 / "graded_pure.vo").read_bytes().startswith(b"vo:"),
                   "corrupted cached .vo was reused without rebuilding")

            (rocq_dir / "graded_pure.v").write_text("(* pure v2 *)\n", encoding="utf-8")
            out4 = base / "out4"
            out4.mkdir()
            graded_source._support(repo, ["rocq", "c"], out4, files)
            ensure(len(compiled_calls) == 6 and len([entry for entry in cache.iterdir() if entry.is_dir()]) == 2,
                   "editing support source did not invalidate the cache key")


def _type_grades_and_presence_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-type-grades.hf"
    raw = source.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-type-grades-") as temporary:
        directory = Path(temporary)
        candidate = directory / source.name
        proof = directory / "Generated.v"

        status, output, error = _source_command(source, "KeepDouble")
        ensure(status == 0, error)
        report = json.loads(output)
        ensure(_demand(report["binders"]) == [("n", 0, 4), ("values", 1, 0)], f"wrong KeepDouble grades: {report}")

        status, output, error = _source_command(source, "ShareLength")
        ensure(status == 0, error)
        shared = json.loads(output)
        ensure(_demand(shared["binders"]) == [("n", 0, 6), ("left", 1, 0), ("right", 0, 0)],
               f"wrong ShareLength grades: {shared}")

        status, gallina, error = _elaborate_command(source)
        ensure(status == 0 and all(f"Graded replay {name} NatExact: SHA256" in gallina
                                   for name in ("Identity", "KeepDouble", "Relay", "ShareLength")), error)
        unit_text, _ = rocq_cache.use_cached_prelude(gallina + """
Import HoldFast_GradedTypeGrades.
Theorem keep_double_id : forall n (values : holdfast_Vec nat (n + n)),
  holdfast_d1_KeepDouble n values = values.
Proof. reflexivity. Qed.
Print Assumptions keep_double_id.
""", directory)
        proof.write_text(unit_text, encoding="utf-8")
        kernel = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                                capture_output=True, text=True, encoding="utf-8", check=False, timeout=30)
        ensure(kernel.returncode == 0, kernel.stderr)
        solver_ledger.audit(kernel.stdout, 1, "GradedTypeGrades", ())

        for original, replacement, failure in (
            ("Type a @ NatExact(0, 2)", "Type a @ NatExact(0, 1)", "fails exact type-use demand"),
            ("Type a @ NatExact(0, 2)", "Type a @ NatExact(0, 3)", "fails exact type-use demand"),
            ("a x @ NatExact(1, 0)", "a x @ NatExact(1, 1)", "fails exact type-use demand"),
            ("Nat n @ NatExact(0, 4)", "Nat n @ NatExact(0, 2)", "fails exact type-use demand"),
            ("Nat n @ NatExact(0, 6)", "Nat n @ NatExact(0, 4)", "fails exact type-use demand"),
        ):
            ensure(original in raw, f"missing (s, r) control: {original!r}")
            candidate.write_text(raw.replace(original, replacement), encoding="utf-8")
            status, output, error = _elaborate_command(candidate)
            ensure(status == 1 and not output and failure in error, error)

        bounded = raw.replace("NatExact(0, 4)", "NatBound(0, 5)").replace("NatExact", "NatBound")
        candidate.write_text(bounded, encoding="utf-8")
        status, output, error = _source_command(candidate, "KeepDouble", "--domain", "NatBound")
        ensure(status == 0, error)
        candidate.write_text(bounded.replace("NatBound(0, 5)", "NatBound(0, 3)"), encoding="utf-8")
        status, output, error = _source_command(candidate, "KeepDouble", "--domain", "NatBound")
        ensure(status == 1 and not output and "fails bounded type-use demand" in error, error)

        presence = (
            raw.replace("NatExact(0, 2)", "Presence(0, 1)")
            .replace("NatExact(0, 4)", "Presence(0, 1)")
            .replace("NatExact(0, 6)", "Presence(0, 1)")
            .replace("NatExact", "Presence")
        )
        candidate.write_text(presence, encoding="utf-8")
        status, output, error = _source_command(candidate, "KeepDouble", "--domain", "Presence")
        ensure(status == 0, error)
        presence_report = json.loads(output)
        ensure(presence_report["domain"] == "Presence", "wrong Presence domain in report")
        _verify_source_certificate(directory, presence_report["kernel_sha256"], presence_report["gallina"],
                                   "presence_source_check_sound", ("[0; 0; 4]", "[0; 0; 3]"))

        candidate.write_text(presence.replace("Nat n @ Presence(0, 1)", "Nat n @ Presence(0, 0)", 1), encoding="utf-8")
        status, output, error = _source_command(candidate, "KeepDouble", "--domain", "Presence")
        ensure(status == 1 and not output and "fails presence type-use demand" in error, error)

        let_ok = ("module LetTypeGrade;\n"
                  "definition Nat Good(Nat n @ NatExact(1, 0)) => let Nat x @ NatExact(1, 0) = n in x;\n")
        candidate.write_text(let_ok, encoding="utf-8")
        status, output, error = _source_command(candidate, "Good")
        ensure(status == 0, error)

        let_bad_type = ("module LetTypeGrade;\n"
                        "definition Nat BadType(Nat n @ NatExact(1, 0)) => let Nat x @ NatExact(1, 1) = n in x;\n")
        candidate.write_text(let_bad_type, encoding="utf-8")
        status, output, error = _source_command(candidate, "BadType")
        ensure(status == 1 and not output and "fails exact type-use demand" in error, error)


def _domains_and_grade_polymorphism() -> None:
    dom_poly = TOOLS / "tests" / "fixtures" / "graded-domains-polymorphism.hf"
    ind_fam = TOOLS / "tests" / "fixtures" / "graded-inductive-families.hf"

    for decl, extra in (
        ("UseTiny", ()),
        ("NestedMul", ()),
        ("PromAdd", ()),
        ("MixedPoly", ()),
        ("InferLocal", ("--infer-grades",)),
    ):
        status, output, error = _source_command(dom_poly, decl, *extra)
        ensure(status == 0, f"{decl}: {error}")
        report = json.loads(output)
        ensure(report["status"] == "checked" and report["scope"] == "graded-core-source", f"wrong status/scope for {decl}: {report}")
        if decl == "UseTiny":
            ensure(report["domain"] == "TinyNat", f"expected TinyNat domain: {report['domain']}")
        if decl == "InferLocal":
            ensure(bool(report.get("inferred_grades")), f"expected inferred_grades metadata: {report}")

    with tempfile.TemporaryDirectory(prefix="holdfast-domains-cli-") as temporary:
        directory = Path(temporary)
        # Standalone Linear / Affine / SecurityLoHi checks
        for name, dom, body in (
            ("LinId", "Linear", "definition Nat LinId(Nat x @ Linear(LOne)) => x;\n"),
            ("AffDrop", "Affine", "definition Nat AffDrop(Nat x @ Affine(AOne), Nat y @ Affine(AZero)) => x;\n"),
            ("SecHi", "SecurityLoHi", "definition Nat SecHi(Nat lo @ SecurityLoHi(Lo), Nat hi @ SecurityLoHi(Hi)) => hi;\n"),
        ):
            p = directory / f"{name}.hf"
            p.write_text(f"module {name};\n{body}", encoding="utf-8")
            st, out, err = _source_command(p, name, "--domain", dom)
            ensure(st == 0 and json.loads(out)["domain"] == dom, f"{name}/{dom}: {err}")

        # Negative exact per-binder span diagnostic + `@ _` residual failure
        bad_demand = directory / "BadBinder.hf"
        bad_demand.write_text(
            "module BadBinder;\ndefinition Nat F(Nat x @ NatExact(2), Nat y @ NatExact(1)) => x + y;\n",
            encoding="utf-8",
        )
        st, out, err = _source_command(bad_demand, "F")
        ensure(st == 1 and not out and ":2:18: grade: binder 'x' fails exact computation demand (expected 2, got 1)" in err, err)

        bad_hole = directory / "BadHole.hf"
        bad_hole.write_text(
            "module BadHole;\ndefinition Nat F(Nat x @ NatExact(1)) => let y @ _ = x in y + y;\n",
            encoding="utf-8",
        )
        st, out, err = _source_command(bad_hole, "F", "--infer-grades")
        ensure(st == 1 and not out and ":2:18: grade: binder 'x'" in err, err)

        # Elaborate graded-domains-polymorphism.hf with --infer-grades and compile in Rocq with erasure audit
        out_io, err_io = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out_io), contextlib.redirect_stderr(err_io):
            st = parser_main(["elaborate", str(dom_poly), "--infer-grades"])
        ensure(st == 0, err_io.getvalue())
        gallina_poly = out_io.getvalue()
        ensure("_erased_UseTiny_correspondence" in gallina_poly and "_erased_InferLocal_correspondence" in gallina_poly,
               "missing CBV erasure correspondence in elaborated Gallina")
        poly_text, _ = rocq_cache.use_cached_prelude(
            gallina_poly + "\nImport HoldFast_GradedDomainsPoly.\n"
            "Print Assumptions holdfast_d25_erased_UseTiny_correspondence.\n"
            if "holdfast_d25_erased_UseTiny_correspondence" in gallina_poly else
            gallina_poly + "\nImport HoldFast_GradedDomainsPoly.\n"
            + "\n".join(
                f"Print Assumptions {line.split()[1]}."
                for line in gallina_poly.splitlines()
                if line.startswith("Theorem ") and "_erased_" in line and "_correspondence" in line
            ) + "\n",
            directory,
        )
        poly_v = directory / "PolyCheck.v"
        poly_v.write_text(poly_text, encoding="utf-8")
        erased_count = sum(
            1 for line in gallina_poly.splitlines()
            if line.startswith("Theorem ") and "_erased_" in line and "_correspondence" in line
        )
        ensure(erased_count >= 5, f"expected >= 5 CBV erasure correspondence theorems, got {erased_count}")
        rc = subprocess.run([*proofenv.rocq_command(), "-q", poly_v.name], cwd=directory,
                            capture_output=True, text=True, encoding="utf-8", check=True, timeout=60)
        solver_ledger.audit(rc.stdout, erased_count, "GradedDomainsPoly CBV erasure", ())

        # Elaborate graded-inductive-families.hf (GFin & MyVec) and compile in Rocq
        st_i, out_i, err_i = _elaborate_command(ind_fam)
        ensure(st_i == 0, err_i)
        ind_text, _ = rocq_cache.use_cached_prelude(out_i, directory)
        ind_v = directory / "IndCheck.v"
        ind_v.write_text(ind_text, encoding="utf-8")
        subprocess.run([*proofenv.rocq_command(), "-q", ind_v.name], cwd=directory,
                       capture_output=True, text=True, encoding="utf-8", check=True, timeout=60)

        # CLI derive-combinator & synthesize-graded with --verify-rocq
        for cli_args in (
            ["derive-combinator", "dist_pair", "--domain", "NatExact", "--verify-rocq"],
            ["derive-combinator", "flatten_box", "--domain", "NatBound", "--verify-rocq"],
            ["derive-combinator", "cross_mode", "--domain", "NatExact", "--payload-type", "Nat", "--verify-rocq"],
            ["synthesize-graded", "--goal", "Nat", "--var", "x:Nat@1", "--example", "0->1", "--example", "2->3", "--verify-rocq"],
        ):
            o, e = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(o), contextlib.redirect_stderr(e):
                cst = parser_main(cli_args)
            ensure(cst == 0, e.getvalue())
            cjson = json.loads(o.getvalue())
            ensure(cjson["status"] in {"derived", "synthesized"} and "gallina" in cjson, f"bad CLI JSON: {cjson}")


def _q25cb_zero_type_use_skip_and_benchmark() -> None:
    bench_hf = TOOLS / "tests" / "fixtures" / "graded-q25cb-benchmark.hf"
    source = bench_hf.read_bytes()
    root = TOOLS.parent
    with hf_parser.cached_build(root) as compiled:
        parsed = hf_parser.parse_source(compiled, source, surface=True)

    t0 = time.perf_counter()
    res_skip, elab_skip = hf_elaborate._checked_elaboration(source, parsed, enable_zero_type_use_skip=True)
    dt_skip = time.perf_counter() - t0

    t1 = time.perf_counter()
    res_noskip, elab_noskip = hf_elaborate._checked_elaboration(source, parsed, enable_zero_type_use_skip=False)
    dt_noskip = time.perf_counter() - t1

    ensure(res_skip.gallina == res_noskip.gallina,
           "Q25cb zero-type-use skipping changed the elaborated Gallina output")
    ensure(elab_skip.substitute_skips > 0,
           f"expected substitute_skips > 0 on multi-binder fixture, got {elab_skip.substitute_skips}")
    ensure(elab_skip.substitute_calls < elab_noskip.substitute_calls,
           f"expected fewer substitute() calls with skipping ({elab_skip.substitute_calls} vs {elab_noskip.substitute_calls})")
    cert_bytes = len(res_skip.gallina.encode("utf-8"))
    ensure(dt_skip >= 0.0 and dt_noskip >= 0.0 and cert_bytes > 0, "invalid Q25cb benchmark metrics")
    ensure("erased_dead=4" in res_skip.gallina and "_erased_CombineStageC_correspondence" in res_skip.gallina,
           "expected CombineStageC dead-binder CBV erasure in Gallina")

    with tempfile.TemporaryDirectory(prefix="holdfast-q25cb-") as temporary:
        directory = Path(temporary)
        corresp = [
            line.split()[1] for line in res_skip.gallina.splitlines()
            if line.startswith("Theorem ") and "_erased_" in line and "_correspondence" in line
        ]
        v_text, _ = rocq_cache.use_cached_prelude(
            res_skip.gallina + "\nImport HoldFast_GradedQ25cbBenchmark.\n"
            + "".join(f"Print Assumptions {thm}.\n" for thm in corresp),
            directory,
        )
        v = directory / "Q25cbVerify.v"
        v.write_text(v_text, encoding="utf-8")
        rc = subprocess.run([*proofenv.rocq_command(), "-q", v.name], cwd=directory,
                            capture_output=True, text=True, encoding="utf-8", check=True, timeout=60)
        solver_ledger.audit(rc.stdout, len(corresp), "Q25cb CBV erasure", ())


def _batch_checker_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-rocq-batch-ctrl-") as temporary:
        base = Path(temporary)
        batch = rocq_cache.BatchChecker(prefix="holdfast-batch-unit-")
        ensure(batch.unique_stem("Sample") == "Sample"
               and batch.unique_stem("Sample") == "Sample_2",
               "BatchChecker did not disambiguate duplicate stems")
        batch.register("unit_a")
        batch.register("unit_b")
        batch.register("unit_a")
        ensure(batch.units == ("unit_a", "unit_b"), "BatchChecker did not deduplicate registered units")
        work_dir = batch.work_dir
        ensure(work_dir.is_dir(), "BatchChecker did not create work_dir on access")
        fake_chk = base / "fake-rocqchk"
        fake_chk.write_text("#!/bin/sh\n", encoding="utf-8")
        seen_cmds: list[list[str]] = []

        def fake_run(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            seen_cmds.append(cmd)
            ensure(kwargs["cwd"] == work_dir, "rocqchk ran outside batch work_dir")
            return subprocess.CompletedProcess(cmd, 0, "", "")

        with (patch.dict("os.environ", {"VOS_ROCQCHK": str(fake_chk)}),
              patch.object(rocq_cache.subprocess, "run", side_effect=fake_run)):
            ensure(proofenv.rocqchk_command() == [str(fake_chk)], "VOS_ROCQCHK override was ignored")
            batch.verify_all()
        ensure(seen_cmds == [[str(fake_chk), "-silent", "unit_a", "unit_b"]],
               f"BatchChecker ran unexpected rocqchk command: {seen_cmds!r}")
        ensure(not work_dir.exists(), "BatchChecker did not clean up its temporary directory")


def _cached_prelude_controls() -> None:
    prelude = rocq_cache.prelude_source().decode("utf-8")
    ensure("From Stdlib Require Import Arith.PeanoNat Lia." in prelude
           and "From Stdlib Require Import ZArith.BinInt." in prelude,
           "prelude_source altered _PRELUDE directives unexpectedly")
    with tempfile.TemporaryDirectory(prefix="holdfast-prelude-ctrl-") as temporary:
        base = Path(temporary)
        out = base / "work"
        out.mkdir()
        plain = "Module Plain.\nDefinition x := 1.\nEnd Plain.\n"
        unchanged, used_plain = rocq_cache.use_cached_prelude(plain, out)
        ensure(not used_plain and unchanged == plain, "use_cached_prelude altered output without _PRELUDE")
        sample = ("(* header *)\nModule Sample.\n\n"
                  + rocq_cache.elaborate_types._PRELUDE
                  + "\nDefinition x := 1.\nEnd Sample.\n")
        fake_calls: list[str] = []

        def fake_materialize(directory: Path, **_kwargs: object) -> None:
            fake_calls.append(str(directory))
            (directory / "HoldFastPrelude.vo").write_bytes(b"vo")

        with patch.object(rocq_cache, "materialize_prelude", side_effect=fake_materialize):
            rewritten, used = rocq_cache.use_cached_prelude(sample, out)
        ensure(used and len(fake_calls) == 1 and (out / "HoldFastPrelude.vo").is_file(),
               "use_cached_prelude did not materialize HoldFastPrelude.vo")
        expected_prefix = (
            "(* header *)\n"
            "Require Import HoldFastPrelude.\n"
            + rocq_cache._PRELUDE_REQUIRES
            + "Module Sample.\n\n"
            + rocq_cache._PRELUDE_IMPORTS
        )
        ensure(rewritten.startswith(expected_prefix)
               and "Definition x := 1." in rewritten
               and rocq_cache.elaborate_types._PRELUDE not in rewritten,
               "use_cached_prelude produced unexpected rewritten source")


def _replay_graded_support_units() -> None:
    batch = rocq_cache.BatchChecker()
    _replay("graded_pure", "GradedPure", _PURE_PROOFS, batch=batch)
    _replay("graded_domains", "GradedDomains", _DOMAIN_PROOFS, ("graded_pure",), batch=batch)
    batch.verify_all()


def cases() -> list[Case]:
    return [Case("support cache reuses verified .vo artifacts and repairs corruption", _support_cache_controls),
            Case("rocqchk batch checker deduplicates units and cleans up", _batch_checker_controls),
            Case("cached HoldFastPrelude rewrites elaborate output cleanly", _cached_prelude_controls),
            Case("pure dependent usage, ordered grade domains, and kernel check",
                 _replay_graded_support_units, lane="toolchain"),
            Case("source-bound exact grades and dependent partial application replay", _source_replay, lane="toolchain"),
            Case("source-bound natural bounds and exact type dependencies", _bounded_source_replay, lane="toolchain"),
            Case("graded type-valued identity and universe specialization replay", _type_identity_source_replay,
                 lane="toolchain"),
            Case("graded value application preserves dependent and callable argument types", _value_application,
                 lane="toolchain"),
            Case("graded let sequences the initializer and substitutes independent type demand", _graded_let,
                 lane="toolchain"),
            Case("default elaboration checks source grades before Gallina emission", _default_source_replay, lane="toolchain"),
            Case("explicit (s, r) type grades and Presence domain source replay", _type_grades_and_presence_replay,
                 lane="toolchain"),
            Case("custom domain, inductive families, grade polymorphism, local inference, and CLI replay",
                 _domains_and_grade_polymorphism, lane="toolchain"),
            Case("Q25cb zero-type-use substitution skipping agreement and multi-binder benchmark",
                 _q25cb_zero_type_use_skip_and_benchmark, lane="toolchain")]
