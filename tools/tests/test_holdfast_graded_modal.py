# SPDX-License-Identifier: Apache-2.0
"""Replay exact and bounded modal and dependent-pair elimination in Rocq."""

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
    "instantiate_extent_typed",
    "check_sound",
    "checked_let_box_demands",
    "bounded_check_sound",
    "bounded_checked_let_box_demands",
    "checked_let_indexed_demands",
    "bounded_checked_let_indexed_demands",
    "promotion_scales_term_demand",
    "dependent_elimination_of_abstract_box",
    "dependent_elimination_of_promoted_box",
    "bounded_elimination_keeps_exact_type_use",
    "reject_exact_underuse",
    "reject_bounded_overuse",
    "zero_use_keeps_logical_motive",
    "reject_wrong_exact_box_grade",
    "reject_wrong_motive_specialization",
    "reject_bypassing_open",
    "reject_computing_with_zero_use_payload",
)
_SUPPORT = ("graded_pure.v", "graded_domains.v", "graded_modal.v", "graded_modal_source.v")


def _replay() -> None:
    launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
    compile_unit = [*launch, "rocq", "c", "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-modal-") as temporary:
        directory = Path(temporary)
        for name in _SUPPORT[:-1]:
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


def _source_command(path: Path, declaration: str, *options: str) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(["check-grades", str(path), declaration, "--modal", *options])
    return status, output.getvalue(), error.getvalue()


def _audit_certificate(directory: Path, kernel_hashes: dict[str, str], certificate: str,
                       theorem: str, stale_row: tuple[str, str]) -> None:
    compiler = [*proofenv.rocq_command(), "-q"]
    ensure(set(kernel_hashes) == set(_SUPPORT), "wrong Rocq support closure")
    for name in _SUPPORT:
        unit = TOOLS / "rocq" / name
        ensure(hashlib.sha256(unit.read_bytes()).hexdigest() == kernel_hashes[name],
               f"unbound Rocq support {name}")
        shutil.copyfile(unit, directory / name)
        subprocess.run([*compiler, name], cwd=directory, check=True, timeout=30)
    unit = directory / "ModalSourceProof.v"
    unit.write_text(certificate, encoding="utf-8")
    subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True, check=True, timeout=30)
    audit = directory / "ModalSourceAudit.v"
    audit.write_text("Require Import ModalSourceProof graded_modal_source.\n"
                     f"Print Assumptions GradedModalSource.{theorem}.\n"
                     "Print Assumptions source_rows_match.\n", encoding="utf-8")
    replay = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                            text=True, encoding="utf-8", check=True, timeout=30)
    solver_ledger.audit(replay.stdout, 2, "GradedModalSource", ())
    stale = certificate.replace(*stale_row)
    ensure(stale != certificate, "modal certificate control did not replace a type demand")
    unit.write_text(stale, encoding="utf-8")
    refused = subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True,
                             text=True, encoding="utf-8", check=False, timeout=30)
    ensure(refused.returncode != 0 and "Unable to unify" in refused.stderr, refused.stderr)


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

        _audit_certificate(directory, result["kernel_sha256"], result["gallina"],
                           "source_check_sound", ("[0; 0; 2]", "[0; 0; 1]"))


def _bounded_source_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-modal-bounded.hf"
    raw = source.read_bytes()
    options = ("--domain", "NatBound")
    status, output, error = _source_command(source, "OpenBounded", *options)
    ensure(status == 0, error)
    result = json.loads(output)
    ensure(result["domain"] == "NatBound" and result["dependencies"] == ["Box"]
           and result["source_sha256"] == hashlib.sha256(raw).hexdigest(),
           "bounded modal replay lost its domain, dependency or source bytes")
    [packed] = result["binders"]
    ensure(packed["name"] == "packed" and packed["computation"] == 2 and packed["type"] == 2,
           "bounded modal replay failed to separate computation allowance from type use")
    ensure(result["result_type_uses"] == [{"name": "packed", "uses": 2, "span": packed["span"]}],
           "bounded match lost the scrutinee's exact type-demand row")

    status, output, error = _source_command(source, "PromoteBounded", *options)
    ensure(status == 0, error)
    promoted = json.loads(output)
    [n] = promoted["binders"]
    ensure(n["name"] == "n" and n["computation"] == 6 and n["type"] == 12,
           "bounded promotion and the dependent motive did not scale their separate rows")

    with tempfile.TemporaryDirectory(prefix="holdfast-bounded-modal-controls-") as temporary:
        directory = Path(temporary)
        changed = directory / source.name
        for original, replacement, failure in (
            (b"Box(n) => (n + n,", b"Box(n) => (n + n + n + n,", ": grade: "),
            (b"Box<Nat, 3>(n).Value", b"Box<Nat, 2>(n).Value", ": grade: "),
            (b"packed @ NatBound(2)", b"packed @ NatBound(0)", ": grade: "),
            (b"values @ NatBound(2)", b"values @ NatBound(0)", ": grade: "),
            (b"grade q : NatBound", b"grade q : NatExact", ": unsupported: "),
        ):
            ensure(original in raw, f"bounded modal control is absent: {original!r}")
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, "OpenBounded", *options)
            ensure(status == 1 and not output and failure in error, error)

        changed.write_bytes(raw.replace(b"NatBound(2)", b"NatExact(1)").replace(b"NatBound", b"NatExact"))
        status, output, error = _source_command(changed, "OpenBounded", "--domain", "NatExact")
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)

        _audit_certificate(directory, result["kernel_sha256"], result["gallina"],
                           "bounded_source_check_sound", ("[0; 2; 2]", "[0; 2; 1]"))


def _dependent_pair_source_replay() -> None:
    source = TOOLS / "tests" / "fixtures" / "graded-dependent-pair.hf"
    raw = source.read_bytes()
    for declaration, domain in (("OpenIndexed", "NatExact"), ("OpenBounded", "NatBound")):
        status, output, error = _source_command(source, declaration, "--domain", domain)
        ensure(status == 0, error)
        result = json.loads(output)
        ensure(result["domain"] == domain and result["dependencies"] == ["Indexed"]
               and result["source_sha256"] == hashlib.sha256(raw).hexdigest(),
               "dependent pair replay lost its domain, record or source identity")
        [packed] = result["binders"]
        ensure(packed["name"] == "packed" and packed["computation"] == packed["type"] == 2,
               "incorrect pair demand after tensor elimination")
        ensure(result["result_type_uses"] == [{"name": "packed", "uses": 2, "span": packed["span"]}],
               "the motive's type demand did not reach the named pair")

    status, output, error = _source_command(source, "BuildAndOpen")
    ensure(status == 0, error)
    result = json.loads(output)
    n, payload = result["binders"]
    ensure(n["name"] == "n" and n["computation"] == 0 and n["type"] == 6
           and payload["name"] == "payload" and payload["computation"] == 0 and payload["type"] == 2,
           "record fields used in a type leaked into computation demand")
    ensure(payload["annotation_type_uses"] == [{"name": "n", "uses": 2, "span": n["span"]}]
           and result["result_type_uses"] == [{"name": "payload", "uses": 2, "span": payload["span"]},
                                             {"name": "n", "uses": 4, "span": n["span"]}],
           "dependent pair specialization lost a constructed field or annotation demand")

    with tempfile.TemporaryDirectory(prefix="holdfast-dependent-pair-controls-") as temporary:
        directory = Path(temporary)
        changed = directory / source.name
        for declaration, domain, original, replacement, failure in (
            ("OpenBounded", "NatBound", b"packed @ NatBound(2)", b"packed @ NatBound(1)", ": grade: "),
            ("BuildAndOpen", "NatExact", b"match (Indexed(n + n, payload))", b"match (Indexed(n + 1, payload))", ": grade: "),
            ("BuildAndOpen", "NatExact", b"(Indexed(length, values).Length)> same", b"length> same", ": grade: "),
            ("OpenIndexed", "NatExact", b"Vec<Nat, (Length)> Payload", b"Vec<Nat, (Payload + 1)> Payload", ": unsupported: "),
        ):
            ensure(raw.count(original) == 1, f"pair control does not identify one occurrence: {original!r}")
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, declaration, "--domain", domain)
            ensure(status == 1 and not output and failure in error, error)

        asymmetric = raw.replace(b"packed @ NatExact(2)", b"packed @ NatExact(3)").replace(
            b"=> (1, ((Indexed(length, payload)", b"=> (length, ((Indexed(length, payload)")
        ensure(asymmetric != raw, "missing asymmetric pair control")
        changed.write_bytes(asymmetric)
        status, output, error = _source_command(changed, "OpenIndexed")
        ensure(status == 1 and not output and ": grade: " in error, error)
        _audit_certificate(directory, result["kernel_sha256"], result["gallina"],
                           "source_check_sound", ("[0; 0; 6]", "[0; 0; 5]"))

    status, output, error = _source_command(source, "OpenStereo")
    ensure(status == 0, error)
    stereo = json.loads(output)
    n, samples = stereo["binders"]
    ensure(stereo["dependencies"] == ["StereoFrame"] and n["computation"] == samples["computation"] == 0
           and n["type"] == 4 and samples["type"] == 2,
           "indexed family replay lost the record identity or confused type and computation demand")
    length_row = {"name": "n", "uses": 2, "span": n["span"]}
    ensure(samples["annotation_type_uses"] == [length_row]
           and stereo["result_type_uses"] == [{"name": "samples", "uses": 2, "span": samples["span"]}, length_row],
           "indexed family replay lost a dependency in the telescope or specialized motive")

    with tempfile.TemporaryDirectory(prefix="holdfast-indexed-family-controls-") as temporary:
        directory = Path(temporary)
        changed = directory / source.name
        changed.write_bytes(raw.replace(b"NatExact(0)", b"NatBound(1)").replace(b"NatExact", b"NatBound"))
        status, output, error = _source_command(changed, "OpenStereo", "--domain", "NatBound")
        ensure(status == 0, error)
        bounded_n, bounded_samples = json.loads(output)["binders"]
        ensure(bounded_n["computation"] == bounded_samples["computation"] == 1
               and bounded_n["type"] == n["type"] and bounded_samples["type"] == samples["type"],
               "bounded indexed family replay changed exact type demand")

        for original, replacement in (
            (b"Vec<Nat, (n + n + 1)> samples", b"Vec<Nat, (n + n + 2)> samples"),
            (b"match (StereoFrame(n, samples))", b"match (StereoMirror(n, samples))"),
            (b"Vec<Nat, (frame.Ticks)>", b"Vec<Nat, (frame.Samples)>"),
        ):
            ensure(original in raw, f"indexed family control is absent: {original!r}")
            changed.write_bytes(raw.replace(original, replacement))
            status, output, error = _source_command(changed, "OpenStereo")
            ensure(status == 1 and not output and ": grade: " in error, error)
        _audit_certificate(directory, stereo["kernel_sha256"], stereo["gallina"],
                           "source_check_sound", ("[0; 0; 4]", "[0; 0; 3]"))


def cases() -> list[Case]:
    return [Case("natural box promotion and dependent elimination replay", _replay, lane="toolchain"),
            Case("graded box declaration, motive and telescope source replay", _source_replay, lane="toolchain"),
            Case("bounded box declaration and dependent motive source replay", _bounded_source_replay, lane="toolchain"),
            Case("graded dependent pair tensor and motive source replay", _dependent_pair_source_replay, lane="toolchain")]
