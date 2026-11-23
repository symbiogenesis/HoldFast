# SPDX-License-Identifier: Apache-2.0
"""Support-source authentication, bounded compatibility and qualification refusals."""

import hashlib
import io
import json
import subprocess
import tarfile
import tempfile
from pathlib import Path
from unittest.mock import patch

import toolchain as holdfast
from tests.harness import Case, ensure, raises
from toolchain import parser as holdfast_parser
from toolchain import parser_checked as checked


def _tar(files: dict[str, bytes]) -> bytes:
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w:gz") as bundle:
        root = tarfile.TarInfo("release")
        root.type = tarfile.DIRTYPE
        bundle.addfile(root)
        for name, contents in files.items():
            member = tarfile.TarInfo(f"release/{name}")
            member.size = len(contents)
            bundle.addfile(member, io.BytesIO(contents))
    return stream.getvalue()


def _files() -> dict[str, bytes]:
    files = {f"coq-menhirlib/src/{name}.v": b"fixture source\n" for name in checked.MODULES}
    files.update({"coq-menhirlib/src/_CoqProject": b"fixture project\n",
                  "LICENSE": b"generator terms\n", "coq-menhirlib/LICENSE": b"support terms\n"})
    return files


def _archive_controls() -> None:
    files = _files()
    licenses = {name: checked._sha256(files[name]) for name in checked.LICENSES}
    version = checked._sha256(files["coq-menhirlib/src/Version.v"])
    original = _tar(files)
    with patch.object(checked, "LICENSES", licenses), patch.object(checked, "VERSION_SHA256", version):
        with patch.object(checked, "ARCHIVE_SHA512", hashlib.sha512(original).hexdigest()):
            ensure(checked._release_sources(original) == files, "authenticated selected sources changed")
            with raises(ValueError, msg="corrupt archive consumed") as raised:
                checked._release_sources(original + b"corruption")
            ensure("digest" in str(raised.exception), "archive corruption lost its cause")
        for change in ("missing", "license", "version", "escape"):
            changed = dict(files)
            if change == "missing":
                changed.pop("coq-menhirlib/src/Main.v")
            elif change == "license":
                changed["coq-menhirlib/LICENSE"] += b"changed"
            elif change == "version":
                changed["coq-menhirlib/src/Version.v"] = b"Definition require_unreleased := tt.\n"
            else:
                changed["../escape"] = b"unsafe"
            archive = _tar(changed)
            with (
                patch.object(checked, "ARCHIVE_SHA512", hashlib.sha512(archive).hexdigest()),
                raises(ValueError, msg=f"unsupported {change} archive accepted"),
            ):
                checked._release_sources(archive)


def _proof_footprint() -> None:
    # Original authored fixtures: no upstream proof text is incorporated here.
    original = b"".join(f"Definition {name} : nat.\nrefine 0.\nProof.\nexact 0.\nDefined.\n".encode()
                         for name in checked.TARGETS)
    candidate = original.replace(b"refine 0.\nProof.\n", b"Proof.\nrefine 0.\n")
    reference = original.replace(b"Proof.\n", b"")
    with patch.object(checked, "INTERPRETER_SHA256", checked._sha256(original)), \
            patch.object(checked, "CANDIDATE_SHA256", checked._sha256(candidate)), \
            patch.object(checked, "REFERENCE_SHA256", checked._sha256(reference)):
        ensure(checked._proof_openings(original) == candidate, "repair changed more than proof openings")
        ensure(checked._proof_openings(original, reference=True) == reference, "diagnostic twin changed terms")
        for source in (original + b"changed", candidate):
            with raises(ValueError, msg="repair accepted different or already modified source") as raised:
                checked._proof_openings(source)
            ensure("unsupported" in str(raised.exception), "unsupported source repair lost its cause")
        with patch.object(checked, "CANDIDATE_SHA256", "0" * 64):
            with raises(ValueError, msg="unexpected repaired bytes accepted") as raised:
                checked._proof_openings(original)
            ensure("reviewed candidate" in str(raised.exception), "changed repair digest lost its cause")


def _validator_items_map_footprint() -> None:
    original = (
        b"Proof.\n"
        b"  intros -> Hval1 Hval2 Val st prod fut lookahead (pos & -> & Hlookahead).\n"
        b"  rewrite /forallb_items StateProdPosMap.fold_1 in Val.\n"
        b"  assert (match future_of_prod prod pos with\n"
        b"          | [] => b1 st prod pos (find_items_map (items_map ()) st prod pos)\n"
        b"          | s :: fut' => b2 st prod pos (find_items_map (items_map ()) st prod pos) s fut'\n"
        b"          end = true).\n"
        b"  - unfold find_items_map in *.\n"
        b"    assert (Hfind := @StateProdPosMap.find_2 _ (items_map ()) (st, prod, pos)).\n"
    )
    candidate = (
        b"Proof.\n"
        b"  intros Him Hval1 Hval2 Val st prod fut lookahead (pos & -> & Hlookahead).\n"
        b"  rewrite -Him in Hlookahead.\n"
        b"  rewrite /forallb_items StateProdPosMap.fold_1 in Val.\n"
        b"  assert (match future_of_prod prod pos with\n"
        b"          | [] => b1 st prod pos (find_items_map im st prod pos)\n"
        b"          | s :: fut' => b2 st prod pos (find_items_map im st prod pos) s fut'\n"
        b"          end = true).\n"
        b"  - unfold find_items_map in *.\n"
        b"    assert (Hfind := @StateProdPosMap.find_2 _ im (st, prod, pos)).\n"
    )
    with patch.object(checked, "VALIDATOR_COMPLETE_SHA256", checked._sha256(original)), \
            patch.object(checked, "VALIDATOR_COMPLETE_CANDIDATE_SHA256", checked._sha256(candidate)):
        ensure(checked._validator_items_map(original) == candidate, "items_map repair changed unexpected bytes")
        ensure(checked._validator_items_map(original, reference=True) == original, "reference items_map changed")
        for source in (original + b"changed", candidate):
            with raises(ValueError, msg="Validator_complete repair accepted unexpected source") as raised:
                checked._validator_items_map(source)
            ensure("unsupported" in str(raised.exception), "unsupported Validator_complete source lost its cause")
        with patch.object(checked, "VALIDATOR_COMPLETE_CANDIDATE_SHA256", "0" * 64):
            with raises(ValueError, msg="unexpected Validator_complete repaired bytes accepted") as raised:
                checked._validator_items_map(original)
            ensure("reviewed candidate" in str(raised.exception), "changed Validator_complete digest lost its cause")


def _pure_grammar_view_and_assumptions() -> None:
    root = Path(__file__).resolve().parents[2]
    mly_text = (root / "tools/toolchain/parser/parser.mly").read_text(encoding="utf-8")
    pure_mly, token_stub = checked._pure_grammar_view(mly_text)
    ensure(pure_mly == checked.HOLDFAST_PURE_GRAMMAR_MLY, "pure grammar view differed from checked specification")
    ensure("type token =" in token_stub and "let generic_call_prefix _ _ : unit = raise Error" in token_stub,
           "token stub omitted token definitions or prefix entry")
    for mutated in (
        mly_text.replace("MODULE module_name=name SEMICOLON", "MODULE module_name=name"),
        mly_text.replace("%token MODULE ", "%token "),
    ):
        with raises(ValueError, msg="drifted parser.mly pure grammar skeleton accepted"):
            checked._pure_grammar_view(mutated)
    closed = "Closed under the global context\n" * len(checked.THEOREMS)
    checked._check_closed_assumptions(closed, len(checked.THEOREMS))
    for unclosed in ("Axioms:\nAut.Gram.token : Type\n", "Closed under the global context\n"):
        with raises(ValueError, msg="unclosed concrete theorem assumptions accepted") as raised:
            checked._check_closed_assumptions(unclosed, len(checked.THEOREMS))
        ensure("unclosed assumptions" in str(raised.exception), "unclosed assumption refusal lost its cause")


def _process_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-support-") as temporary:
        directory = Path(temporary)
        for code, output, expected in ((1, b"require_unreleased was not found", True),
                                       (0, b"require_unreleased", False),
                                       (1, b"unrelated error", False),
                                       (127, b"require_unreleased", False)):
            process = subprocess.CompletedProcess(["rocq"], code, b"", output)
            steps: list[dict[str, object]] = []
            with patch.object(checked.subprocess, "run", return_value=process) as run:
                try:
                    checked._run(["rocq"], directory, directory / "control.stdout", steps,
                                 refusal="require_unreleased")
                except RuntimeError:
                    ensure(not expected, "genuine mismatched-version refusal failed")
                else:
                    ensure(expected, "successful or unrelated failure counted as negative control")
            ensure(run.call_args.kwargs["timeout"] == checked.TIMEOUT, "command lost its duration bound")
            ensure(steps[0]["exit"] == code, "command verdict not journalled")
        with patch.object(checked.subprocess, "run", side_effect=subprocess.TimeoutExpired(
                "rocq", checked.TIMEOUT, output=b"partial", stderr=b"diagnostic")):
            steps = []
            with raises(RuntimeError, msg="timed-out support command passed") as raised:
                checked._run(["rocq"], directory, directory / "timeout.stdout", steps)
            ensure("exceeded" in str(raised.exception), "timeout lacks a diagnostic")
            ensure(steps[0]["status"] == "timeout", "timed-out attempt lost its verdict")
            ensure((directory / "timeout.stdout").read_bytes() == b"partialdiagnostic", "partial failure log lost")


def _refused_qualification() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-support-") as temporary:
        directory = Path(temporary)
        latest = directory / "qualification.json"
        latest.write_text('{"status":"passed","old":true}', encoding="utf-8")
        with patch.object(checked, "_work_root", return_value=directory), \
                patch.object(checked, "_inputs", return_value={}), \
                patch.object(checked, "_toolchain", side_effect=ValueError("different locked prover")):
            with raises(ValueError, msg="unsupported toolchain acquired a passing receipt") as raised:
                checked.qualify(directory)
            ensure("different locked prover" in str(raised.exception), "qualification failure swallowed")
        ensure(not latest.exists(), "failed qualification preserved old success")
        attempts = list(directory.glob("support-*/attempt.json"))
        ensure(len(attempts) == 1 and '"status": "failed"' in attempts[0].read_text(encoding="utf-8"),
               "failed qualification lost its retained attempt")


def _toolchain_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-support-") as temporary:
        directory = Path(temporary)
        locks = directory / "tools/opam"
        locks.mkdir(parents=True)
        sail = locks / "sail.lock"
        sail.write_text(f'"menhir.{checked.RELEASE}"\n', encoding="utf-8")
        (locks / "rocq.lock").write_text(f'"rocq-core.{checked.proofenv.ROCQ_VERSION}"\n', encoding="utf-8")
        for name in ("rocq", "rocqchk", "ocamlc", "ocamllex", "menhir"):
            (directory / name).write_bytes(b"tool identity")
        expected = [
            f"The Rocq Prover, version {checked.proofenv.ROCQ_VERSION}",
            checked.proofenv.OCAML_VERSION,
            str(directory),
            f"menhir, version {checked.RELEASE}",
            str(directory),
        ]
        with patch.object(checked, "_run", side_effect=expected):
            identity = checked._toolchain(directory, directory, [])
        digests = identity["binary_sha256"]
        ensure(isinstance(digests, dict) and len(digests) == 5, "support tools lost executable identities")
        for index in (0, 1, 2, 3, 4):
            changed = [*expected]
            changed[index] = "different identity"
            with (
                patch.object(checked, "_run", side_effect=changed),
                raises(ValueError, msg="unsupported tool identity accepted"),
            ):
                checked._toolchain(directory, directory, [])
        sail.write_text('"menhir.different"\n', encoding="utf-8")
        with patch.object(checked, "_run") as run:
            with raises(ValueError, msg="support source disagreed with locked generator") as raised:
                checked._toolchain(directory, directory, [])
            ensure("Sail snapshot" in str(raised.exception), "different generator source lost its cause")
            run.assert_not_called()


def _changed_observations() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-support-observations-") as temporary:
        root = Path(temporary)
        candidate, reference = root / "candidate", root / "reference"
        candidate.mkdir()
        reference.mkdir()
        guard = f"Definition guard := Version.require_{checked.RELEASE}.\n"
        files = {candidate / "Frozen.v": checked.FROZEN_QUERY, reference / "Frozen.v": checked.FROZEN_QUERY,
                 candidate / "Assumptions.v": checked.ASSUMPTIONS_QUERY,
                 candidate / "VersionAccepted.v": guard,
                 candidate / "VersionRefused.v": guard.replace(f"require_{checked.RELEASE}", "require_unreleased"),
                 root / "run.stdout": "Closed under the global context\n", root / "run.stderr": ""}
        steps: list[dict[str, object]] = [{"stdout": str(root / "run.stdout"), "stderr": str(root / "run.stderr"),
                                         "stdout_sha256": checked._sha256(files[root / "run.stdout"].encode()),
                                         "stderr_sha256": checked._sha256(b"")}]
        for changed in (None, *files):
            for path, text in files.items():
                path.write_text(text, encoding="utf-8", newline="")
            if changed is not None:
                changed.write_bytes(b"substituted observation")
            try:
                checked._observations(candidate, reference, guard, steps)
            except ValueError as error:
                ensure(changed is not None and "changed" in str(error), "unexpected observation refusal")
            else:
                ensure(changed is None, "changed proof probe or transcript acquired qualification")


def _host_replacement_and_retirement() -> None:
    ensure(not hasattr(holdfast, "_Parser"), "legacy Python recursive-descent parser is still present")
    source = b"module M; public const Nat Base = 4; public Nat F(Nat x) => x + Base;"
    envelope = checked.parse_checked(source)
    ensure(envelope.get("schema") == 1 and envelope.get("source_sha256") == checked._sha256(source),
           "checked host parser returned an invalid envelope")
    module = holdfast.parse_module(source)
    ensure(module.name.text == "M" and len(module.declarations) == 2,
           "checked host parser decoded unexpected declarations")
    ensure(holdfast.translate_ast(source, envelope) == holdfast.translate(source),
           "translate and translate_ast diverged under the checked parser")
    root = Path(__file__).resolve().parents[2]
    with tempfile.TemporaryDirectory(prefix="holdfast-checked-runtime-") as temporary:
        runtime_dir = Path(temporary)
        exe = runtime_dir / "holdfast-checked-parser"
        exe.write_bytes(b"original binary")
        receipt: dict[str, object] = {
            "schema": 1,
            "inputs": checked._runtime_inputs(root),
            "generated_sha256": {"holdfast-parser": checked._sha256(b"different binary")},
        }
        (runtime_dir / "receipt.json").write_text(json.dumps(receipt), encoding="utf-8")
        with patch.object(checked, "_runtime_root", return_value=runtime_dir):
            with raises(ValueError, msg="tampered runtime binary was accepted") as raised:
                checked.ensure_checked_build(root)
            ensure("changed after its build" in str(raised.exception), "tampered runtime binary lost its cause")
        tampered = holdfast_parser.Build(runtime_dir, exe, receipt)
        with raises(ValueError, msg="tampered explicit build was accepted") as raised:
            checked.parse_checked(source, compiled=tampered)
        ensure("changed after its build" in str(raised.exception), "tampered explicit build lost its cause")


def _runtime_variants() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-variants-") as temporary:
        base = Path(temporary)
        cache = base / "runtime"
        cache.mkdir()
        grammar_a, grammar_b = base / "a", base / "b"
        for grammar in (grammar_a, grammar_b):
            grammar.mkdir()
            for name in ("holdfast-checked-parser", "holdfast_checked_parser.ml", "holdfast_checked_parser.mli", "HoldFastPureGrammar.v"):
                (grammar / name).write_bytes(f"{grammar.name}:{name}".encode())
        with (patch.object(checked, "_runtime_root", return_value=cache),
              patch.object(checked, "_runtime_inputs", side_effect=lambda path: {"grammar": path.name})):
            a = checked._install_runtime_build(grammar_a, grammar_a)
            b = checked._install_runtime_build(grammar_b, grammar_b)
            ensure(a.executable != b.executable and a.executable.read_bytes() != b.executable.read_bytes(),
                   "different grammars shared a mutable runtime executable")
            # An existing grammar may be used while another process owns the staging lock.
            with holdfast_parser._file_lock(cache / "runtime.lock", timeout=1):
                for grammar, origin in ((grammar_a, a), (grammar_b, b), (grammar_a, a)):
                    current = checked.ensure_checked_build(grammar)
                    ensure(current.executable == origin.executable and current.receipt == origin.receipt,
                           "alternating checkouts replaced or rebuilt a verified runtime")
            (b.directory / "receipt.json").write_text(json.dumps(a.receipt), encoding="utf-8")
            with raises(ValueError, msg="one grammar accepted another grammar's runtime receipt") as raised:
                checked.ensure_checked_build(grammar_b)
            ensure("different inputs" in str(raised.exception), "receipt substitution lost its source identity diagnostic")
            a.executable.write_bytes(b"changed")
            with raises(ValueError, msg="changed executable passed receipt verification") as raised:
                checked.ensure_checked_build(grammar_a)
            ensure("changed after its build" in str(raised.exception), "damaged cache entry lost its integrity diagnostic")


def cases() -> list[Case]:
    return [Case("independent-checked-runtime-variants", _runtime_variants),
            Case("immutable-source-and-version-controls", _archive_controls),
            Case("proof-opening-byte-footprint", _proof_footprint),
            Case("validator-items-map-byte-footprint", _validator_items_map_footprint),
            Case("pure-grammar-view-and-closed-assumptions", _pure_grammar_view_and_assumptions),
            Case("bounded-command-and-negative-verdict-controls", _process_controls),
            Case("locked-generator-and-prover-controls", _toolchain_controls),
            Case("changed-probes-and-transcripts-refuse", _changed_observations),
            Case("failed-qualification-discards-stale-success", _refused_qualification),
            Case("host-replacement-and-python-retirement", _host_replacement_and_retirement)]
