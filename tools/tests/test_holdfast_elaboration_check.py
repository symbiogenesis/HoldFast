# SPDX-License-Identifier: Apache-2.0
"""Failure retention and exact-subject controls for native HoldFast term replay."""

import ast
import json
import subprocess
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from toolchain import (
    HoldFastError,
)
from toolchain import (
    elaboration_check as replay,
)


def _qualification_input_closure() -> None:
    root = Path(__file__).resolve().parents[2]
    bound = replay._inputs(root)
    pending = ["elaboration_check"]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        relative = f"tools/toolchain/{'__init__' if module == 'toolchain' else module}.py"
        path = root / relative
        ensure(relative in bound, f"replay does not bind its imported checker input {relative}")
        ensure(bound[relative] == replay._sha256(path.read_bytes()),
               f"replay checker hash does not describe {relative}")
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            imports: list[str] = []
            if isinstance(node, ast.Import):
                imports = [name.name for name in node.names if name.name == "toolchain"
                           or name.name.startswith("toolchain.")]
            elif isinstance(node, ast.ImportFrom) and node.module is not None:
                if node.module == "toolchain":
                    imports = [f"toolchain.{name.name}" for name in node.names]
                elif node.module.startswith("toolchain."):
                    imports = [node.module]
            for name in imports:
                local = name.removeprefix("toolchain.")
                if local == "toolchain" or (root / f"tools/toolchain/{local}.py").is_file():
                    pending.append(local)
    ensure({"tools/pyproject.toml", "tools/uv.lock"} <= bound.keys(),
           "replay omitted its Python dependency/version owners")
    ensure("solver_ledger" in visited and "jsonutil" in visited,
           "input audit failed to reach the assumption and syntax-protocol checkers")


def _process_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        steps: list[dict[str, object]] = []
        log = directory / "command.log"
        done = subprocess.CompletedProcess(["rocq"], 1, b"partial", b"refused")
        with patch.object(replay.subprocess, "run", return_value=done):
            with raises(RuntimeError, msg="failed compiler counted as a kernel verdict") as raised:
                replay._run(["rocq"], directory, log, steps)
            ensure("exited 1" in str(raised.exception), "compiler failure lost its verdict")
        ensure(log.read_bytes() == b"partialrefused", "compiler failure transcript was lost")
        ensure(steps[0]["status"] == "failed", "compiler failure was not retained")
        with patch.object(replay.subprocess, "run", side_effect=subprocess.TimeoutExpired(
                "rocq", replay.TIMEOUT, output=b"before", stderr=b"timeout")):
            with raises(RuntimeError, msg="timeout counted as acceptance") as raised:
                replay._run(["rocq"], directory, log, steps)
            ensure("exceeded" in str(raised.exception), "timeout lost its bounded diagnostic")
        ensure(steps[-1]["status"] == "timeout", "timeout verdict was not journalled")
        ensure(log.read_bytes() == b"partialrefused", "a later process overwrote earlier evidence")
        ensure(Path(str(steps[-1]["log"])).read_bytes() == b"beforetimeout", "partial timeout output lost")
        with (
            patch.object(replay.subprocess, "run", side_effect=FileNotFoundError("rocq missing")),
            raises(FileNotFoundError, msg="missing compiler counted as acceptance"),
        ):
            replay._run(["rocq"], directory, directory / "missing.log", steps)
        ensure(steps[-1]["status"] == "unavailable", "unavailable tooling was not distinguished")


def _semantic_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        compiled = replay.holdfast_parser.Build(directory, directory / "parser", {})
        fixture = replay.Fixture("wrong-index", b"module M;", "type")
        with patch.object(replay.holdfast_parser, "parse_source", side_effect=HoldFastError(
                "syntax", 1, 1, "malformed fixture")):
            with raises(HoldFastError, msg="parse failure satisfied a semantic negative") as raised:
                replay._case(compiled, fixture, directory, 0, [])
            ensure(raised.exception.kind == "syntax", "parser failure changed category")
        with patch.object(replay.holdfast_parser, "parse_source", return_value={}), \
                patch.object(replay.holdfast_elaborate, "elaborate", side_effect=HoldFastError(
                    "type", 1, 5, "index mismatch")):
            row = replay._case(compiled, fixture, directory, 0, [])
        ensure(row["category"] == "type" and row["column"] == 5, "intended semantic refusal lost")
        for outcome in (HoldFastError("unsupported", 1, 1, "missing implementation"), None):
            proposed = SimpleNamespace(module="M", gallina="Definition value := 0.\n")
            with patch.object(replay.holdfast_parser, "parse_source", return_value={}), \
                    patch.object(replay.holdfast_elaborate, "elaborate", side_effect=outcome,
                                 return_value=proposed):
                with raises(ValueError, msg="unrelated refusal or acceptance satisfied a negative") as raised:
                    replay._case(compiled, fixture, directory, 0, [])
                ensure("expected type" in str(raised.exception), "wrong semantic rejection lost its cause")


def _refused_attempts() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        latest = directory / "qualification.json"
        latest.write_text('{"status":"passed","stale":true}', encoding="utf-8")
        with patch.object(replay, "_work_root", return_value=directory), \
                patch.object(replay, "_inputs", return_value={}), \
                patch.object(replay, "_toolchain", side_effect=ValueError("wrong locked prover")):
            with raises(ValueError, msg="unsupported prover qualified") as raised:
                replay.qualify(directory)
            ensure("wrong locked prover" in str(raised.exception), "qualification failure was swallowed")
        ensure(not latest.exists(), "stale passing receipt survived a new failed attempt")
        attempts = list(directory.glob("replay-*/attempt.json"))
        ensure(len(attempts) == 1, "failed attempt journal was not retained")
        row = json.loads(attempts[0].read_text(encoding="utf-8"))
        ensure(row["status"] == "failed" and not row["kernel_checked"], "failed replay acquired acceptance")
        ensure("wrong locked prover" in row["error"], "attempt omitted its refusal cause")


def _freshness_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        for name in (*replay.holdfast_parser.GENERATED, "holdfast-parser"):
            (directory / name).write_bytes(name.encode())
        outputs = {name: replay._sha256((directory / name).read_bytes())
                   for name in (*replay.holdfast_parser.GENERATED, "holdfast-parser")}
        compiled = replay.holdfast_parser.Build(directory, directory / "holdfast-parser",
                                            {"generated_sha256": outputs})
        ensure(replay._parser_outputs(compiled) == outputs, "unchanged parser output was refused")
        (directory / "parser.ml").write_bytes(b"changed parser")
        with raises(ValueError, msg="stale generated parser was accepted") as raised:
            replay._parser_outputs(compiled)
        ensure("changed" in str(raised.exception), "changed parser lost its refusal")
        artifact = directory / "Case000.vo"
        artifact.write_bytes(b"checked library")
        rows: list[dict[str, object]] = [{"vo": str(artifact), "vo_sha256": replay._sha256(artifact.read_bytes())}]
        ensure(str(artifact) in replay._observations(rows, []), "checked library not bound in receipt")
        artifact.write_bytes(b"replacement library")
        with raises(ValueError, msg="replaced checked library was accepted") as raised:
            replay._observations(rows, [])
        ensure("changed" in str(raised.exception), "changed library lost its refusal")


def _changed_input_completion() -> None:
    """A late edit refuses final publication even after successful kernel commands."""
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        compiled = replay.holdfast_parser.Build(directory, directory / "parser", {"toolchain": {}})
        example = replay.Fixture("example", b"module M;")
        row: dict[str, object] = {"category": "accepted", "library": "HoldFastElaboration.Case000"}
        with patch.object(replay, "_work_root", return_value=directory), \
                patch.object(replay, "_inputs", side_effect=[{"source": "old"}, {"source": "new"}]), \
                patch.object(replay, "_toolchain", return_value={}), \
                patch.object(replay, "_runtime", return_value={}), \
                patch.object(replay, "_parser_outputs", return_value={}), \
                patch.object(replay.holdfast_parser, "build", return_value=compiled), \
                patch.object(replay.holdfast_parser, "read_source", return_value=b"module M;"), \
                patch.object(replay, "fixtures", return_value=(example,)), \
                patch.object(replay, "_case", return_value=row), \
                patch.object(replay, "_run", return_value=""):
            with raises(ValueError, msg="changed source acquired a passing replay receipt") as raised:
                replay.qualify(directory)
            ensure("changed during" in str(raised.exception), "late edit lost its freshness diagnostic")
        ensure(not (directory / "qualification.json").exists(), "late edit published acceptance")
        attempts = list(directory.glob("replay-*/attempt.json"))
        ensure(len(attempts) == 1, "late edit attempt journal missing")
        ensure(json.loads(attempts[0].read_text(encoding="utf-8"))["status"] == "failed",
               "late edit retained passing attempt status")


def _native_output_placement() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        for kind in ("", *replay.env.CROSS_OS_FILESYSTEMS, *replay.env.VOLATILE_FILESYSTEMS):
            with patch.object(replay.env, "lane_of", return_value="fixture"), \
                    patch.object(replay.env, "lane_root", return_value=directory), \
                    patch.object(replay.env, "filesystem", return_value=kind):
                with raises(ValueError, msg=f"unsupported output filesystem accepted: {kind}") as raised:
                    replay._work_root(directory)
                ensure("persistent native" in str(raised.exception), "placement refusal lost its purpose")


def _pure_routing_and_observations() -> None:
    source = b"module A_B; public Nat F(Nat value) => value; public const Nat C = 2;"
    translated = replay.holdfast.translate(source)
    fixture = replay.Fixture("pure-routing", source, pure=True,
                             observations=(("f_F 2", "2"), ("c_C", "2")))
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        compiled = replay.holdfast_parser.Build(directory, directory / "parser", {})
        commands: list[list[str]] = []

        def command(arguments: list[str], _directory: Path, _log: Path,
                    _steps: list[dict[str, object]]) -> str:
            commands.append(arguments)
            if arguments[-1] == "Case000.v":
                (directory / "Case000.vo").write_bytes(b"kernel fixture")
                return ""
            return "Closed under the global context\n" * 4

        with patch.object(replay.holdfast_parser, "parse_source", return_value={}) as parse, \
                patch.object(replay.holdfast, "translate_ast", return_value=translated) as consume, \
                patch.object(replay.holdfast_elaborate, "elaborate", side_effect=AssertionError("wrong consumer")), \
                patch.object(replay, "_run", side_effect=command):
            row = replay._case(compiled, fixture, directory, 0, [])
        parse.assert_called_once_with(compiled, source, surface=False)
        ensure(consume.call_count == 2, "pure consumer was not checked deterministically")
        ensure(row["consumer"] == "pure" and row["category"] == "accepted"
               and row["assumption_exports"] == ["f_F", "c_C"],
               "pure exports were omitted from the assumption audit")
        generated = (directory / "Case000.v").read_text(encoding="utf-8")
        ensure(generated.startswith(translated.gallina)
               and "Corelib.Init.Logic.eq (HoldFastEncoded_415f42.f_F 2) (2) := Corelib.Init.Logic.eq_refl (2)." in generated
               and "Corelib.Init.Logic.eq (HoldFastEncoded_415f42.c_C) (2)" in generated,
               "independent observations were not compiled in the kernel-checked library")
        audit = (directory / "Case000Assumptions.v").read_text(encoding="utf-8")
        ensure("Print Assumptions Case000.HoldFastEncoded_415f42.f_F." in audit
               and "Print Assumptions Case000.HoldFastEncoded_415f42.c_C." in audit
               and "Print Assumptions Case000.holdfast_replay_check_0." in audit
               and "Print Assumptions Case000.holdfast_replay_check_1." in audit,
               "generated exports or observation proofs escaped the assumption audit")
        ensure(len(commands) == 2 and commands[0][-1] == "Case000.v",
               "observation results used an extra host evaluator")
        with patch.object(replay.holdfast_parser, "parse_source", return_value={}), \
                patch.object(replay.holdfast, "translate_ast", return_value=translated), \
                patch.object(replay, "_run", side_effect=RuntimeError("kernel rejected observation")):
            with raises(RuntimeError, msg="a rejected observation acquired acceptance") as raised:
                replay._case(compiled, fixture, directory, 1, [])
            ensure("kernel rejected" in str(raised.exception), "observation failure lost its cause")


def _pure_semantic_negatives_and_inventory() -> None:
    fixture = replay.Fixture("pure-negative", b"module M; public bool F() => !1;", "type", pure=True)
    with tempfile.TemporaryDirectory(prefix="holdfast-replay-") as temporary:
        directory = Path(temporary)
        compiled = replay.holdfast_parser.Build(directory, directory / "parser", {})
        with patch.object(replay.holdfast_parser, "parse_source", return_value={}), \
                patch.object(replay.holdfast, "translate_ast", side_effect=HoldFastError("type", 1, 35, "requires bool")), \
                patch.object(replay.holdfast_elaborate, "elaborate", side_effect=AssertionError("wrong consumer")):
            row = replay._case(compiled, fixture, directory, 0, [])
        ensure(row["category"] == "type" and row["consumer"] == "pure", "pure semantic refusal was lost")
        with patch.object(replay.holdfast_parser, "parse_source", side_effect=HoldFastError("syntax", 1, 1, "bad syntax")):
            with raises(HoldFastError, msg="a parsing refusal satisfied a pure semantic negative") as raised:
                replay._case(compiled, fixture, directory, 1, [])
            ensure(raised.exception.kind == "syntax", "parsing refusal changed kind")
    fixtures = replay.fixtures(b"module M;", b"module WordCount;")
    operators = next(case for case in fixtures if case.name == "pure-expression-operators")
    ensure(operators.pure and ("f_Difference 8 3", "5") in operators.observations
           and ("c_Saturated", "0") in operators.observations
           and ("f_Precedence", "true") in operators.observations
           and ("c_Static", "true") in operators.observations,
           "hosted fixtures lack runtime, static or precedence observations")
    ensure(any(case.name == "pure-skipped-runtime-dependency" and case.pure
               and case.expected == "unsupported" for case in fixtures),
           "hosted replay lost required-static checking of skipped operands")
    division = next(case for case in fixtures if case.name == "pure-division-remainder")
    ensure(division.pure and ("f_Quotient 17 0", "99") in division.observations
           and ("f_Remainder 17 0", "99") in division.observations
           and ("f_DivThenMul", "12") in division.observations
           and ("f_Specialized 23", "6") in division.observations
           and ("c_StaticRemainder", "2") in division.observations,
           "hosted division replay lacks guarded runtime, precedence or static observations")
    for case in fixtures:
        if not case.pure:
            continue
        try:
            replay.holdfast.translate(case.source)
        except HoldFastError as error:
            ensure(case.expected != "accepted" and error.kind == case.expected,
                   f"hosted pure fixture {case.name} reached {error.kind}, expected {case.expected}")
        else:
            ensure(case.expected == "accepted", f"hosted semantic negative {case.name} was accepted")


def cases() -> list[Case]:
    return [Case("holdfast-replay-qualification-input-closure", _qualification_input_closure),
            Case("holdfast-replay-process-controls", _process_controls),
            Case("holdfast-replay-semantic-negative-controls", _semantic_controls),
            Case("holdfast-replay-failed-attempt-retention", _refused_attempts),
            Case("holdfast-replay-artifact-freshness", _freshness_controls),
            Case("holdfast-replay-changed-input-completion", _changed_input_completion),
            Case("holdfast-replay-pure-routing-kernel-observations-and-exports", _pure_routing_and_observations),
            Case("holdfast-replay-pure-semantic-negatives-and-hosted-inventory", _pure_semantic_negatives_and_inventory),
            Case("holdfast-replay-native-output-placement", _native_output_placement)]
