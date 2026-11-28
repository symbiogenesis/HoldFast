# SPDX-License-Identifier: Apache-2.0
"""Native parser protocol, bounded execution and exact toolchain controls."""

import hashlib
import json
import subprocess
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import MAX_SOURCE_BYTES, HoldFastError, parser
from toolchain.cli import holdfast_parser as cli


def _build(directory: Path) -> parser.Build:
    executable = directory / "holdfast-parser"
    executable.write_bytes(b"test executable identity")
    return parser.Build(directory, executable,
                        {"generated_sha256": {"holdfast-parser": hashlib.sha256(executable.read_bytes()).hexdigest()}})


def _response(value: object, code: int = 0, stderr: bytes = b"") -> subprocess.CompletedProcess[bytes]:
    return subprocess.CompletedProcess(["holdfast-parser"], code, json.dumps(value).encode(), stderr)


def _expect_failure(compiled: parser.Build, response: subprocess.CompletedProcess[bytes],
                    message: str) -> None:
    with patch.object(parser.subprocess, "run", return_value=response):
        with raises((TypeError, ValueError, RuntimeError), msg="invalid native response accepted") as raised:
            parser.parse_source(compiled, b"module M;")
        error = raised.exception
        ensure(message in str(error), f"missing refusal detail: {error}")


def _protocol() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        compiled = _build(Path(temporary))
        ast = {"kind": "file", "span": [0, 9], "name": {"text": "M", "span": [7, 8]}, "declarations": []}
        source = b"module M;\r\n// exact bytes"
        with patch.object(parser.subprocess, "run", return_value=_response({"schema": 1, "ast": ast})) as process:
            result = parser.parse_source(compiled, source)
        ensure(result["ast"] == ast, "native syntax tree changed in orchestration")
        ensure(result["source_sha256"] == hashlib.sha256(source).hexdigest(), "source digest normalized bytes")
        ensure(process.call_args.kwargs["input"] == source, "parser received changed source")
        ensure(process.call_args.kwargs["timeout"] == parser.PARSE_TIMEOUT, "parser has no duration bound")
        for value, message in (
                ({"schema": True, "ast": ast}, "schema"),
                ({"schema": 2, "ast": ast}, "schema"),
                ({"schema": 1, "ast": {"kind": "file", "span": [0, 100]}}, "outside"),
                ({"schema": 1, "ast": {"kind": "file", "span": [False, 9]}}, "span"),
                ({"schema": 1, "ast": None}, "tree")):
            _expect_failure(compiled, _response(value), message)
        _expect_failure(compiled, _response({"schema": 1, "ast": ast}, stderr=b"warning"), "standard error")
        _expect_failure(compiled, _response({}, 7), "exited 7")
        _expect_failure(compiled, subprocess.CompletedProcess([], 0, b"{invalid", b""), "malformed JSON")
        refusal = {"kind": "syntax", "line": 3, "column": 10, "message": "expected expression"}
        with patch.object(parser.subprocess, "run", return_value=_response(refusal, 1)):
            with raises(HoldFastError, msg="native refusal accepted") as raised:
                parser.parse_source(compiled, source)
            error = raised.exception
            ensure((error.kind, error.line, error.column) == ("syntax", 3, 10), "native diagnostic lost")
        _expect_failure(compiled, _response({**refusal, "line": True}, 1), "invalid refusal")
        compiled.executable.write_bytes(b"changed")
        with patch.object(parser.subprocess, "run") as process:
            with raises(ValueError, msg="changed executable consumed") as raised:
                parser.parse_source(compiled, source)
            ensure("changed after" in str(raised.exception), "stale executable refusal missing")
            process.assert_not_called()


def _bounds() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        directory = Path(temporary)
        compiled = _build(directory)
        source = directory / "source.hf"
        source.write_bytes(b" " * (MAX_SOURCE_BYTES + 1))
        for operation in (lambda: parser.read_source(source),
                          lambda: parser.parse_source(compiled, source.read_bytes())):
            with patch.object(parser.subprocess, "run") as process:
                with raises(HoldFastError, msg="oversized source accepted") as raised:
                    operation()
                ensure(raised.exception.kind == "limit", "oversized source has wrong diagnostic")
                process.assert_not_called()
        with patch.object(parser.subprocess, "run", side_effect=subprocess.TimeoutExpired("parser", 15)):
            with raises(HoldFastError, msg="timed-out parse accepted") as raised:
                parser.parse_source(compiled, b"module M;")
            ensure(raised.exception.kind == "limit", "timeout has wrong diagnostic")
        with patch.object(parser.subprocess, "run", side_effect=subprocess.TimeoutExpired("tool", 120)):
            with raises(RuntimeError, msg="timed-out build accepted") as raised:
                parser._run(["tool"], directory)
            ensure("exceeded" in str(raised.exception), "build timeout has no useful refusal")


def _strict_response_json() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        compiled = _build(Path(temporary))
        ast = {"kind": "file", "span": [0, 9], "name": {"text": "M", "span": [7, 8]},
               "declarations": []}
        valid = json.dumps({"schema": 1, "ast": ast}).encode()
        ambiguous = (
            b'{"schema":2,"schema":1,"ast":' + json.dumps(ast).encode() + b"}",
            b'{"schema":2,"schem\\u0061":1,"ast":' + json.dumps(ast).encode() + b"}",
            valid.replace(b'"declarations": []', b'"declarations": [1], "declarations": []'),
            valid.replace(b'"declarations": []', b'"declarations": [NaN]'),
            valid.replace(b'"declarations": []', b'"declarations": [Infinity]'),
            valid.replace(b'"declarations": []', b'"declarations": [1e400]'),
            valid.decode().encode("utf-16"),
            b'{"schema":1,"ast":"\xff"}',
        )
        for raw in ambiguous:
            _expect_failure(compiled, subprocess.CompletedProcess([], 0, raw, b""), "malformed JSON")
        for depth in (parser.MAX_RESPONSE_DEPTH + 1, 10_000):
            raw = b'{"schema":1,"ast":' + b"[" * depth + b"0" + b"]" * depth + b"}"
            with patch.object(parser.json, "loads", side_effect=AssertionError("unbounded JSON decoding")):
                _expect_failure(compiled, subprocess.CompletedProcess([], 0, raw, b""), "nesting bound")
        # Brackets, escaped quotes and escaped backslashes inside a JSON string
        # consume no container budget, regardless of their byte count.
        spelling = '[{\\"' * (parser.MAX_RESPONSE_DEPTH + 1)
        escaped = {**ast, "description": spelling}
        with patch.object(parser.subprocess, "run", return_value=_response({"schema": 1, "ast": escaped})):
            actual = parser.parse_source(compiled, b"module M;")
        ensure(actual["ast"] == escaped, "quoted delimiters changed syntax or exhausted JSON depth")
        for response in ({"schema": 1, "ast": ast, "ignored": True},
                         {"kind": "syntax", "line": 1, "column": 1, "message": "bad", "ast": ast},
                         {"kind": [], "line": 1, "column": 1, "message": "bad"},
                         {"kind": "syntax", "line": 1, "column": 1, "message": "\ud800"}):
            _expect_failure(compiled, _response(response, 1 if "kind" in response else 0),
                            "invalid refusal" if "kind" in response else "schema")


def _located_tree_bounds() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        compiled = _build(Path(temporary))
        source = b"module M; // caf\xc3\xa9"
        for child, message in (({"kind": "child", "span": [7, 8]}, None),
                               ({"kind": "child", "span": [10, 11]}, "parent"),
                               ({"kind": "child", "span": [16, 17]}, "UTF-8"),
                               ({"kind": "child", "span": [7, 8], "value": "\ud800"}, "Unicode"),
                               ({"kind": "child", "span": [7, 8], "\ud800": "value"}, "Unicode")):
            # The UTF-8 case needs its parent to cover the comment containing é.
            end = len(source) if message == "UTF-8" else 9
            ast = {"kind": "file", "span": [0, end], "declarations": [child]}
            response = _response({"schema": 1, "ast": ast})
            if message:
                with patch.object(parser.subprocess, "run", return_value=response):
                    with raises(ValueError, msg=f"native tree accepted invalid {message} boundary") as raised:
                        parser.parse_source(compiled, source)
                    error = raised.exception
                    ensure(message in str(error), f"wrong located-tree refusal: {error}")
            else:
                with patch.object(parser.subprocess, "run", return_value=response):
                    ensure(parser.parse_source(compiled, source)["ast"] == ast,
                           "valid nested source span changed")
        for depth in (parser.MAX_SYNTAX_DEPTH, parser.MAX_SYNTAX_DEPTH + 1):
            ast = {"kind": "leaf", "span": [0, 9]}
            for _ in range(depth - 1):
                ast = {"kind": "file", "span": [0, 9], "child": ast}
            response = _response({"schema": 1, "ast": ast})
            with patch.object(parser.subprocess, "run", return_value=response):
                try:
                    parser.parse_source(compiled, b"module M;")
                except ValueError as error:
                    ensure(depth > parser.MAX_SYNTAX_DEPTH and "syntax depth" in str(error),
                           "wrong syntax-depth boundary")
                else:
                    ensure(depth == parser.MAX_SYNTAX_DEPTH, "over-budget native syntax accepted")
        ast = {"kind": "file", "span": [0, 1]}
        with patch.object(parser.subprocess, "run", return_value=_response({"schema": 1, "ast": ast})):
            with raises(ValueError,
                        msg="successful native reply concealed invalid source encoding") as raised:
                parser.parse_source(compiled, b"\xff")
            ensure("UTF-8" in str(raised.exception), "invalid source encoding has no protocol refusal")


def _versions() -> None:
    root = TOOLS.parent
    locked = parser._locked_versions(root)
    expected = [f"menhir, version {locked['menhir']}", locked["ocaml-base-compiler"],
                f"The OCaml lexer generator, version {locked['ocaml-base-compiler']}", str(root)]
    with patch.object(parser, "_run", side_effect=expected), patch.object(parser, "_digest", return_value="a" * 64):
        result = parser._toolchain(root)
    ensure(result["ocamlc"] == locked["ocaml-base-compiler"], "accepted compiler differs from lock")
    for index in range(3):
        changed = [*expected]
        changed[index] = "different version"
        with patch.object(parser, "_run", side_effect=changed):
            with raises(ValueError, msg="different parser toolchain accepted") as raised:
                parser._toolchain(root)
            ensure("identity differs" in str(raised.exception), "version refusal missing")


def _failed_build() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        root = Path(temporary)
        for name in parser.INPUT_PATHS:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("authored input\n", encoding="utf-8")
        output = root / "native-build"
        output.mkdir()
        with patch.object(parser, "_run", side_effect=RuntimeError("generator refused grammar")):
            with raises(RuntimeError, msg="failed generator acquired a build") as raised:
                parser._compile(root, output, {})
            ensure("refused grammar" in str(raised.exception), "generator failure hidden")
        ensure(not (output / "receipt.json").exists(), "failed build left a passing receipt")


def _cli() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        source = Path(temporary) / "source.hf"
        source.write_bytes(b"module M;")
        with redirect_stdout(out := StringIO()), redirect_stderr(err := StringIO()), \
                patch.object(cli.holdfast_parser, "cached_build", side_effect=RuntimeError("no locked toolchain")):
            code = cli.main(["parse", str(source)])
        ensure(code == 1 and not out.getvalue() and "no locked toolchain" in err.getvalue(),
               "failed build emitted an AST or lost its cause")


def _qualification_freshness() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        root = Path(temporary)
        output = root / "build"
        output.mkdir()
        example = root / "examples/pure.hf"
        example.parent.mkdir(parents=True)
        source = b"module M; public Nat F() { return 1; }\r\n"
        inputs, toolchain = {"source": "original"}, {"compiler": "original"}
        surface_fixture = root / parser.SURFACE_FIXTURE
        surface_fixture.parent.mkdir(parents=True)
        constant_example = example.with_name("constants.hf")
        expression_example = example.with_name("expressions.hf")
        constant_source = source + b"// const"
        expression_source = source + b"// expressions"
        for change in ("source", "toolchain", "generated", "executable", "example", "surface", "constant", "expression", "none"):
            example.write_bytes(source)
            surface_fixture.write_bytes(source)
            constant_example.write_bytes(constant_source)
            expression_example.write_bytes(expression_source)
            for name in (*parser.GENERATED, "holdfast-parser"):
                (output / name).write_bytes(b"original")
            hashes = {name: hashlib.sha256(b"original").hexdigest()
                      for name in (*parser.GENERATED, "holdfast-parser")}
            compiled = parser.Build(output, output / "holdfast-parser",
                                    {"inputs": inputs, "toolchain": toolchain,
                                     "generated_sha256": hashes})
            latest = root / "qualification.json"
            latest.write_text('{"status":"passed","old":true}', encoding="utf-8")

            def parse_example(_compiled: parser.Build, _source: bytes, *, surface: bool = False,
                              mode: str = change) -> dict[str, parser.Json]:
                if mode in {"generated", "executable"}:
                    (output / ("parser.ml" if mode == "generated" else "holdfast-parser")).write_bytes(b"changed")
                elif mode == "example":
                    example.write_bytes(source + b"// changed")
                elif mode == "surface" and surface:
                    surface_fixture.write_bytes(source + b"// changed")
                elif mode == "constant" and _source == constant_source:
                    constant_example.write_bytes(constant_source + b"// changed")
                elif mode == "expression" and _source == expression_source:
                    expression_example.write_bytes(expression_source + b"// changed")
                return {"schema": 1}

            with patch.object(parser, "_work_root", return_value=root), \
                    patch.object(parser, "build", return_value=compiled), \
                    patch.object(parser, "_fixtures", return_value=["independent"]), \
                    patch.object(parser, "_surface_layout_fixture", return_value="original-surface-tokens-and-comments"), \
                    patch.object(parser.holdfast_surface, "qualify", return_value=["surface-independent"]), \
                    patch.object(parser, "parse_source", side_effect=parse_example), \
                    patch.object(parser, "_inputs", return_value={"source": "changed"} if change == "source" else inputs), \
                    patch.object(parser, "_toolchain", return_value={"compiler": "changed"} if change == "toolchain" else toolchain):
                try:
                    report = parser.qualify(root)
                except ValueError as error:
                    ensure(change != "none" and "changed" in str(error), f"unexpected qualification refusal: {error}")
                    ensure(not latest.exists(), "refused qualification preserved a stale passing report")
                else:
                    ensure(change == "none", f"changed {change} accepted after qualification fixtures")
                    ensure(report["example"] == {"path": "examples/pure.hf",
                                                  "source_sha256": hashlib.sha256(source).hexdigest()},
                           "qualification omitted tested example byte identity")
                    ensure(report["expression_example"] == {"path": "examples/expressions.hf",
                                                             "source_sha256": hashlib.sha256(expression_source).hexdigest()},
                           "qualification omitted tested extended-expression example identity")
                    entries = report["syntax_entries"]
                    ensure(isinstance(entries, dict) and entries["surface"]["example"] == {
                        "path": parser.SURFACE_FIXTURE, "source_sha256": hashlib.sha256(source).hexdigest(),
                    }, "qualification omitted tested surface fixture identity")
                    ensure(json.loads(latest.read_text(encoding="utf-8")) == report,
                           "published qualification report differs from returned evidence")


def _constant_callable_oracle_required() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        compiled = _build(Path(temporary))
        with patch.object(parser, "_concise_fixture", return_value="concise"), \
                patch.object(parser, "_constant_callable_fixture", side_effect=ValueError("constant role changed")) as oracle:
            with raises(ValueError, msg="constant callable syntax oracle was bypassed") as raised:
                parser._fixtures(compiled)
            ensure(str(raised.exception) == "constant role changed", "constant oracle failure was replaced")
        oracle.assert_called_once_with(compiled)


def _extended_expression_oracle_required() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-parser-") as temporary:
        compiled = _build(Path(temporary))
        with patch.object(parser, "_concise_fixture", return_value="concise"), \
                patch.object(parser, "_constant_callable_fixture", return_value="constants"), \
                patch.object(parser, "_typed_local_fixture", return_value="locals"), \
                patch.object(parser, "_extended_expression_fixture",
                             side_effect=ValueError("operator span changed")) as oracle:
            with raises(ValueError, msg="extended expression syntax oracle was bypassed") as raised:
                parser._fixtures(compiled)
            ensure(str(raised.exception) == "operator span changed", "extended expression oracle failure was replaced")
        oracle.assert_called_once_with(compiled)


def _batch_worker_parity() -> None:
    root = TOOLS.parent
    samples = (
        (b"module M; public Nat F() => 1 + 2;", False, False),
        (b"module M; public definition Nat F(Nat x) => x + 1;", True, False),
        (b"module M; public definition Nat F(Nat x) => x + 1;", True, True),
    )
    with parser.cached_build(root) as compiled:
        for source, surface, layout in samples:
            batched = parser.parse_source(compiled, source, surface=surface, layout=layout)
            args = [str(compiled.executable)]
            if layout:
                args.append("--surface-layout")
            elif surface:
                args.append("--surface")
            done = subprocess.run(args, input=source, capture_output=True, timeout=parser.PARSE_TIMEOUT, check=False)
            oneshot = parser.decode_response(
                source, done.returncode, done.stdout, done.stderr, surface=surface or layout, layout=layout,
            )
            ensure(batched == oneshot, f"batch worker diverged from single-shot parser for mode ({surface}, {layout})")
        for bad, kind in (
            (b"module M; public Nat F() => ;", "syntax"),
            (b"// bad \xff\nmodule M;", "encoding"),
            ("module M; // \u202e bidi".encode(), "encoding"),
            ("module M; // \u200b zwsp".encode(), "encoding"),
            (b"module M; // \x00 nul", "encoding"),
        ):
            with raises(HoldFastError, msg=f"batch worker missed refusal {kind}") as raised:
                parser.parse_source(compiled, bad)
            ensure(raised.exception.kind == kind, f"batch worker returned wrong refusal kind: {raised.exception}")
        parser.reset_worker()
        after_reset = parser.parse_source(compiled, samples[0][0])
        ast_obj = after_reset["ast"]
        ensure(isinstance(ast_obj, dict) and ast_obj.get("kind") == "file",
               "batch worker did not recover cleanly after reset")
        parser.reset_worker()


def cases() -> list[Case]:
    return [Case("constant-callable-oracle-is-required", _constant_callable_oracle_required),
            Case("extended-expression-oracle-is-required", _extended_expression_oracle_required),
            Case("native-protocol-and-source-identity", _protocol),
            Case("bounded-read-and-process-controls", _bounds),
            Case("strict-unambiguous-bounded-native-json", _strict_response_json),
            Case("native-tree-depth-containment-and-utf8-spans", _located_tree_bounds),
            Case("snapshot-version-controls", _versions),
            Case("generator-failure-without-receipt", _failed_build),
            Case("qualification-rechecks-tested-inputs", _qualification_freshness),
            Case("cli-failure-without-output", _cli),
            Case("batch-worker-matches-single-shot-modes", _batch_worker_parity, lane="toolchain")]
