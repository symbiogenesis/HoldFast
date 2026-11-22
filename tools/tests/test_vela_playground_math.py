# SPDX-License-Identifier: Apache-2.0
"""Full-language compiler, native-parser identity and transport controls."""

import hashlib
import json
import re
import shutil
import subprocess
import sys
from functools import cache
from pathlib import Path
from typing import cast
from unittest.mock import patch

from tests.harness import Case, ensure
from tests.test_vela_playground import _http, _post, _running
from toolchain import StaticEvaluation, VelaError, authoring, parser, playground, translate
from toolchain import ast as syntax
from toolchain.authoring import Finding
from toolchain.cli import vela_playground as playground_cli
from toolchain.commands import COMMANDS
from toolchain.mathematical import Compilation
from toolchain.playground_worker import compile_request

_PURE = "module Simple; public Nat Value() => 42;"
_SOURCE = ("module Indexed;\n// supplementary comment: \U0001f680\n"
           "public definition Vec<Nat, 2> Pair() => VCons(7, VCons(8, VNil<Nat>()));\n"
           "public definition Nat Last() => At(Pair(), FSucc(FZero<0>()));\n")
_DIGEST = hashlib.sha256(_SOURCE.encode()).hexdigest()


def _result(value: str = "8", value_type: str = "Nat") -> dict[str, object]:
    return {"ok": True, "sourceHash": _DIGEST, "valueType": value_type, "value": value}


def _process(response: dict[str, object]) -> playground.subprocess.CompletedProcess[bytes]:
    return playground.subprocess.CompletedProcess([], 0, json.dumps(response).encode(), b"")


def _http_whole_language_request_shape() -> None:
    with _running() as server:
        for mode in ("pure", "mathematical", "borrow", "", 1, None):
            status, _, body = _http(server, "/api/compile", {"source": _SOURCE, "mode": mode})
            ensure(status == 400 and "error" in json.loads(body),
                   f"client-selected compiler mode {mode!r} reached compilation")


def _http_dispatch_and_strict_fields() -> None:
    with _running() as server:
        parser = server.mathematical_parser
        request = {"source": _SOURCE, "expression": "Last()", "valueType": "Nat"}
        with patch.object(playground.subprocess, "run", return_value=_process(_result())) as worker:
            ensure(_post(server, "/api/evaluate", request) == _result(),
                   "mathematical HTTP response changed its exact source or typed value")
        forwarded = json.loads(cast("bytes", worker.call_args.kwargs["input"]))
        ensure(forwarded == {**request, "action": "evaluate"},
               "HTTP dispatch changed authored input")
        invocation = cast("list[str]", worker.call_args.args[0])
        ensure(_SOURCE not in " ".join(invocation) and "Last()" not in " ".join(invocation),
               "authored mathematical source or expression became an executable argument")
        ensure(worker.call_args.kwargs["timeout"] == playground.WORKER_SECONDS,
               "mathematical compilation escaped the isolated worker timeout")
        compile_reply: dict[str, object] = {
            "ok": True, "sourceHash": _DIGEST, "module": "Indexed", "gallina": "Module Indexed.\nEnd Indexed.\n",
            "editorServices": False, "findings": []}
        with patch.object(playground.subprocess, "run", return_value=_process(compile_reply)):
            ensure(_post(server, "/api/compile", {"source": _SOURCE}) == compile_reply,
                   "mathematical compilation lost its Gallina result")
        invalid_requests: tuple[tuple[str, dict[str, object]], ...] = (
            ("/api/compile", {"source": _SOURCE, "parser": str(parser)}),
            ("/api/compile", {"source": _SOURCE, "executable": str(parser)}),
            ("/api/authoring", {"source": _SOURCE, "mode": "mathematical"}),
            ("/api/evaluate", {**request, "valueType": "Vec<Nat,2>"}),
            ("/api/evaluate", {**request, "expression": "x" * 4097}),
            ("/api/compile", {"source": _SOURCE, "mode": {"name": "mathematical"}}),
        )
        with patch.object(playground.subprocess, "run") as worker:
            for path, payload in invalid_requests:
                status, _, _ = _http(server, path, payload)
                ensure(status == 400, f"invalid mathematical request reached {path}")
            ensure(not worker.called, "malformed request launched a compiler worker")


def _worker_reply_binding() -> None:
    with _running() as server:
        request = {"source": _SOURCE, "expression": "Last()", "valueType": "Nat"}
        malformed: tuple[dict[str, object], ...] = (
            {**_result(), "sourceHash": hashlib.sha256(b"different source").hexdigest()},
            {**_result(), "mode": "mathematical"},
            _result("-1"),
            _result("true", "bool"),
            {**_result(), "value": 8},
            {"ok": False, "sourceHash": _DIGEST,
             "error": {"kind": "type", "message": "wrong length", "line": True, "column": 1}},
            {"ok": False, "sourceHash": _DIGEST,
             "error": {"kind": "invented", "message": "wrong length", "line": 1, "column": 1}},
        )
        for response in malformed:
            with patch.object(playground.subprocess, "run", return_value=_process(response)):
                refused = _post(server, "/api/evaluate", request)
            ensure(refused["ok"] is False and refused["sourceHash"] == _DIGEST
                   and cast("dict[str, object]", refused["error"])["kind"] == "internal"
                   and "value" not in refused and "gallina" not in refused,
                   "malformed mathematical worker reply escaped source/type/schema validation")
        semantic_error: dict[str, object] = {"kind": "type", "message": "expression: wrong vector length",
                                            "line": 1, "column": 1}
        semantic: dict[str, object] = {"ok": False, "sourceHash": _DIGEST, "error": semantic_error}
        for kind in ("type", "inference", "protocol"):
            semantic_error["kind"] = kind
            with patch.object(playground.subprocess, "run", return_value=_process(semantic)):
                ensure(_post(server, "/api/evaluate", request) == semantic,
                       "semantic mathematical refusal was replaced with a success or infrastructure error")
        with patch.object(playground.subprocess, "run",
                          side_effect=playground.subprocess.TimeoutExpired("worker", playground.WORKER_SECONDS)):
            refused = _post(server, "/api/evaluate", request)
        ensure(refused["ok"] is False and refused["sourceHash"] == _DIGEST
               and cast("dict[str, object]", refused["error"])["kind"] == "timeout",
               "mathematical worker timeout retained a successful or unbound result")
        with patch.object(playground.subprocess, "run", return_value=_process(_result())):
            ensure(_post(server, "/api/evaluate", request) == _result(),
                   "mathematical transport failed recovery after rejected worker replies")


def _changed_parser_refuses() -> None:
    with _running() as server:
        parser = server.mathematical_parser

        def replace_during_worker(*_args: object, **_kwargs: object) -> playground.subprocess.CompletedProcess[bytes]:
            parser.write_bytes(b"replaced parser with different executable bytes")
            return _process({"ok": True, "sourceHash": _DIGEST, "module": "Indexed", "gallina": "stale terms",
                             "editorServices": False, "findings": []})

        request = {"source": _SOURCE}
        with patch.object(playground.subprocess, "run", side_effect=replace_during_worker) as worker:
            refused = _post(server, "/api/compile", request)
        ensure(worker.call_count == 1 and refused["ok"] is False and "gallina" not in refused,
               "parser changed during compilation retained its earlier successful result")
        with patch.object(playground.subprocess, "run") as worker:
            status, _, body = _http(server, "/api/compile", request)
        response = cast("dict[str, object]", json.loads(body))
        ensure(status != 200 or response.get("ok") is False,
               "changed native parser identity retained mathematical compile authority")
        ensure(not worker.called, "changed native parser launched an isolated compiler worker")
        with patch.object(playground.subprocess, "run") as worker:
            pure = _post(server, "/api/compile", {"source": _PURE})
        ensure(pure["ok"] is False and pure["editorServices"] is False and not worker.called,
               "changed parser retained authority for ordinary functions")
        authoring = _post(server, "/api/authoring", {"source": _PURE})
        ensure(authoring["ok"] is True,
               "independent authoring unnecessarily depended on mathematical parser identity")


def _worker_mathematical_routing() -> None:
    parser = Path("/prepared/native/vela-parser")
    compile_input: dict[str, object] = {"source": _SOURCE, "action": "compile"}
    with patch("toolchain.mathematical.compile_source", return_value=Compilation("Indexed", "actual Gallina", ())) as compile_math:
        response = compile_request(compile_input, mathematical_parser=parser)
    ensure(response == {"ok": True, "sourceHash": _DIGEST,
                        "module": "Indexed", "gallina": "actual Gallina", "editorServices": False, "findings": []},
           "worker changed the mathematical elaborator's actual result")
    ensure(compile_math.call_args.args == (_SOURCE.encode(), parser),
           "worker did not forward the exact source bytes and server-owned parser")
    finding = Finding("VELA105", "generic type parameter 'element' should use PascalCase", 3, 36)
    with patch("toolchain.mathematical.compile_source",
               return_value=Compilation("Indexed", "actual Gallina", (finding,))):
        response = compile_request(compile_input, mathematical_parser=parser)
    ensure(response["findings"] == [{"code": "VELA105", "message": finding.message, "line": 3, "column": 36}],
           "worker lost the mathematical producer's original naming finding")
    evaluate_input: dict[str, object] = {"source": _SOURCE, "action": "evaluate",
                                       "expression": "Last()", "valueType": "Nat"}
    with patch("toolchain.mathematical.evaluate_source", return_value=StaticEvaluation("Nat", 8)) as evaluate_math:
        response = compile_request(evaluate_input, mathematical_parser=parser)
    ensure(response == _result(), "worker fabricated a mathematical console value")
    ensure(evaluate_math.call_args.args == (_SOURCE.encode(), "Last()", "Nat", parser),
           "worker changed the expression, result type or parser identity")
    with patch("toolchain.mathematical.evaluate_source", return_value=StaticEvaluation("bool", False)):
        response = compile_request({**evaluate_input, "valueType": "bool"}, mathematical_parser=parser)
    ensure(response == _result("false", "bool"), "false mathematical result was confused with no result")
    with patch("toolchain.mathematical.compile_source", side_effect=VelaError("type", 3, 12, "wrong length")):
        response = compile_request(compile_input, mathematical_parser=parser)
    ensure(response == {"ok": False, "sourceHash": _DIGEST, "editorServices": False,
                        "error": {"kind": "type", "message": "wrong length", "line": 3, "column": 12}},
           "worker lost original mathematical diagnostic positions or source identity")


def _full_language_in_ordinary_modules() -> None:
    prepared = Path("/prepared/native/vela-parser")
    digest = hashlib.sha256(_PURE.encode()).hexdigest()
    with patch("toolchain.mathematical.compile_source", return_value=Compilation("Simple", "actual terms", ())) as full:
        pure = compile_request({"source": _PURE, "action": "compile"}, mathematical_parser=prepared)
        ensure(pure == {"ok": True, "sourceHash": digest, "module": "Simple", "gallina": translate(_PURE.encode()).gallina,
                        "editorServices": True, "findings": []} and full.call_args.args == (_PURE.encode(), prepared),
               "ordinary functions bypassed the full elaborator or lost editor services")
    with patch("toolchain.mathematical.compile_source", side_effect=VelaError("type", 1, 20, "full source judgment")):
        refused = compile_request({"source": _PURE, "action": "compile"}, mathematical_parser=prepared)
    ensure(refused["ok"] is False and refused["sourceHash"] == digest and "gallina" not in refused
           and refused["error"] == {"kind": "type", "message": "full source judgment", "line": 1, "column": 20},
           "editor-service acceptance replaced the full language's refusal")
    expression = "At(VCons(Value(), VNil<Nat>()), FZero<0>())"
    request: dict[str, object] = {"source": _PURE, "action": "evaluate", "expression": expression, "valueType": "Nat"}
    with patch("toolchain.mathematical.evaluate_source", return_value=StaticEvaluation("Nat", 42)) as evaluate_full:
        evaluated = compile_request(request, mathematical_parser=prepared)
        ensure(evaluated == {"ok": True, "sourceHash": digest, "valueType": "Nat", "value": "42"}
               and evaluate_full.call_args.args == (_PURE.encode(), expression, "Nat", prepared),
               "the surrounding module restricted the language available in the console")


def _mathematical_naming_reply_validation() -> None:
    source = ("module Naming;\n// supplementary: \U0001f680\r\n"
              "public definition element Identity<element>(element value) => value;\n")
    digest = hashlib.sha256(source.encode()).hexdigest()
    finding: dict[str, object] = {
        "code": "VELA105", "message": "generic type parameter 'element' should use PascalCase",
        "line": 3, "column": 36}
    valid: dict[str, object] = {"ok": True, "sourceHash": digest, "module": "Naming",
                                "gallina": "actual checked-source terms", "editorServices": False, "findings": [finding]}
    request: dict[str, object] = {"source": source}
    malformed: tuple[dict[str, object], ...] = (
        {key: value for key, value in valid.items() if key != "findings"},
        {key: value for key, value in valid.items() if key != "editorServices"},
        {**valid, "editorServices": 0},
        {**valid, "editorServices": "false"},
        {**valid, "editorServices": True},
        {**valid, "findings": None},
        {**valid, "findings": "not a list"},
        {**valid, "findings": [{**finding, "code": "VELA100"}]},
        {**valid, "findings": [{**finding, "code": "VELA999"}]},
        {**valid, "findings": [{**finding, "line": True}]},
        {**valid, "findings": [{**finding, "line": 99}]},
        {**valid, "findings": [{**finding, "column": 999}]},
        {**valid, "findings": [{**finding, "column": 7}]},
        {**valid, "findings": [{**finding, "column": 37}]},
        {**valid, "findings": [{**finding, "message": ""}]},
        {**valid, "findings": [{**finding, "extra": "unrecognized"}]},
        {**valid, "findings": [finding, finding]},
        {**valid, "sourceHash": hashlib.sha256(b"old source").hexdigest()},
    )
    with _running() as server:
        with patch.object(playground.subprocess, "run", return_value=_process(valid)):
            ensure(_post(server, "/api/compile", request) == valid,
                   "valid naming warnings prevented mathematical compilation")
        for response in malformed:
            with patch.object(playground.subprocess, "run", return_value=_process(response)):
                refused = _post(server, "/api/compile", request)
            ensure(refused["ok"] is False and refused["sourceHash"] == digest
                   and cast("dict[str, object]", refused["error"])["kind"] == "internal"
                   and "gallina" not in refused and "findings" not in refused,
                   "invalid naming findings retained compilation output or a clean warning result")
        with patch.object(playground, "MAX_AUTHORING_FINDINGS", 0), \
                patch.object(playground.subprocess, "run", return_value=_process(valid)):
            refused = _post(server, "/api/compile", request)
        ensure(refused["ok"] is False and "gallina" not in refused,
               "mathematical naming findings escaped their configured count budget")
        underscored_source = source.replace("element", "T_value")
        underscored: dict[str, object] = {
            **valid, "sourceHash": hashlib.sha256(underscored_source.encode()).hexdigest(),
            "findings": [{**finding, "message": "generic type parameter 'T_value' should use PascalCase"}]}
        with patch.object(playground.subprocess, "run", return_value=_process(underscored)):
            ensure(_post(server, "/api/compile", {**request, "source": underscored_source}) == underscored,
                   "capital-initial name with underscores was confused with PascalCase")
        capital_source = source.replace("element", "T")
        capital: dict[str, object] = {
            **valid, "sourceHash": hashlib.sha256(capital_source.encode()).hexdigest(),
            "findings": [{**finding, "message": "generic type parameter 'T' should use PascalCase", "column": 30}]}
        with patch.object(playground.subprocess, "run", return_value=_process(capital)):
            refused = _post(server, "/api/compile", {**request, "source": capital_source})
        ensure(refused["ok"] is False and "findings" not in refused,
               "clean PascalCase type received a fabricated naming warning")
        two_source = source + "public definition item Again<item>(item value) => value;\n"
        later: dict[str, object] = {**finding, "line": 4, "column": 30,
                                    "message": "generic type parameter 'item' should use PascalCase"}
        reordered: dict[str, object] = {
            **valid, "sourceHash": hashlib.sha256(two_source.encode()).hexdigest(), "findings": [later, finding]}
        with patch.object(playground.subprocess, "run", return_value=_process(reordered)):
            refused = _post(server, "/api/compile", {**request, "source": two_source})
        ensure(refused["ok"] is False and "findings" not in refused,
               "out-of-order worker naming coordinates bypassed complete reply validation")
        with patch.object(playground.subprocess, "run", return_value=_process(valid)):
            ensure(_post(server, "/api/compile", request) == valid,
                   "mathematical naming transport failed recovery after malformed warnings")
        pattern_source = (
            "module Pattern;\n"
            "public definition Nat Check(bool flag) => match (flag) { None => 1, _ => 0 };\n"
        )
        pattern_digest = hashlib.sha256(pattern_source.encode()).hexdigest()
        retired_finding: dict[str, object] = {
            "code": "VELA106",
            "message": "retired pattern finding",
            "line": 2,
            "column": 58,
        }
        retired_payload: dict[str, object] = {
            "ok": True,
            "sourceHash": pattern_digest,
            "module": "Pattern",
            "gallina": "actual checked-source terms",
            "editorServices": False,
            "findings": [retired_finding],
        }
        with patch.object(playground.subprocess, "run", return_value=_process(retired_payload)):
            refused = _post(server, "/api/compile", {"source": pattern_source})
        ensure(refused["ok"] is False and "findings" not in refused,
               "retired VELA106 finding code bypassed reply validation")


def _native_cli_startup() -> None:
    commands = [command for command in COMMANDS if command.name.startswith("vela-playground")]
    ensure(len(commands) == 1 and commands[0].guest_only([]),
           "unified playground did not select exactly one native-backed launch")
    with patch("toolchain.parser.cached_build") as build, patch.object(playground_cli, "PlaygroundServer") as factory:
        prepared = build.return_value.__enter__.return_value
        prepared.executable = Path("/native/lane/build/vela-parser")
        server = factory.return_value.__enter__.return_value
        server.launch_url = "http://127.0.0.1:12345/#token=fixture"
        ensure(playground_cli.main(["--port", "0"]) == 0,
               "mathematical playground failed its prepared native startup")
        ensure(build.call_count == 1 and factory.call_args.args == (0,)
               and factory.call_args.kwargs == {"mathematical_parser": prepared.executable},
               "native parser was rebuilt per request or not supplied to the local server")
        ensure(server.serve_forever.call_count == 1,
               "prepared mathematical playground did not enter its HTTP service")
    with patch("toolchain.parser.cached_build", side_effect=RuntimeError("native tools unavailable")), \
            patch.object(playground_cli, "PlaygroundServer") as factory:
        ensure(playground_cli.main(["--port", "0"]) == 1 and not factory.called,
               "unavailable native toolchain started a mathematical service without its parser")


def _pure_authoring_rejects_mathematical_lint() -> None:
    digest = hashlib.sha256(_PURE.encode()).hexdigest()
    clean: dict[str, object] = {"ok": True, "sourceHash": digest, "bindingPreview": _PURE, "findings": []}
    invalid: dict[str, object] = {
        **clean, "findings": [{"code": "VELA105", "message": "unsupported generic type naming finding",
                              "line": 1, "column": 1}]}
    with _running() as server:
        with patch.object(playground.subprocess, "run", return_value=_process(invalid)):
            refused = _post(server, "/api/authoring", {"source": _PURE})
        ensure(refused["ok"] is False and cast("dict[str, object]", refused["error"])["kind"] == "internal"
               and "findings" not in refused and "bindingPreview" not in refused,
               "pure authoring accepted a mathematical-only naming finding")
        with patch.object(playground.subprocess, "run", return_value=_process(clean)):
            ensure(_post(server, "/api/authoring", {"source": _PURE}) == clean,
                   "pure authoring failed recovery after a refused mathematical finding")


def _playground_formatting_example_assets() -> None:
    root = Path(__file__).resolve().parents[2]
    playground_dir = root / "tools/toolchain/playground"
    docs_dir = root / "docs"
    ensure(not playground_dir.exists() or not any(playground_dir.iterdir()),
           "duplicate tools/toolchain/playground asset directory must remain retired")
    html = (docs_dir / "index.html").read_text(encoding="utf-8")
    script = (docs_dir / "app.mjs").read_text(encoding="utf-8")
    styles = (docs_dir / "style.css").read_text(encoding="utf-8")
    ensure('href="./style.css"' in html and 'src="./app.mjs"' in html,
           "playground index.html must use relative ./style.css and ./app.mjs asset paths for GitHub Pages")
    for section_id in ("overview", "playground", "pillars", "tour", "reference", "verification", "specifications"):
        ensure(f'id="{section_id}"' in html,
               f"GitHub Pages index.html omitted section #{section_id}")
    ensure("export const EXAMPLES = {" in script and "export async function browserApi(" in script,
           "playground app.mjs omitted exported EXAMPLES or in-browser browserApi runtime")
    ensure('<option value="formatting">Raw strings &amp; checked formatting</option>' in html,
           "playground selector omitted the raw-strings and checked-formatting example")
    ensure("formatting: {" in script and "Format.Write(ref " in script and '"""' in script,
           "playground app.mjs omitted the raw-strings and checked-formatting example source")
    ensure('<option value="ergonomics">Records, properties, updates &amp; guards</option>' in html,
           "playground selector omitted the records, properties, updates and guards example")
    ensure("ergonomics: {" in script and "counter with {" in script and "previous is Succ(" in script,
           "playground app.mjs omitted the records, properties, updates and guards example source")
    lexer_source = (root / "tools/toolchain/parser/lexer.mll").read_text(encoding="utf-8")
    identifier_table = lexer_source.split("let identifier state lexbuf =", 1)[1].split("let digit_run", 1)[0]
    lexer_active: set[str] = set()
    lexer_retired: set[str] = set()
    for word, action in re.findall(r'\|\s*"([A-Za-z0-9_]+)"\s*->\s*([^|\n]+)', identifier_table):
        if action.strip().startswith("refuse "):
            lexer_retired.add(word)
        else:
            lexer_active.add(word)
    grammar_block = script.split("export const VELA_GRAMMAR = Object.freeze({", 1)[1].split("});", 1)[0]

    def _grammar_words(field: str) -> set[str]:
        section = grammar_block.split(f"{field}: Object.freeze([", 1)[1].split("]),", 1)[0]
        return set(re.findall(r'"([^"]+)"', section))

    js_keywords = _grammar_words("keywords")
    js_types = _grammar_words("typeKeywords")
    js_constants = _grammar_words("constants")
    js_retired = _grammar_words("retiredKeywords")
    js_active = js_keywords | js_types | js_constants
    ensure(lexer_active <= js_active,
           f"playground VELA_GRAMMAR omitted lexer keywords: {sorted(lexer_active - js_active)}")
    ensure(js_retired == lexer_retired and not (js_active & js_retired),
           "playground VELA_GRAMMAR drifted on retired lexer keywords")
    ensure(not (js_keywords & js_types) and not (js_keywords & js_constants) and not (js_types & js_constants),
           "playground VELA_GRAMMAR keyword sets overlapped")
    ensure("export function buildVelaMonarchLanguage()" in script
           and "export const VELA_LEXICAL_PATTERNS = Object.freeze({" in script
           and "export function createTicketTracker(" in script
           and "export function projectGrammarSemanticTokens(" in script
           and "export function highlightVelaCodeHtml(" in script
           and "[^<>=\\r\\n;{}&|-]+" not in script
           and 'monaco.languages.setMonarchTokensProvider("vela", buildVelaMonarchLanguage())' in script
           and "genericArgs:" in script
           and '"typeParameter"' in script
           and '"delimiter.angle"' in script
           and ".compact-code .tok-typeParameter" in styles
           and ".compact-code .tok-angle" in styles,
           "playground app.mjs or style.css omitted grammar-coupled generic Monarch, semantic token, or static card highlighting")
    workflow = (root / ".github/workflows/pages.yml").read_text(encoding="utf-8")
    ensure("runs-on: ubuntu-26.04" in workflow and "ubuntu-latest" not in workflow,
           "GitHub Pages workflow must pin ubuntu-26.04 rather than ubuntu-latest")
    ensure("actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1" in workflow
           and "persist-credentials: false" in workflow
           and "actions/configure-pages@45bfe0192ca1faeb007ade9deae92b16b8254a0d # v6.0.0" in workflow
           and "actions/upload-pages-artifact@fc324d3547104276b827a68afc52ff2a11cc49c9 # v5.0.0" in workflow
           and "actions/deploy-pages@368f82528645a54fb793d4d04e342629a3f51346 # v5.0.1" in workflow
           and "upload-artifact@v4" not in workflow
           and "upload-pages-artifact@v3" not in workflow,
           "GitHub Pages workflow must pin Node 24 actions by SHA without deprecated Node 20 artifacts")


_NODE_RUNTIME_SCRIPT = r"""
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

const repoRoot = process.argv[2];
const playgroundDir = path.join(repoRoot, "docs");
const appPath = path.join(playgroundDir, "app.mjs");
const htmlPath = path.join(playgroundDir, "index.html");
const html = fs.readFileSync(htmlPath, "utf8");

const appUrl = pathToFileURL(appPath).href;
const mod = await import(appUrl);

const codeRegex = /<pre class="compact-code"><code>([\s\S]*?)<\/code><\/pre>/g;
const blocks = [];
let match;
while ((match = codeRegex.exec(html)) !== null) {
  const unescaped = match[1]
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&amp;/g, "&")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'");
  blocks.push(unescaped);
}
if (blocks.length < 7) {
  throw new Error(`Expected at least 7 .compact-code blocks, found ${blocks.length}`);
}
for (let i = 0; i < blocks.length; i += 1) {
  const rendered = mod.highlightVelaCodeHtml(blocks[i]);
  if (!rendered.includes("tok-keyword")) {
    throw new Error(`Compact code block ${i + 1} produced no tok-keyword spans`);
  }
}

const unparsedSnippet = [
  "// line comment",
  "/* block comment */",
  "byte Nat usize true false Zero None 'a' 'lifetime \"str\" \"\"\"raw\"\"\" 0x1f_u8 0b1010 42",
  "Read<TValue, capacity>(4)",
].join("\n");
const renderedUnparsed = mod.highlightVelaCodeHtml(unparsedSnippet);
for (const expectedClass of [
  "tok-comment",
  "tok-type",
  "tok-constant",
  "tok-string",
  "tok-number",
  "tok-function",
  "tok-typeParameter",
  "tok-parameter",
  "tok-angle",
]) {
  if (!renderedUnparsed.includes(expectedClass)) {
    throw new Error(`highlightVelaCodeHtml omitted ${expectedClass}`);
  }
}

const monarch = mod.buildVelaMonarchLanguage();
const stateNames = new Set(Object.keys(monarch.tokenizer));
for (const [stateName, rules] of Object.entries(monarch.tokenizer)) {
  for (const rule of rules) {
    if (Array.isArray(rule) && rule[0] instanceof RegExp) {
      new RegExp(rule[0].source, rule[0].flags);
    }
    const action = Array.isArray(rule) ? rule[1] : null;
    const targets = [];
    if (Array.isArray(rule) && typeof rule[2] === "string" && rule[2].startsWith("@")) {
      targets.push(rule[2]);
    } else if (action && typeof action === "object" && !Array.isArray(action) && typeof action.next === "string") {
      targets.push(action.next);
    }
    for (const target of targets) {
      if (target !== "@pop" && target !== "@push" && target !== "@popall") {
        const cleanTarget = target.replace(/^@/, "").split(".")[0];
        if (!stateNames.has(cleanTarget)) {
          throw new Error(`Monarch state ${stateName} references missing state ${target}`);
        }
      }
    }
  }
}

if (!Object.isFrozen(mod.VELA_LEXICAL_PATTERNS) || !(mod.VELA_LEXICAL_PATTERNS.callableWord instanceof RegExp)) {
  throw new Error("Expected frozen VELA_LEXICAL_PATTERNS export with shared RegExp patterns");
}
const tracker = mod.createTicketTracker((snap) => snap.ok);
const t1 = tracker.next("compile");
if (!tracker.isCurrent("compile", t1, { ok: true }) || tracker.isCurrent("compile", t1, { ok: false })) {
  throw new Error("createTicketTracker failed current snapshot check");
}
tracker.invalidate("compile");
if (tracker.isCurrent("compile", t1, { ok: true })) {
  throw new Error("createTicketTracker failed invalidate check");
}

const mixedSource = "module Mixed; public Nat Read() => At(VCons(42, VNil<Nat>()), FZero<0>());";
const read = await mod.browserApi("/api/evaluate", { source: mixedSource, expression: "Read()", valueType: "Nat" });
if (!read.ok || read.value !== "42") {
  throw new Error(`Dependent builtins failed in an ordinary function: ${JSON.stringify(read)}`);
}
const ordinarySource = "module Ordinary; public Nat Value() => 42;";
for (const [source, detail] of [["\uFEFF" + ordinarySource, "byte-order mark"],
                                [ordinarySource + "\n//\uD800", "surrogate"]]) {
  const refusal = await mod.browserApi("/api/evaluate", { source, expression: "Value()", valueType: "Nat" });
  if (refusal.ok || refusal.error?.kind !== "encoding" || !refusal.error.message.includes(detail)) {
    throw new Error("Browser source encoding diagnostic diverged: " + JSON.stringify(refusal));
  }
}
for (const source of [ordinarySource, mod.EXAMPLES.vectors.source]) {
  for (const [expression, valueType] of [["false && 1", "bool"], ["-1", "Nat"]]) {
    const refusal = await mod.browserApi("/api/evaluate", { source, expression, valueType });
    if (refusal.ok || refusal.error?.kind !== "type" || "value" in refusal) {
      throw new Error(`Expected ${expression} to refuse in ${source.split(";")[0]}: ${JSON.stringify(refusal)}`);
    }
  }
}
for (const [expression, kind] of [
  ["At(VCons(Value(), VNil<Nat>()), FZero<1>())", "type"],
  ["1; public const Nat Injected = 7", "syntax"],
]) {
  const refusal = await mod.browserApi("/api/evaluate", { source: ordinarySource, expression, valueType: "Nat" });
  if (refusal.ok || refusal.error?.kind !== kind || "value" in refusal) {
    throw new Error(`Invalid console expression ${expression} produced ${JSON.stringify(refusal)}`);
  }
}

const commentFormatSource = [
  "module Grouping;", "// Preserve the sum before multiplying.",
  "/// Computes the intended value.", "public Nat F()=>((1+2))*3; // result",
].join("\r\n");
const fmtSession = (await mod.browserApi("/api/session", {})).session;
const doc = { uri: "untitled:playground.vela", version: 1, text: commentFormatSource };
await mod.browserApi("/api/lsp", {session: fmtSession, message: { jsonrpc: "2.0", method: "textDocument/didOpen", params: { textDocument: doc } }});
const fmtReply = await mod.browserApi("/api/lsp", {session: fmtSession, message: { jsonrpc: "2.0", id: 1, method: "textDocument/formatting", params: { textDocument: { uri: doc.uri } } }});
const candidate = fmtReply.messages[0].result?.[0]?.newText;
if (!candidate || !candidate.includes("((1 + 2)) * 3; // result") ||
    !candidate.includes("// Preserve the sum before multiplying.\n/// Computes the intended value.")) {
  throw new Error("Browser formatter lost source grouping, comments, or documentation");
}
const afterFormat = await mod.browserApi("/api/evaluate", { source: candidate, expression: "F()", valueType: "Nat" });
if (!afterFormat.ok || afterFormat.value !== "9") throw new Error("Browser formatter changed evaluation");
await mod.browserApi("/api/close", { session: fmtSession });

for (const [template, expected] of [
  [String.raw`{{{ByteLength("}"):d}}}\n`, "4"],
  ["{match (true) { true => 42, false => 8, }:x4}", "4"],
  ["{true:x2}", null],
  ["{15:b8}", null],
]) {
  const source = 'module Formatting; public TextBuilder<12> F(){ let TextBuilder<12> b = EmptyBuilder(); return Format.Write(ref b, $"' + template + '"); }';
  const outcome = await mod.browserApi("/api/evaluate", { source, expression: "Written(F())", valueType: "Nat" });
  if (expected === null ? outcome.ok || outcome.error?.kind !== "type" : !outcome.ok || outcome.value !== expected) {
    throw new Error("Browser interpolation disagrees on " + template);
  }
}

const unchecked = await mod.browserApi("/api/compile", {
  source: "module Claims; public lemma EveryNatIsZero(Nat n) ensures n == 0 proof { assert n == 0; }",
});
if (!unchecked.ok || unchecked.sourceStatus !== "evaluation-preview" || unchecked.gallina !== null ||
    unchecked.uncheckedClaims?.[0]?.name !== "EveryNatIsZero") {
  throw new Error("A browser sample was presented as a proof");
}
const quantified = await mod.browserApi("/api/evaluate", {
  source: ordinarySource, expression: "forall (Nat n) => n == 0", valueType: "bool",
});
if (quantified.ok || quantified.error?.kind !== "unsupported") throw new Error("Browser evaluated an open quantifier");

const parity = { examples: {} };
for (const [key, example] of Object.entries(mod.EXAMPLES)) {
  const compiled = await mod.browserApi("/api/compile", { source: example.source });
  if (!compiled.ok || (compiled.editorServices ? !compiled.gallina : compiled.gallina !== null)) {
    throw new Error(`Example ${key} failed browserApi compile: ${JSON.stringify(compiled)}`);
  }
  const evaluated = await mod.browserApi("/api/evaluate", {
    source: example.source,
    expression: example.expression,
    valueType: example.valueType,
  });
  if (!evaluated.ok) {
    throw new Error(`Example ${key} failed browserApi evaluate: ${JSON.stringify(evaluated)}`);
  }
  const suggestions = [];
  for (const sug of example.suggestions || []) {
    const sugResult = await mod.browserApi("/api/evaluate", {
      source: example.source,
      expression: sug.expression,
      valueType: sug.valueType,
    });
    if (!sugResult.ok) {
      throw new Error(`Example ${key} suggestion ${sug.expression} failed: ${JSON.stringify(sugResult)}`);
    }
    suggestions.push({ expression: sug.expression, valueType: sug.valueType, result: sugResult });
  }
  const authoring = compiled.editorServices
    ? await mod.browserApi("/api/authoring", { source: example.source })
    : null;
  parity.examples[key] = {
    source: example.source,
    expression: example.expression,
    valueType: example.valueType,
    compiled,
    evaluated,
    suggestions,
    authoring,
  };
}

const bareLocalPureSource = [
  "module BareLocalPure;",
  "",
  "public Nat Compute(Nat x)",
  "{",
  "    Nat current = x + 1;",
  "    return current;",
  "}",
  "",
].join("\n");
const bareLocalPureCompile = await mod.browserApi("/api/compile", { source: bareLocalPureSource });
if (
  bareLocalPureCompile.ok ||
  bareLocalPureCompile.error?.message !==
    "local declaration requires 'let' or 'var' before its type (write 'let T x = e;' or 'var T x = e;')"
) {
  throw new Error(`Expected pure bare local to be refused under Q25ah: ${JSON.stringify(bareLocalPureCompile)}`);
}
const bareLocalPureAuthoring = await mod.browserApi("/api/authoring", { source: bareLocalPureSource });
if (!bareLocalPureAuthoring.ok || !bareLocalPureAuthoring.bindingPreview.includes("let Nat current = x + 1;")) {
  throw new Error(`Expected pure authoring preview to repair bare local: ${JSON.stringify(bareLocalPureAuthoring)}`);
}
parity.bareLocalPure = {
  source: bareLocalPureSource,
  compiled: bareLocalPureCompile,
  authoring: bareLocalPureAuthoring,
};

const bareLocalMath = await mod.browserApi("/api/compile", {
  source: [
    "module BareLocal;",
    "public record Box(Nat Value);",
    "public Nat Read(Box box)",
    "{",
    "    Nat current = box.Value;",
    "    return current;",
    "}",
  ].join("\n"),
});
if (
  bareLocalMath.ok ||
  bareLocalMath.error?.message !==
    "local declaration requires 'let' or 'var' before its type (write 'let T x = e;' or 'var T x = e;')"
) {
  throw new Error(`Expected mathematical bare local to be refused under Q25ah: ${JSON.stringify(bareLocalMath)}`);
}

for (const [declaration, why] of [
  ["import Flags { State };", "requires native module resolution"],
  ["public union State { ready(); }", "uppercase initial"],
  ["public union State { Ready(); Busy(); } public definition Nat Read(State s) => match (s) { ready => 1, Busy => 0 };", "binds every value"],
]) {
  const result = await mod.browserApi("/api/compile", { source: "module ConstructorCases; " + declaration });
  if (result.ok || !result.error.message.includes(why)) throw new Error(JSON.stringify(result));
}

const underscored = await mod.browserApi("/api/compile", { source: "module A_B; public Nat Read() => 0;" });
if (!underscored.gallina.includes("Module VelaEncoded_415f42.") || !underscored.gallina.includes("End VelaEncoded_415f42.")) {
  throw new Error("pure browser module name collided with a dotted module");
}

const vela105Source = [
  "module NamingCheck;",
  "public definition item Identity<item>(item value) => value;",
].join("\n");
const vela105Compiled = await mod.browserApi("/api/compile", { source: vela105Source });
if (!vela105Compiled.ok || vela105Compiled.findings?.length !== 1) {
  throw new Error(`Expected VELA105 finding on lowercase generic type parameter: ${JSON.stringify(vela105Compiled)}`);
}
parity.vela105 = vela105Compiled.findings[0];

const guardedSource = [
  "module PatternGuards;",
  "public definition bool HasRoom(Nat v) => v is Succ(prev) && prev > 0;",
  "public definition Nat Pick(Nat v) => if (true && v is Succ(n) && n is Succ(rest)) rest else 10;",
  "public Nat Read(Nat v) { if (v is Succ(n) && n > 1) { return n; } else { return 0; } }",
].join("\n");
for (const source of [ordinarySource, guardedSource]) {
  const result = await mod.browserApi("/api/evaluate", {
    source, expression: "if (4 is Succ(prev) && prev > 1) prev else 0", valueType: "Nat",
  });
  if (!result.ok || result.value !== "3") {
    throw new Error(`Pattern guards depended on the surrounding declarations: ${JSON.stringify(result)}`);
  }
}
const guardTokens = mod.projectGrammarSemanticTokens(guardedSource).tokens;
for (const [line, sourceLine] of guardedSource.split("\n").entries()) {
  for (const occurrence of sourceLine.matchAll(/\b(n|prev|rest)\b/g)) {
    if (!guardTokens.some(token => token.line === line && token.character === occurrence.index && token.type === "variable")) {
      throw new Error(`Missing guarded pattern variable at ${line}:${occurrence.index}`);
    }
  }
}
for (const [expression, valueType, expected] of [
  ["HasRoom(0)", "bool", "false"], ["HasRoom(2)", "bool", "true"],
  ["Pick(1)", "Nat", "10"], ["Pick(5)", "Nat", "3"], ["Read(5)", "Nat", "4"],
]) {
  const result = await mod.browserApi("/api/evaluate", { source: guardedSource, expression, valueType });
  if (!result.ok || result.value !== expected) {
    throw new Error(`Pattern guard evaluation failed for ${expression}: ${JSON.stringify(result)}`);
  }
}
for (const expression of [
  "if (0 is Succ(n) && n > 1) 1 else n",
  "if (0 is Succ(n) || n == 0) 1 else 0",
]) {
  const result = await mod.browserApi("/api/evaluate", { source: guardedSource, expression, valueType: "Nat" });
  if (result.ok || result.error?.kind !== "name") {
    throw new Error(`Pattern binding escaped in ${expression}: ${JSON.stringify(result)}`);
  }
}

class MockElement {
  constructor(tagName = "div", id = "") {
    this.tagName = tagName.toUpperCase();
    this.id = id;
    this.className = "";
    this.textContent = "";
    this._innerHTML = "";
    this.value = "";
    this.hidden = false;
    this.disabled = false;
    this.checked = true;
    this.open = false;
    this.title = "";
    this.type = "";
    this.tabIndex = 0;
    this.selectionStart = 0;
    this.selectionEnd = 0;
    this.dataset = {};
    this.attributes = new Map();
    this.children = [];
    this.listeners = new Map();
    const self = this;
    this.classList = {
      _set: new Set(),
      add(... tokens) { tokens.forEach((t) => this._set.add(t)); },
      remove(...tokens) { tokens.forEach((t) => this._set.delete(t)); },
      toggle(token, force) {
        const shouldAdd = force === undefined ? !this._set.has(token) : Boolean(force);
        if (shouldAdd) this._set.add(token);
        else this._set.delete(token);
        return shouldAdd;
      },
      contains(token) { return this._set.has(token); },
    };
  }
  get innerHTML() { return this._innerHTML; }
  set innerHTML(val) { this._innerHTML = String(val); }
  setAttribute(k, v) { this.attributes.set(k, String(v)); }
  getAttribute(k) { return this.attributes.get(k) ?? null; }
  addEventListener(type, fn) {
    if (!this.listeners.has(type)) this.listeners.set(type, []);
    this.listeners.get(type).push(fn);
  }
  dispatchEvent(type, event = {}) {
    const handlers = this.listeners.get(type) || [];
    return Promise.all(handlers.map((fn) => fn({ preventDefault() {}, target: this, ...event })));
  }
  append(...nodes) {
    this.children.push(...nodes);
    for (const node of nodes) {
      if (node && node.tagName === "SCRIPT" && typeof node.onload === "function") {
        queueMicrotask(() => node.onload());
      }
    }
  }
  replaceChildren(...nodes) {
    this.children = [...nodes];
  }
  contains(other) { return other === this || this.children.includes(other); }
  focus() {}
  scrollIntoView() {}
  setRangeText(replacement, start, end) {
    this.value = this.value.slice(0, start) + replacement + this.value.slice(end);
  }
}

const elementsById = new Map();
for (const m of html.matchAll(/\bid="([^"]+)"/g)) {
  const id = m[1];
  if (!elementsById.has(id)) {
    const el = new MockElement("div", id);
    if (id === "inspect-panel" || id === "authoring-panel") el.hidden = true;
    if (id === "examples") el.value = "squares";
    if (id === "expression") el.value = mod.EXAMPLES.squares.expression;
    if (id === "value-type") el.value = mod.EXAMPLES.squares.valueType;
    elementsById.set(id, el);
  }
}

const tabButtons = [];
for (const m of html.matchAll(/\bdata-tab="([^"]+)"/g)) {
  const btn = new MockElement("button");
  btn.dataset.tab = m[1];
  tabButtons.push(btn);
}

const loadExampleButtons = [];
for (const m of html.matchAll(/\bdata-load-example="([^"]+)"/g)) {
  const btn = new MockElement("button");
  btn.setAttribute("data-load-example", m[1]);
  loadExampleButtons.push(btn);
}

const expandLinks = [];
for (const m of html.matchAll(/\bdata-expand-target="([^"]+)"/g)) {
  const link = new MockElement("a");
  link.setAttribute("data-expand-target", m[1]);
  expandLinks.push(link);
}

const compactCodes = blocks.map((text) => {
  const code = new MockElement("code");
  code.textContent = text;
  return code;
});

const headEl = new MockElement("head");
const bodyEl = new MockElement("body");

globalThis.document = Object.assign(new MockElement("document"), {
  head: headEl,
  body: bodyEl,
  activeElement: null,
  getElementById(id) {
    if (!elementsById.has(id)) {
      elementsById.set(id, new MockElement("div", id));
    }
    return elementsById.get(id);
  },
  createElement(tag) { return new MockElement(tag); },
  querySelector(sel) {
    const tabMatch = /^\[data-tab="([^"]+)"\]$/.exec(sel);
    if (tabMatch) return tabButtons.find((b) => b.dataset.tab === tabMatch[1]) || null;
    return null;
  },
  querySelectorAll(sel) {
    if (sel === ".compact-code code") return compactCodes;
    if (sel === "[data-tab]") return tabButtons;
    if (sel === "[data-load-example]") return loadExampleButtons;
    if (sel === "[data-expand-target]") return expandLinks;
    return [];
  },
});

const mockModel = {
  _val: mod.EXAMPLES.squares.source,
  getValue() { return this._val; },
  setValue(v) { this._val = String(v); this._onChange?.(); },
  onDidChangeContent(handler) { this._onChange = handler; },
  dispose() {},
};
let markers = [];
const mockEditor = {
  updateOptions() {},
  setPosition() {},
  onDidChangeCursorPosition() {},
  onDidChangeCursorSelection() {},
  addCommand() {},
  hasTextFocus() { return false; },
  getPosition() { return { lineNumber: 1, column: 1 }; },
  getSelection() { return { isEmpty() { return true; } }; },
  setSelection() {},
  revealRangeInCenter() {},
  focus() {},
  trigger() {},
  dispose() {},
};

globalThis.window = {
  MonacoEnvironment: null,
  require: Object.assign(
    (_deps, onLoad) => { queueMicrotask(() => onLoad({})); },
    { config() {} }
  ),
  monaco: {
    KeyMod: { CtrlCmd: 2048 },
    KeyCode: { Enter: 3 },
    MarkerSeverity: { Error: 8, Warning: 4 },
    SymbolKind: { Module: 1, Function: 11, Constant: 13, Variable: 12 },
    InlayHintKind: { Parameter: 2, Type: 1 },
    Uri: { parse(u) { return u; } },
    languages: {
      register() {},
      setMonarchTokensProvider() {},
      setLanguageConfiguration() {},
      registerHoverProvider() {},
      registerDefinitionProvider() {},
      registerReferenceProvider() {},
      registerDocumentHighlightProvider() {},
      registerDocumentSymbolProvider() {},
      registerInlayHintsProvider() {},
      registerDocumentSemanticTokensProvider() {},
      registerDocumentFormattingEditProvider() {},
    },
    editor: {
      defineTheme() {},
      createModel(text) {
        mockModel._val = text;
        return mockModel;
      },
      create() { return mockEditor; },
      setModelMarkers(_model, _owner, next) { markers = next; },
    },
  },
  addEventListener() {},
};
globalThis.location = { hash: "", pathname: "/", search: "" };
globalThis.history = { replaceState() {} };
globalThis.sessionStorage = { getItem() { return null; }, setItem() {} };

await import(`${appUrl}?ui=1`);
await new Promise((resolve) => setTimeout(resolve, 60));

const connLabel = elementsById.get("connection-label").textContent;
if (connLabel !== "In-browser engine ready") {
  throw new Error(`Expected connection-label 'In-browser engine ready', got '${connLabel}'`);
}
if (elementsById.get("compile-summary").textContent.includes("Connection changed")
    || elementsById.get("authoring-summary").textContent.includes("Connection changed")
    || elementsById.get("console-result").children[0]?.children.some((child) => child.textContent.includes("Connection changed"))) {
  throw new Error("First connection showed a reconnect notice in an output panel");
}
if (elementsById.get("editor-notice").hidden !== true || elementsById.get("editor").hidden !== false) {
  throw new Error("Expected Monaco editor to finish loading and hide #editor-notice");
}
for (let i = 0; i < compactCodes.length; i += 1) {
  if (!compactCodes[i].innerHTML.includes("tok-keyword")) {
    throw new Error(`UI startup failed to highlight .compact-code block ${i + 1}`);
  }
}

async function expectConsoleValue(expression, expected) {
  elementsById.get("expression").value = expression;
  elementsById.get("value-type").value = "Nat";
  await elementsById.get("evaluate-form").dispatchEvent("submit");
  const card = elementsById.get("console-result").children[0];
  const texts = card.children.map((child) => child.textContent);
  if (!texts.includes(expected)) {
    throw new Error(`UI evaluate failed for ${expression}: ${JSON.stringify(texts)}`);
  }
}

const indexedSquare = "At(VCons(Square(7), VNil<Nat>()), FZero<0>())";
await expectConsoleValue(indexedSquare, "49");
await elementsById.get("compile-button").dispatchEvent("click");
if (!elementsById.get("gallina-output").textContent.includes("Module Vela_Playground.")) {
  throw new Error(`UI compile failed: ${elementsById.get("gallina-output").textContent}`);
}
await elementsById.get("check-authoring").dispatchEvent("click");
if (!elementsById.get("binding-preview").textContent.includes("module Playground;")) {
  throw new Error("Style check did not produce a preview of the current source");
}
await expectConsoleValue(indexedSquare, "49");

const form = elementsById.get("evaluate-form");
for (const [id, modifier] of [["value-type", "metaKey"], ["evaluate-button", "ctrlKey"]]) {
  const target = elementsById.get(id);
  form.append(target);
  document.activeElement = target;
  const previousResult = elementsById.get("console-result").children[0];
  await document.dispatchEvent("keydown", { target, key: "Enter", [modifier]: true });
  if (elementsById.get("console-panel").hidden || elementsById.get("console-result").children[0] === previousResult) {
    throw new Error(`The evaluation shortcut did not evaluate from #${id}`);
  }
}
document.activeElement = null;

await elementsById.get("reconnect-button").dispatchEvent("click");
if (!elementsById.get("download-output").disabled || elementsById.get("console-result").children[0].className !== "empty-console") {
  throw new Error("Reconnecting retained a result from the previous connection");
}

if (elementsById.get("binding-preview").textContent !== "No current preview.") {
  throw new Error("Reconnecting retained an authoring preview from the previous connection");
}

const invalid = "module Invalid; public Nat Wrong() => true;";
const refusal = await mod.browserApi("/api/compile", { source: invalid });
mockModel.setValue(invalid);
await elementsById.get("compile-button").dispatchEvent("click");
if (refusal.ok || markers.length !== 1 || !markers[0].message.includes(refusal.error.message)) {
  throw new Error(`Expected the full compiler diagnostic after editor synchronization: ${JSON.stringify(markers)}`);
}

elementsById.get("examples").value = "vectors";
await elementsById.get("examples").dispatchEvent("change");
await expectConsoleValue("Second()", "20");

elementsById.get("examples").value = "squares";
await elementsById.get("examples").dispatchEvent("change");
await expectConsoleValue(indexedSquare, "49");
console.log(JSON.stringify(parity));
"""


def _node_command(root: Path) -> tuple[list[str], str] | None:
    node = shutil.which("node")
    if node is not None:
        return [node, "--input-type=module", "-", str(root)], _NODE_RUNTIME_SCRIPT
    if sys.platform == "win32" and shutil.which("wsl.exe") is not None:
        resolved = root.resolve()
        drive = resolved.drive.rstrip(":").lower()
        rel = resolved.as_posix().split(":/", 1)[1]
        wsl_root = f"/mnt/{drive}/{rel}"
        return ["wsl.exe", "-u", "root", "-e", "node", "--input-type=module", "-", wsl_root], _NODE_RUNTIME_SCRIPT
    return None


@cache
def _browser_results() -> str:
    root = Path(__file__).resolve().parents[2]
    cmd_info = _node_command(root)
    if cmd_info is None:
        raise AssertionError("Node.js runtime is required on host or WSL to execute playground app.mjs")
    cmd, script_input = cmd_info
    done = subprocess.run(
        cmd,
        input=script_input,
        capture_output=True,
        encoding="utf-8",
        errors="replace",
        check=False,
        timeout=30,
    )
    ensure(
        done.returncode == 0,
        f"playground app.mjs runtime or UI startup check failed (exit {done.returncode}):\n{done.stderr or done.stdout}",
    )
    return done.stdout


def _playground_browser_runtime_and_ui_startup() -> None:
    parity = json.loads(_browser_results())
    prepared = Path("/prepared/native/vela-parser")
    for key, entry in parity["examples"].items():
        if entry["compiled"]["editorServices"]:
            source = entry["source"]
            ensure(entry["compiled"]["gallina"] == translate(source.encode()).gallina,
                   f"example {key} lost canonical Gallina for ordinary functions")
            ensure(entry["authoring"] == compile_request({"action": "authoring", "source": source},
                                                        mathematical_parser=prepared),
                   f"example {key} drifted on authoring previews or lint findings")
    bare = parity["bareLocalPure"]
    ensure(bare["authoring"] == compile_request({"action": "authoring", "source": bare["source"]},
                                               mathematical_parser=prepared),
           "bare local pure authoring preview drifted between browserApi and playground_worker")
    canonical_vela105 = authoring.generic_type_findings((syntax.Name("item", syntax.Site(2, 33)),))[0]
    ensure(parity["vela105"] == {
        "code": canonical_vela105.code,
        "message": canonical_vela105.message,
        "line": canonical_vela105.line,
        "column": canonical_vela105.column,
    }, "browserApi mathematical VELA105 finding drifted from canonical authoring.generic_type_findings")


def _catalog_native_parity() -> None:
    parity = json.loads(_browser_results())
    with parser.cached_build(Path(__file__).resolve().parents[2]) as built:
        for key, entry in parity["examples"].items():
            source = entry["source"]
            compiled = compile_request({"action": "compile", "source": source}, mathematical_parser=built.executable)
            expected = entry["compiled"]
            for field in ("ok", "sourceHash", "module", "findings", "editorServices"):
                ensure(compiled.get(field) == expected[field], f"example {key} differs on {field}: {compiled.get('error')}")
            if expected["editorServices"]:
                ensure(compiled["gallina"] == expected["gallina"], f"example {key} differs on canonical Gallina")
            for observation in [entry, *entry["suggestions"]]:
                evaluated = compile_request({"action": "evaluate", "source": source, "expression": observation["expression"],
                                            "valueType": observation["valueType"]}, mathematical_parser=built.executable)
                ensure(evaluated == observation.get("evaluated", observation.get("result")),
                       f"example {key} differs on {observation['expression']}: {evaluated}")


def cases() -> list[Case]:
    return [Case("whole-language-http-request-shape", _http_whole_language_request_shape),
            Case("unified-http-source-routing-and-request-field-refusals", _http_dispatch_and_strict_fields),
            Case("mathematical-worker-source-type-and-schema-refusals-with-recovery", _worker_reply_binding),
            Case("mathematical-changed-parser-identity-refuses-before-worker", _changed_parser_refuses),
            Case("mathematical-worker-reuses-elaborator-and-preserves-refusals", _worker_mathematical_routing),
            Case("full-language-compilation-and-evaluation-in-ordinary-modules", _full_language_in_ordinary_modules),
            Case("mathematical-naming-findings-source-shape-budget-and-recovery", _mathematical_naming_reply_validation),
            Case("pure-authoring-refuses-mathematical-only-naming-finding", _pure_authoring_rejects_mathematical_lint),
            Case("mathematical-cli-prepares-native-parser-once-and-refuses-missing-tools", _native_cli_startup),
            Case("playground-formatting-example-assets", _playground_formatting_example_assets),
            Case("playground-browser-runtime-and-ui-startup", _playground_browser_runtime_and_ui_startup),
            Case("playground-browser-and-native-catalog-parity", _catalog_native_parity, lane="toolchain")]
