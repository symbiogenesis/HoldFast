# SPDX-License-Identifier: Apache-2.0
"""Versioned, source-bound comparison edits through the real LSP protocol."""

import subprocess
import sys
import tempfile
from io import BytesIO
from pathlib import Path
from typing import cast
from unittest.mock import patch

from tests.harness import Case, ensure
from tests.test_vela_lsp_projection import _error_code, _notice, _request
from toolchain import authoring_preview, lsp_actions, trace_runtime
from toolchain.lsp import Server
from toolchain.protocol_json import decode_message, encode_message, read_frame

INDEPENDENT_CASES = True
_URI = "untitled:actions.vela"
_SOURCE = "// \U0001f600 keep == here\r\nmodule M;\r\npublic bool F(bool x) => x == false;\r\n"


def _initialize(versions: bool = True, kind: str = "refactor.rewrite") -> dict[str, object]:
    return _request("initialize", {"capabilities": {
        "workspace": {"workspaceEdit": {"documentChanges": versions}},
        "textDocument": {"codeAction": {"codeActionLiteralSupport": {"codeActionKind": {"valueSet": [kind]}}}}}})


def _open() -> dict[str, object]:
    return _notice("textDocument/didOpen", {"textDocument": {
        "uri": _URI, "version": 7, "languageId": "vela", "text": _SOURCE}})


def _range(line: int, first: int, last: int) -> dict[str, object]:
    return {"start": {"line": line, "character": first}, "end": {"line": line, "character": last}}


def _action(line: int, first: int, last: int, identity: int = 2, **context: object) -> dict[str, object]:
    return _request("textDocument/codeAction", {"textDocument": {"uri": _URI},
        "range": _range(line, first, last), "context": {"diagnostics": [], **context}}, identity)


def _stdio() -> None:
    changed = _SOURCE.replace("x == false", "true == x")
    messages = [_initialize(), _notice("initialized"), _open(), _action(2, 28, 28),
                _notice("textDocument/didChange", {"textDocument": {"uri": _URI, "version": 8},
                                                    "contentChanges": [{"text": changed}]}),
                _action(2, 25, 34, 3, only=["refactor"]), _action(0, 11, 13, 4),
                _action(2, 25, 34, 5, only=["quickfix"]), _request("shutdown", identity=6), _notice("exit")]
    completed = subprocess.run([sys.executable, str(Path(__file__).resolve().parents[1] / "run.py"), "vela-lsp"],
                               input=b"".join(encode_message(message) for message in messages),
                               capture_output=True, timeout=45, check=False)
    ensure(completed.returncode == 0, f"stdio action session failed: {completed.stderr!r}")
    stream, replies = BytesIO(completed.stdout), {}
    while (frame := read_frame(stream)) is not None:
        reply = decode_message(frame)
        if "id" in reply:
            replies[cast("int", reply["id"])] = reply
    capabilities = cast("dict[str, dict[str, object]]", replies[1]["result"])["capabilities"]
    ensure(capabilities["codeActionProvider"] == {"codeActionKinds": ["refactor.rewrite"]},
           "client did not negotiate checked rewrite actions")
    for identity, version, end, text in ((2, 7, 35, "!(x)"), (3, 8, 34, "(x)")):
        expected = [{"title": "Simplify Boolean comparison (VELA103)", "kind": "refactor.rewrite",
                     "edit": {"documentChanges": [{"textDocument": {"uri": _URI, "version": version},
                         "edits": [{"range": _range(2, 25, end), "newText": text}]}]}}]
        ensure(replies[identity].get("result") == expected, f"incorrect versioned action: {replies[identity]}")
    ensure(replies[4].get("result") == [] and replies[5].get("result") == [],
           "a comment or an excluded action kind produced a rewrite")


def _selection_and_lifecycle() -> None:
    for expression in ("x == x", "x // retain\n == true", "(x == true) == false"):
        source = f"module M; public bool F(bool x) => {expression};".encode()
        ensure(authoring_preview.selection(source, 0, len(source)) is None,
               "a nonliteral, comment-bearing, or ambiguous range produced an edit")
    for versions, kind in ((False, "refactor"), (True, "quickfix")):
        server = Server(checker=lambda _: None)
        response = server.handle(_initialize(versions, kind))[0]
        ensure("codeActionProvider" not in cast("dict[str, dict[str, object]]", response["result"])["capabilities"],
               "an unsupported client received the action capability")
        server.handle(_notice("initialized"))
        server.handle(_open())
        ensure(_error_code(server.handle(_action(2, 28, 28))) == -32803,
               "client without versioned rewrite support received an action")
    server = Server(checker=lambda _: None)
    server.handle(_initialize())
    server.handle(_notice("initialized"))
    server.handle(_open())
    ensure(_error_code(server.handle(_action(2, 30, 29))) == -32602, "reversed range produced an action")
    ensure(_error_code(server.handle(_action(0, 4, 4))) == -32602, "split surrogate produced an action")
    with patch.object(lsp_actions, "actions", side_effect=lambda *_: server.invalidate_inspections()):
        ensure(_error_code(server.handle(_action(2, 28, 28))) == -32803,
               "a late result survived dependency invalidation")


def _interpreter_mismatch() -> None:
    server = Server(checker=lambda _: None)
    server.handle(_initialize())
    server.handle(_notice("initialized"))
    server.handle(_open())
    with tempfile.TemporaryDirectory() as directory:
        library = Path(directory) / "alternate-interpreter"
        library.write_bytes(b"same version label and compiler checkout, different interpreter")
        # The isolated worker still observes its installed interpreter.
        with patch.object(trace_runtime, "configured_shared_library", return_value=library):
            ensure(_error_code(server.handle(_action(2, 28, 28))) == -32803,
                   "server published a checked edit from a different interpreter")
    response = server.handle(_action(2, 28, 28, 3))[0]
    ensure(len(cast("list[object]", response["result"])) == 1, "restoring the interpreter failed to restore edits")


def cases() -> list[Case]:
    return [Case("checked comparison actions over stdio and unsaved overlays", _stdio),
            Case("comparison selection, negotiation and generation refusal", _selection_and_lifecycle),
            Case("mixed interpreter generations with an isolated comparison worker", _interpreter_mismatch)]
