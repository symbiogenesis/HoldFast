# SPDX-License-Identifier: Apache-2.0
"""Isolated compiler worker for the local browser playground."""

import hashlib
import sys
from dataclasses import asdict
from pathlib import Path
from typing import cast

from toolchain import (
    Translation,
    ValueType,
    VelaError,
    translate,
)
from toolchain import (
    mathematical as vela_mathematical,
)
from toolchain.authoring import lint_source, preview_bindings
from toolchain.elaborate_holes import OpenGoalsError
from toolchain.hashing import file_sha256
from toolchain.protocol_json import MAX_BODY_BYTES, decode_message, encode_body


def _editor_translation(source: bytes) -> Translation | VelaError | None:
    """Check compatibility with the pure editor services and their canonical emitter."""
    try:
        return translate(source)
    except VelaError as error:
        return error
    except (OSError, RuntimeError, ValueError):
        return None


def compile_request(request: dict[str, object], *, mathematical_parser: Path) -> dict[str, object]:
    source = cast("str", request["source"]).encode("utf-8")
    digest = hashlib.sha256(source).hexdigest()
    if "mode" in request:
        raise ValueError("The playground does not accept a language mode")
    try:
        if request["action"] == "authoring":
            preview = preview_bindings(source)
            findings = lint_source(preview)
            return {"ok": True, "sourceHash": digest,
                    "findings": [{"code": finding.code, "message": finding.message,
                                  "line": finding.line, "column": finding.column}
                                 for finding in findings],
                    "bindingPreview": preview.decode("utf-8")}
        if request["action"] == "compile":
            compiled = vela_mathematical.compile_source(source, mathematical_parser)
            editor = _editor_translation(source)
            return {"ok": True, "sourceHash": digest,
                    "module": compiled.module,
                    "gallina": editor.gallina if isinstance(editor, Translation) else compiled.gallina,
                    "editorServices": isinstance(editor, Translation),
                    "findings": [{"code": finding.code, "message": finding.message,
                                  "line": finding.line, "column": finding.column}
                                 for finding in compiled.findings]}
        if request["action"] != "evaluate":
            raise ValueError("Unknown compiler request")
        result = vela_mathematical.evaluate_source(
            source, cast("str", request["expression"]), cast("ValueType", request["valueType"]), mathematical_parser)
        value = ("true" if result.value else "false") if result.value_type == "bool" else str(result.value)
    except VelaError as error:
        response: dict[str, object] = {
            "ok": False, "sourceHash": digest,
            "error": {"kind": error.kind, "message": error.message,
                      "line": error.line, "column": error.column}}
        if request["action"] == "compile":
            if isinstance(error, OpenGoalsError):
                response["goals"] = [asdict(goal) for goal in error.goals]
                primary = error.stopped
                response["error"] = {"kind": primary.kind if primary else "open-goals",
                                     "message": primary.message if primary else "Provide a term at each named hole",
                                     "line": error.line, "column": error.column}
                response["editorServices"] = False
                return response
            editor = _editor_translation(source)
            response["editorServices"] = (isinstance(editor, VelaError)
                                          and editor.kind == error.kind and error.kind in {"name", "type"})
        return response
    return {"ok": True, "sourceHash": digest, "valueType": result.value_type, "value": value}


def require_parser(parser: Path, digest: str) -> None:
    if file_sha256(parser) != digest:
        raise ValueError("prepared mathematical parser is unavailable or changed")


def main(*, mathematical_parser: Path, parser_sha256: str) -> int:
    try:
        request = decode_message(sys.stdin.buffer.read(MAX_BODY_BYTES + 1))
        if request["action"] != "authoring":
            require_parser(mathematical_parser, parser_sha256)
        response = compile_request(request, mathematical_parser=mathematical_parser)
        raw = encode_body(response)
    except (KeyError, TypeError, ValueError, UnicodeError, OSError, RuntimeError):
        return 1
    sys.stdout.buffer.write(raw)
    return 0
