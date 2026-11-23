# SPDX-License-Identifier: Apache-2.0
"""One bounded pure-prototype check, run by the host language server's worker."""

import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import cast

from toolchain import MAX_SOURCE_BYTES, HoldFastError, inspect_source, translate
from toolchain.authoring import format_source
from toolchain.completion import recover
from toolchain.concrete import parts
from toolchain.protocol_json import MAX_BODY_BYTES


def worker_command(*args: str) -> list[str]:
    """Build an isolated `-I` command line for the checkout's fixed worker."""
    tools = str(Path(__file__).resolve().parents[1])
    script = (f"import sys; sys.path.insert(0, {tools!r}); "
              "from toolchain.lsp_worker import main; raise SystemExit(main())")
    return [sys.executable, "-I", "-c", script, *args]


def run_worker(source: bytes, *args: str) -> bytes:
    """Run one isolated compiler operation with the language server's time and output bounds."""
    done = subprocess.run(worker_command(*args), input=source, capture_output=True, timeout=5, check=False)
    if done.returncode or len(done.stdout) > MAX_BODY_BYTES:
        raise ValueError("compiler worker failed or exceeded its output bound")
    return done.stdout


def main() -> int:
    source = sys.stdin.buffer.read(MAX_SOURCE_BYTES + 1)
    result: dict[str, object]
    match sys.argv[1:]:
        case []:
            error_data = None
            try:
                translate(source)
            except HoldFastError as error:
                error_data = {"kind": error.kind, "line": error.line, "column": error.column,
                              "message": error.message[:4096]}
            print(json.dumps(error_data, ensure_ascii=True))
            return 0
        case ["--comparison-action", first, last]:
            # The preview consumes the snapshot worker, which imports this entry point.
            from toolchain.authoring_preview import selection  # noqa: PLC0415

            try:
                start, end = int(first), int(last)
                preview = selection(source, start, end)
            except (ValueError, HoldFastError, OSError):
                return 2
            result = {"selection": [start, end], "edit": None}
            if preview is not None:
                binding = cast("dict[str, object]", preview["binding"])
                result["edit"] = {key: preview[key] for key in ("span", "replacement", "candidate_sha256")}
                result["producer"] = cast("dict[str, object]", binding["producer"])["version"]
        case ["--complete-at", cursor]:
            try:
                result = recover(source, int(cursor))
            except (ValueError, HoldFastError):
                return 2
        case ["--format"]:
            try:
                result = {"status": "ok", "formatted": format_source(source, syntax_only=True).decode("utf-8")}
            except HoldFastError as error:
                result = {"status": "unavailable", "reason": error.kind}
        case [("--inspect" | "--inspect-snapshot" | "--inspect-completion") as mode]:
            try:
                result = inspect_source(source, syntax_tree=mode == "--inspect-snapshot",
                                        completion_options=mode == "--inspect-completion")
                if mode == "--inspect-snapshot":
                    result["concrete"] = parts(source)
            except HoldFastError as error:
                result = {"status": "unavailable", "reason": error.kind}
        case _:
            return 2

    digest = hashlib.sha256(source).hexdigest()
    result["source_sha256"] = digest
    encoded = json.dumps(result, ensure_ascii=True)
    if len(encoded) > MAX_BODY_BYTES:
        if sys.argv[1] not in {"--inspect", "--inspect-snapshot", "--inspect-completion"}:
            return 1
        encoded = json.dumps({"status": "unavailable", "reason": "inspection-limit", "source_sha256": digest})
    print(encoded, end="")
    return 0
