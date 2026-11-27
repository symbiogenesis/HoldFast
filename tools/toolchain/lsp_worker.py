# SPDX-License-Identifier: Apache-2.0
"""One bounded pure-prototype check, run by the host language server's worker."""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import cast

from toolchain import MAX_SOURCE_BYTES, HoldFastError, inspect_source, translate
from toolchain._isolated_worker import (
    IsolatedBatchWorker,
    cast_str_list,
    decode_header_pair,
    read_exact,
    write_batch_reply,
)
from toolchain.authoring import format_source
from toolchain.completion import recover
from toolchain.concrete import parts
from toolchain.protocol_json import MAX_BODY_BYTES

_SUBPROCESS_RUN = subprocess.run
_BATCH_WORKER = IsolatedBatchWorker()
_WORKER_TIMEOUT_SECONDS = 5


def worker_command(*args: str) -> list[str]:
    """Build an isolated `-I` command line for the checkout's fixed worker."""
    tools = str(Path(__file__).resolve().parents[1])
    script = (f"import sys; sys.path.insert(0, {tools!r}); "
              "from toolchain.lsp_worker import main; raise SystemExit(main())")
    return [sys.executable, "-I", "-c", script, *args]


def reset_worker() -> None:
    """Terminate the persistent isolated LSP batch worker if active."""
    _BATCH_WORKER.reset()


def run_worker(source: bytes, *args: str) -> bytes:
    """Run one isolated compiler operation with the language server's time and output bounds."""
    if getattr(subprocess, "run", None) is not _SUBPROCESS_RUN:
        done = subprocess.run(
            worker_command(*args), input=source, capture_output=True,
            timeout=_WORKER_TIMEOUT_SECONDS, check=False,
        )
        if done.returncode or len(done.stdout) > MAX_BODY_BYTES:
            raise ValueError("compiler worker failed or exceeded its output bound")
        return done.stdout
    bounded = source[:MAX_SOURCE_BYTES + 1]
    args_json = json.dumps(list(args), ensure_ascii=True, separators=(",", ":")).encode("utf-8")
    header = f"{len(bounded)} ".encode("ascii") + args_json + b"\n"
    key = (
        sys.executable,
        os.environ.get("VOS_BUILD_ROOT"),
        os.environ.get("VOS_ROCQ"),
        os.environ.get("VOS_ROCQCHK"),
        os.environ.get("OPAMROOT"),
        MAX_BODY_BYTES,
    )
    code, body = _BATCH_WORKER.request(
        key,
        worker_command("--batch"),
        header,
        bounded,
        timeout_seconds=_WORKER_TIMEOUT_SECONDS,
        max_body_bytes=MAX_BODY_BYTES,
    )
    if code != 0 or len(body) > MAX_BODY_BYTES:
        raise ValueError("compiler worker failed or exceeded its output bound")
    return body


def _execute(source: bytes, argv_tail: list[str]) -> tuple[int, bytes]:
    result: dict[str, object]
    match argv_tail:
        case []:
            error_data = None
            try:
                translate(source)
            except HoldFastError as error:
                error_data = {"kind": error.kind, "line": error.line, "column": error.column,
                              "message": error.message[:4096]}
            return 0, json.dumps(error_data, ensure_ascii=True).encode("utf-8")
        case ["--comparison-action", first, last]:
            # The preview consumes the snapshot worker, which imports this entry point.
            from toolchain.authoring_preview import selection  # noqa: PLC0415

            try:
                start, end = int(first), int(last)
                preview = selection(source, start, end)
            except (ValueError, HoldFastError, OSError):
                return 2, b""
            result = {"selection": [start, end], "edit": None}
            if preview is not None:
                binding = cast("dict[str, object]", preview["binding"])
                result["edit"] = {key: preview[key] for key in ("span", "replacement", "candidate_sha256")}
                result["producer"] = cast("dict[str, object]", binding["producer"])["version"]
        case ["--complete-at", cursor]:
            try:
                result = recover(source, int(cursor))
            except (ValueError, HoldFastError):
                return 2, b""
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
            return 2, b""

    digest = hashlib.sha256(source).hexdigest()
    result["source_sha256"] = digest
    encoded = json.dumps(result, ensure_ascii=True)
    if len(encoded) > MAX_BODY_BYTES:
        if argv_tail not in (["--inspect"], ["--inspect-snapshot"], ["--inspect-completion"]):
            return 1, b""
        encoded = json.dumps({"status": "unavailable", "reason": "inspection-limit", "source_sha256": digest})
    return 0, encoded.encode("utf-8")


def serve_batch() -> int:
    """Process length-framed compiler requests sequentially in an isolated worker."""
    stdin = sys.stdin.buffer
    stdout = sys.stdout.buffer
    while line := stdin.readline(8192):
        parsed = decode_header_pair(line)
        if parsed is None:
            return 2
        length, raw_args = parsed
        if length > MAX_SOURCE_BYTES + 1:
            return 1
        source = read_exact(stdin, length)
        if source is None:
            return 2
        try:
            argv_tail = cast_str_list(json.loads(raw_args))
        except ValueError:
            return 2
        code, body = _execute(source, argv_tail)
        write_batch_reply(stdout, code, body)
    return 0


def main() -> int:
    if sys.argv[1:] == ["--batch"]:
        return serve_batch()
    source = sys.stdin.buffer.read(MAX_SOURCE_BYTES + 1)
    code, body = _execute(source, sys.argv[1:])
    if body:
        sys.stdout.write(body.decode("utf-8"))
    return code
