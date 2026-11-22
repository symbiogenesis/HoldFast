# SPDX-License-Identifier: Apache-2.0
"""Wire fixtures for real LSP processes, including an independent frame reader."""

import json
import subprocess
import sys
from collections.abc import Callable, Iterable, Iterator
from io import BytesIO
from typing import cast

from tests.harness import TOOLS, ensure


def server_command() -> list[str]:
    return [sys.executable, "-I", "-c",
            "import sys; sys.path.insert(0, sys.argv.pop(1)); "
            "from toolchain.cli.vela_lsp import main; raise SystemExit(main())",
            str(TOOLS)]


def frame(message: dict[str, object]) -> bytes:
    body = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body


def run_server(messages: Iterable[dict[str, object]],
               encode: Callable[[dict[str, object]], bytes] = frame) -> BytesIO:
    wire = b"".join(map(encode, messages))
    completed = subprocess.run(server_command(), input=wire, capture_output=True, timeout=30, check=False)
    ensure(completed.returncode == 0 and not completed.stderr,
           f"LSP process exited {completed.returncode}: {completed.stderr!r}")
    return BytesIO(completed.stdout)


def read_replies(stream: BytesIO) -> Iterator[dict[str, object]]:
    while header := stream.readline():
        ensure(header.startswith(b"Content-Length: ") and header.endswith(b"\r\n"),
               f"malformed LSP frame header: {header!r}")
        size = int(header.removeprefix(b"Content-Length: ").strip())
        ensure(stream.readline() == b"\r\n", "LSP frame omitted its separator")
        body = stream.read(size)
        ensure(len(body) == size, "truncated LSP reply body")
        value = json.loads(body)
        ensure(isinstance(value, dict), f"expected LSP message object: {value!r}")
        yield cast("dict[str, object]", value)
