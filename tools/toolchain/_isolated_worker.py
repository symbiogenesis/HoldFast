# SPDX-License-Identifier: Apache-2.0
"""Persistent `-I` isolated batch worker process helper for compiler frontends."""

import atexit
import contextlib
import queue
import re
import subprocess
import threading
from typing import BinaryIO, cast

_HEADER_RE = re.compile(rb"^(-?[0-9]+) ([0-9]+)\r?\n\Z")


def read_exact(stream: BinaryIO, length: int) -> bytes | None:
    """Read exactly ``length`` bytes from ``stream``, or return ``None`` on premature EOF."""
    if length == 0:
        return b""
    chunks: list[bytes] = []
    remaining = length
    while remaining > 0:
        chunk = stream.read(remaining)
        if not chunk:
            return None
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


def _reader_loop(
    stdout: BinaryIO,
    replies: queue.Queue[tuple[str, int | None, bytes]],
    max_body_bytes: int,
) -> None:
    while True:
        try:
            header = stdout.readline(64)
        except OSError:
            replies.put(("eof", None, b""))
            return
        if not header:
            replies.put(("eof", None, b""))
            return
        match = _HEADER_RE.fullmatch(header)
        if match is None:
            replies.put(("error", None, b""))
            return
        code, length = int(match[1]), int(match[2])
        if length > max_body_bytes:
            replies.put(("oversize", code, b""))
            return
        payload = read_exact(stdout, length)
        if payload is None:
            replies.put(("eof", None, b""))
            return
        replies.put(("ok", code, payload))


class IsolatedBatchWorker:
    """Maintain one persistent `-I` isolated subprocess with strict per-request timeouts."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._proc: subprocess.Popen[bytes] | None = None
        self._key: object = None
        self._replies: queue.Queue[tuple[str, int | None, bytes]] | None = None
        atexit.register(self.reset)

    def _close_locked(self, *, force: bool = False) -> None:
        proc = self._proc
        self._proc = None
        self._key = None
        self._replies = None
        if proc is None:
            return
        if force and proc.poll() is None:
            with contextlib.suppress(OSError):
                proc.kill()
        if proc.stdin is not None:
            with contextlib.suppress(OSError):
                proc.stdin.close()
        if not force and proc.poll() is None:
            with contextlib.suppress(OSError, subprocess.SubprocessError):
                proc.wait(timeout=2)
        if proc.poll() is None:
            with contextlib.suppress(OSError):
                proc.kill()
            with contextlib.suppress(OSError, subprocess.SubprocessError):
                proc.wait(timeout=2)
        if proc.stdout is not None:
            with contextlib.suppress(OSError):
                proc.stdout.close()

    def reset(self) -> None:
        """Terminate the active worker subprocess if one is running."""
        with self._lock:
            self._close_locked()

    def request(
        self,
        key: object,
        command: list[str],
        header: bytes,
        payload: bytes,
        *,
        timeout_seconds: float,
        max_body_bytes: int,
        timeout_exit: int | None = None,
    ) -> tuple[int, bytes]:
        """Send one length-framed request and return `(returncode, body)` under timeout."""
        with self._lock:
            for attempt in range(2):
                reused = self._proc is not None and self._proc.poll() is None and self._key == key
                if not reused:
                    self._close_locked()
                    fresh_proc = subprocess.Popen(
                        command,
                        stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.DEVNULL,
                    )
                    assert fresh_proc.stdin is not None and fresh_proc.stdout is not None  # noqa: S101
                    fresh_replies: queue.Queue[tuple[str, int | None, bytes]] = queue.Queue(maxsize=1)
                    thread = threading.Thread(
                        target=_reader_loop,
                        args=(fresh_proc.stdout, fresh_replies, max_body_bytes),
                        daemon=True,
                    )
                    thread.start()
                    self._proc = fresh_proc
                    self._key = key
                    self._replies = fresh_replies
                proc = self._proc
                replies = self._replies
                assert proc is not None and proc.stdin is not None and replies is not None  # noqa: S101
                try:
                    proc.stdin.write(header)
                    if payload:
                        proc.stdin.write(payload)
                    proc.stdin.flush()
                    kind, code, body = replies.get(timeout=timeout_seconds)
                except queue.Empty as error:
                    self._close_locked(force=True)
                    raise subprocess.TimeoutExpired(command, timeout_seconds) from error
                except OSError as error:
                    self._close_locked(force=True)
                    if reused and attempt == 0:
                        continue
                    raise ValueError("compiler worker failed or became unavailable") from error
                if kind == "ok":
                    assert code is not None  # noqa: S101
                    return code, body
                if kind == "eof":
                    exit_code: int | None = None
                    with contextlib.suppress(OSError, subprocess.SubprocessError):
                        exit_code = int(proc.wait(timeout=1))
                    self._close_locked(force=True)
                    if timeout_exit is not None and exit_code == timeout_exit:
                        raise subprocess.TimeoutExpired(command, timeout_seconds)
                    if reused and attempt == 0:
                        continue
                else:
                    self._close_locked(force=True)
                raise ValueError("compiler worker failed or exceeded its output bound")
            raise ValueError("compiler worker unavailable")


def decode_header_pair(line: bytes) -> tuple[int, str] | None:
    """Parse `<byte_length> <rest>\\n` emitted by worker clients."""
    text = line.decode("ascii", errors="strict") if line.isascii() else ""
    if not text.endswith("\n"):
        return None
    length_part, sep, tail = text[:-1].partition(" ")
    if not sep or not length_part.isdecimal():
        return None
    return int(length_part), tail


def write_batch_reply(stdout: BinaryIO, code: int, body: bytes) -> None:
    stdout.write(f"{code} {len(body)}\n".encode("ascii"))
    if body:
        stdout.write(body)
    stdout.flush()


def cast_str_list(value: object) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError("worker arguments must be a list of strings")
    return cast("list[str]", value)
