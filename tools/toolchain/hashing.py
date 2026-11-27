# SPDX-License-Identifier: Apache-2.0
"""Content identities for in-memory bytes and files on disk."""

import hashlib
import os
import stat
import threading
import time
from pathlib import Path
from typing import Protocol

RACILY_CLEAN_NS = 2_000_000_000
_MAX_CACHE_ENTRIES = 8192
_CACHE_LOCK = threading.Lock()
_FILE_DIGEST_CACHE: dict[tuple[str, int, int, int, int, int], str] = {}


class _ReadableBytes(Protocol):
    def read(self, size: int = ..., /) -> bytes: ...


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_bounded(stream: _ReadableBytes, limit: int, *, chunk_size: int = 65_536) -> bytes:
    """Read up to ``limit + 1`` bytes in bounded chunks to avoid huge read allocations."""
    chunks: list[bytes] = []
    total = 0
    while total <= limit:
        chunk = stream.read(min(chunk_size, limit - total + 1))
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
    return b"".join(chunks)


def is_racily_clean(info: os.stat_result, now_ns: int) -> bool:
    """Return True only when a regular file's timestamps are strictly older than the racy window."""
    latest = max(info.st_mtime_ns, info.st_ctime_ns)
    return stat.S_ISREG(info.st_mode) and now_ns - latest >= RACILY_CLEAN_NS


def _cache_key(path: Path, info: os.stat_result) -> tuple[str, int, int, int, int, int]:
    return (str(path), info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def cached_file_digest(path: Path) -> tuple[str, int] | None:
    """Return ``(digest, size)`` if ``path`` is a racily-clean cache hit, else ``None``."""
    info = path.stat()
    if not is_racily_clean(info, time.time_ns()):
        return None
    key = _cache_key(path, info)
    with _CACHE_LOCK:
        digest = _FILE_DIGEST_CACHE.get(key)
    return None if digest is None else (digest, info.st_size)


def store_file_digest(path: Path, info: os.stat_result, digest: str) -> None:
    """Record ``digest`` when ``info`` represents an uncorrupted racily-clean regular file."""
    if not is_racily_clean(info, time.time_ns()):
        return
    key = _cache_key(path, info)
    with _CACHE_LOCK:
        if len(_FILE_DIGEST_CACHE) >= _MAX_CACHE_ENTRIES:
            _FILE_DIGEST_CACHE.clear()
        _FILE_DIGEST_CACHE[key] = digest


def file_sha256(path: Path) -> str:
    before = path.stat()
    if is_racily_clean(before, time.time_ns()):
        key = _cache_key(path, before)
        with _CACHE_LOCK:
            cached = _FILE_DIGEST_CACHE.get(key)
        if cached is not None:
            return cached
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    after = path.stat()
    if os.path.samestat(before, after) and (before.st_size, before.st_mtime_ns, before.st_ctime_ns) == (
            after.st_size, after.st_mtime_ns, after.st_ctime_ns):
        store_file_digest(path, after, digest)
    return digest
