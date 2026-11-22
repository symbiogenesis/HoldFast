# SPDX-License-Identifier: Apache-2.0
"""Shared JSON encoding and decoder checks for the toolchain."""

import hashlib
import json
import math
from collections.abc import Callable


def canonical_bytes(value: object) -> bytes:
    """Encode compact, sorted ASCII JSON for byte bounds and content bindings."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True, allow_nan=False).encode("ascii")


def json_digest(value: object) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def unique_object[T](pairs: list[tuple[str, T]], *,
                     duplicate_error: Callable[[str], Exception] | None = None) -> dict[str, T]:
    """Keep member order and reject repeats, with the caller's diagnostic if supplied."""
    result: dict[str, T] = {}
    for key, value in pairs:
        if key in result:
            if duplicate_error is not None:
                raise duplicate_error(key)
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def finite_float(value: str) -> float:
    """Reject finite JSON spellings that overflow the host float representation."""
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"JSON number exceeds finite precision: {value}")
    return parsed


def exceeds_nesting(raw: bytes, limit: int) -> bool:
    """Check container depth before decoding. The JSON decoder validates syntax."""
    depth = 0
    quoted = escaped = False
    for byte in raw:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:  # backslash
                escaped = True
            elif byte == 34:  # double quote
                quoted = False
        elif byte == 34:
            quoted = True
        elif byte in b"[{":
            depth += 1
            if depth > limit:
                return True
        elif byte in b"]}":
            depth -= 1
    return False
