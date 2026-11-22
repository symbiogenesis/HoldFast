# SPDX-License-Identifier: Apache-2.0
"""Immutable diagnostic source identities and explicit source coordinate units."""

import hashlib
import json
import re
from bisect import bisect_right
from dataclasses import dataclass
from functools import cached_property

from toolchain.ast import MAX_SOURCE_BYTES

MAX_URI_BYTES = 4096


def _normalized(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")


def _utf16_length(text: str) -> int:
    return len(text.encode("utf-16-le")) // 2


@dataclass(frozen=True)
class SourceSnapshot:
    uri: str
    version: int
    text: str
    generation: int

    def __post_init__(self) -> None:
        if not self.uri or len(self.uri.encode("utf-8")) > MAX_URI_BYTES:
            raise ValueError("document URI is empty or exceeds limit")
        if len(self.source) > MAX_SOURCE_BYTES:
            raise ValueError("document exceeds pure prototype source limit")
        if (type(self.version) is not int or not -(2 ** 31) <= self.version < 2 ** 31
                or type(self.generation) is not int or self.generation < 1):
            raise ValueError("invalid document version or generation")

    @cached_property
    def source(self) -> bytes:
        return self.text.encode("utf-8")

    @cached_property
    def identity(self) -> str:
        fields = [self.uri, self.version, self.generation, self.text]
        return hashlib.sha256(json.dumps(fields, ensure_ascii=False).encode("utf-8")).hexdigest()

    @cached_property
    def _line_starts(self) -> tuple[int, ...]:
        """UTF-8 offsets of lines delimited by CRLF, CR or LF, including the final empty line."""
        return (0, *(match.end() for match in re.finditer(rb"\r\n|[\r\n]", self.source)))

    @cached_property
    def _diagnostic_lines(self) -> tuple[str, ...]:
        return tuple(_normalized(self.text).split("\n"))

    def byte_position(self, offset: int) -> dict[str, int]:
        """Convert a UTF-8 boundary to LSP UTF-16, never an interior byte/CRLF."""
        source = self.source
        if type(offset) is not int or not 0 <= offset <= len(source):
            raise ValueError("source byte offset out of bounds")
        if offset and source[offset - 1:offset + 1] == b"\r\n":
            raise ValueError("source byte offset splits CRLF")
        line = bisect_right(self._line_starts, offset) - 1
        prefix = source[self._line_starts[line]:offset].decode("utf-8")
        return {"line": line, "character": _utf16_length(prefix)}

    def position_byte_offset(self, line: int, character: int) -> int:
        """Convert an LSP UTF-16 position to UTF-8, clamping past line end."""
        if any(type(value) is not int or not 0 <= value < 2 ** 31
               for value in (line, character)):
            raise ValueError("source position requires unsigned 31-bit coordinates")
        if line >= len(self._line_starts):
            raise ValueError("source position line out of bounds")
        encoded = self._diagnostic_lines[line].encode("utf-16-le")
        column = min(character, len(encoded) // 2)
        try:
            prefix = encoded[:column * 2].decode("utf-16-le")
        except UnicodeDecodeError as error:
            raise ValueError("source position splits a supplementary character") from error
        return self._line_starts[line] + len(prefix.encode("utf-8"))

    def diagnostic_position(self, line: int, column: int) -> dict[str, int]:
        """Adapt the legacy producer's one-based normalized code-point site."""
        lines = self._diagnostic_lines
        if not 1 <= line <= len(lines) or not 1 <= column <= len(lines[line - 1]) + 1:
            raise ValueError("producer diagnostic outside source")
        return {"line": line - 1, "character": _utf16_length(lines[line - 1][:column - 1])}
