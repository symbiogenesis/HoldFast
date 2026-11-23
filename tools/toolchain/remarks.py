# SPDX-License-Identifier: Apache-2.0
"""LLVM YAML remarks from the pure compiler's required-static call specialization."""

import json
import re
from dataclasses import dataclass
from typing import Literal
from urllib.parse import quote

from toolchain import _Elaborator, _translate, parse_module
from toolchain.ast import MAX_SOURCE_BYTES, Name, Site, VelaError
from toolchain.hashing import sha256_bytes

MAX_DECISIONS = 256
MAX_REMARK_BYTES = 1_048_576
type Decision = Literal["Specialized", "SymbolicStaticArgument", "SpecializationRefused"]
_TAGS = {"Specialized": "Passed", "SymbolicStaticArgument": "Missed", "SpecializationRefused": "Failure"}


@dataclass(frozen=True)
class Export:
    yaml: bytes
    gallina: str | None
    error: VelaError | None


def _message(value: str) -> str:
    if "'" not in value:
        return f"'{value}'"
    if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9 _'();.,-]*", value):
        return value
    return f"'UTF-8 percent-encoded diagnostic: {quote(value, safe="")}'"


class Decisions:
    """Record the authored site and the active instantiation chain at each decision."""

    def __init__(self, filename: str) -> None:
        self.file = f"'{quote(filename, safe="")}'"
        self.function = ""
        self.expansions: list[Name] = []
        self.documents: list[str] = []
        self.size = 0

    def _location(self, site: Site) -> str:
        return f"{{ File: {self.file}, Line: {site.line}, Column: {site.column} }}"

    def record(self, decision: Decision, site: Site, callee: Name, reason: str, *, failed_at: Site | None = None) -> None:
        if len(self.documents) >= MAX_DECISIONS:
            raise ValueError(f"specialization remarks exceed {MAX_DECISIONS} decisions")
        lines = [f"--- !{_TAGS[decision]}", "Pass: vela-static-specialization", f"Name: {decision}",
                 f"DebugLoc: {self._location(site)}", f"Function: {self.function}", "Args:",
                 f"  - Callee: f_{callee.text}", f"    DebugLoc: {self._location(callee.site)}"]
        for origin in self.expansions:
            lines.extend((f"  - GeneratedFrom: f_{origin.text}", f"    DebugLoc: {self._location(origin.site)}"))
        lines.append(f"  - String: {_message(reason)}")
        if failed_at is not None:
            lines.append(f"    DebugLoc: {self._location(failed_at)}")
        record = "\n".join([*lines, "...", ""])
        self.size += len(record.encode("utf-8"))
        if self.size > MAX_REMARK_BYTES:
            raise ValueError("specialization remarks exceed the output byte budget")
        self.documents.append(record)

    def refused(self, site: Site, callee: Name, error: VelaError) -> None:
        self.record("SpecializationRefused", site, callee, error.message, failed_at=Site(error.line, error.column))


def compile_remarks(source: bytes, filename: str, producer: str) -> Export:
    if len(source) > MAX_SOURCE_BYTES:
        raise ValueError("remarks source exceeds the pure compiler byte budget")
    if (not filename or not filename.isprintable() or filename in {".", ".."} or "/" in filename or "\\" in filename
            or len(filename.encode("utf-8")) > 255):
        raise ValueError("remarks require a printable source basename within 255 UTF-8 bytes")
    if re.fullmatch(r"[0-9a-f]{64}", producer) is None:
        raise ValueError("remarks require a bound compiler identity")
    decisions = Decisions(filename)
    gallina: str | None = None
    error: VelaError | None = None
    try:
        gallina = _translate(source, parse_module(source), elaborator=_Elaborator(decisions=decisions)).gallina
    except VelaError as failure:
        error = failure
    binding = {
        "schema": 1, "source": filename, "source_sha256": sha256_bytes(source), "producer_sha256": producer,
        "target": "pure-rocq-gallina", "decision_count": len(decisions.documents),
        "outcome": "emitted" if error is None else "refused",
        "gallina_sha256": sha256_bytes(gallina.encode("ascii")) if gallina is not None else None,
        "diagnostic": None if error is None else {"kind": error.kind, "line": error.line,
                                                   "column": error.column, "message": error.message},
    }
    header = "# Vela remarks " + json.dumps(binding, sort_keys=True, separators=(",", ":")) + "\n"
    data = (header + "".join(decisions.documents)).encode("utf-8")
    if len(data) > MAX_REMARK_BYTES:
        raise ValueError("specialization remarks exceed the output byte budget")
    return Export(data, gallina, error)
