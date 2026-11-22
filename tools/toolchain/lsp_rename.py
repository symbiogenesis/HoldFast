# SPDX-License-Identifier: Apache-2.0
"""Propose local renames and recheck the edited source with the pure compiler."""

from bisect import bisect_right
from collections import defaultdict
from dataclasses import replace

from toolchain.ast import IDENTIFIER, KEYWORDS, UNSUPPORTED
from toolchain.lsp_services import (
    Inspection,
    InspectionError,
    Inspector,
    Occurrence,
    Position,
    lsp_range,
    validate_inspection,
)
from toolchain.source import SourceSnapshot


def valid_name(name: str) -> bool:
    """Accept the same identifier vocabulary as the pure compiler."""
    return IDENTIFIER.fullmatch(name) is not None and name not in KEYWORDS | UNSUPPORTED


def _selected(snapshot: SourceSnapshot, facts: Inspection | None, position: Position | None) -> Occurrence | None:
    if facts is None:
        return None
    if facts.snapshot != snapshot.identity:
        raise InspectionError("Rename facts differ from the current source")
    selected = facts.occurrence_at(position)
    # Public declarations and parameters need package-wide reference coverage.
    if selected is None or facts.symbols[selected.symbol].kind != "variable":
        return None
    return selected


def prepare(snapshot: SourceSnapshot, facts: Inspection | None, position: Position | None) -> object:
    """Offer only compiler-resolved local variables, using the selected occurrence."""
    selected = _selected(snapshot, facts, position)
    if selected is None or facts is None:
        return None
    return {"range": lsp_range(selected.start, selected.end),
            "placeholder": facts.symbols[selected.symbol].name}


def rename(snapshot: SourceSnapshot, facts: Inspection | None, position: Position | None,
           name: str, inspector: Inspector) -> object:
    """Recheck the edited source and every binding before publishing a versioned edit."""
    if not valid_name(name):
        raise ValueError("newName must be a supported pure identifier")
    selected = _selected(snapshot, facts, position)
    if selected is None or facts is None:
        return None
    old_name = facts.symbols[selected.symbol].name
    occurrences = tuple(item for item in facts.occurrences if item.symbol == selected.symbol)
    edits = []
    if name != old_name:
        edits = [{"range": lsp_range(item.start, item.end), "newText": name} for item in occurrences]
        source = bytearray(snapshot.source)
        replacement = name.encode("ascii")
        for item in reversed(occurrences):
            first = snapshot.position_byte_offset(*item.start)
            last = snapshot.position_byte_offset(*item.end)
            source[first:last] = replacement
        candidate = replace(snapshot, text=source.decode("utf-8"))
        checked = validate_inspection(candidate, inspector(candidate.source))
        if checked is None or len(checked.symbols) != len(facts.symbols):
            raise InspectionError("Renamed source did not preserve checked declarations")
        difference = len(name) - len(old_name)
        ends_by_line: defaultdict[int, list[int]] = defaultdict(list)
        for item in occurrences:
            line, column = item.end
            ends_by_line[line].append(column)

        def shifted(point: Position) -> Position:
            line, column = point
            return line, column + difference * bisect_right(ends_by_line[line], column)

        for identity, (before, after) in enumerate(zip(facts.symbols, checked.symbols, strict=True)):
            expected_name = name if identity == selected.symbol else before.name
            if (after.name != expected_name or after.kind != before.kind
                    or after.value_type != before.value_type or after.type_hint != before.type_hint
                    or after.documentation != before.documentation
                    or after.start != shifted(before.start) or after.end != shifted(before.end)):
                raise InspectionError("Rename changed a declaration or its type")
        if len(checked.occurrences) != len(facts.occurrences):
            raise InspectionError("Rename changed the resolved reference inventory")
        for before, after in zip(facts.occurrences, checked.occurrences, strict=True):
            if (after.symbol != before.symbol or after.declaration != before.declaration
                    or after.start != shifted(before.start) or after.end != shifted(before.end)):
                raise InspectionError("Rename captured or rebound a source occurrence")
    return {"documentChanges": [{"textDocument": {"uri": snapshot.uri, "version": snapshot.version},
                                 "edits": edits}]}
