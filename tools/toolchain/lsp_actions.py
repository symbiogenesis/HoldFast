# SPDX-License-Identifier: Apache-2.0
"""Project the pure compiler's checked Boolean comparison edit into an LSP action."""

import hashlib
from typing import cast

from toolchain.inspection import producer_identity
from toolchain.lsp_services import InspectionError, QueryRange
from toolchain.lsp_worker import run_worker
from toolchain.protocol_json import decode_message
from toolchain.source import SourceSnapshot

METHOD = "textDocument/codeAction"
KIND = "refactor.rewrite"


def supports(kinds: object) -> bool:
    if not isinstance(kinds, list) or not all(isinstance(kind, str) for kind in kinds):
        raise ValueError("expected a list of code action kinds")
    return any(kind in {"", "refactor", KIND} for kind in kinds)


def actions(snapshot: SourceSnapshot, selection: QueryRange) -> list[dict[str, object]]:
    first, last = (snapshot.position_byte_offset(*point) for point in selection)
    source = snapshot.source
    try:
        result = decode_message(run_worker(source, "--comparison-action", str(first), str(last)))
        if (result.pop("source_sha256") != hashlib.sha256(source).hexdigest()
                or result.pop("selection") != [first, last]):
            raise InspectionError("Comparison preview differs from the selected source")
        if result == {"edit": None}:
            return []
        if set(result) != {"producer", "edit"} or result["producer"] != producer_identity()["version"]:
            raise InspectionError("Stale comparison preview producer")
        edit = result["edit"]
        if not isinstance(edit, dict) or set(edit) != {"span", "replacement", "candidate_sha256"}:
            raise InspectionError("Invalid comparison preview edit")
        span, replacement = edit["span"], edit["replacement"]
        if (not isinstance(span, list) or len(span) != 2 or any(type(offset) is not int for offset in span)
                or not isinstance(replacement, str)):
            raise InspectionError("Invalid comparison preview span or text")
        begin, end = cast("list[int]", span)
        if not (0 <= begin < end <= len(source) and first < end and begin < max(last, first + 1)):
            raise InspectionError("Comparison preview edit misses the requested range")
        updated = source[:begin] + replacement.encode("utf-8") + source[end:]
        if hashlib.sha256(updated).hexdigest() != edit["candidate_sha256"]:
            raise InspectionError("Comparison preview differs from the checked candidate")
        location = {"start": snapshot.byte_position(begin), "end": snapshot.byte_position(end)}
    except (KeyError, ValueError, TypeError) as error:
        raise InspectionError("Invalid source-bound comparison action") from error
    return [{"title": "Simplify Boolean comparison (VELA103)", "kind": KIND,
             "edit": {"documentChanges": [{"textDocument": {"uri": snapshot.uri, "version": snapshot.version},
                                           "edits": [{"range": location, "newText": replacement}]}]}}]
