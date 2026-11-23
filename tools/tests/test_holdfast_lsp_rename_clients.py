# SPDX-License-Identifier: Apache-2.0
"""Check applied-rename evidence and nearby failures independently of either editor."""

from tests.harness import Case
from toolchain import lsp_rename_clients as rename

INDEPENDENT_CASES = True
URI = "file:///workspace/editor.hf"


def _probe(fault: str = "") -> None:
    frames: list[dict[str, object]] = []

    def send(direction: str, message: dict[str, object]) -> None:
        frames.append({"direction": direction, "index": len(frames), "message": {"jsonrpc": "2.0", **message}})

    def exchange(number: int, method: str, params: dict[str, object], result: object) -> None:
        send("client_to_server", {"method": method, "params": params, "id": number})
        send("server_to_client", {"id": number, "result": result})

    doc = {"uri": URI}
    exchange(0, "initialize", {"capabilities": {"workspace": {"workspaceEdit": {
        "documentChanges": fault != "unversioned"}}}}, {"capabilities": {"renameProvider": {"prepareProvider": True}}})
    send("client_to_server", {"method": "textDocument/didOpen",
                              "params": {"textDocument": {**doc, "version": 0, "text": rename.DISK}}})

    def changed(version: int, source: str) -> None:
        send("client_to_server", {"method": "textDocument/didChange", "params": {
            "textDocument": {**doc, "version": version}, "contentChanges": [{"text": source}]}})

    changed(2, rename.SOURCE)
    selected: dict[str, object] = {"textDocument": doc, "position": {"line": 3, "character": 9}}
    span = {"start": {"line": 3, "character": 8}, "end": {"line": 3, "character": 13}}
    use = {"start": {"line": 4, "character": 11}, "end": {"line": 4, "character": 16}}
    prepared = {"range": span, "placeholder": "value"}
    exchange(1, "textDocument/prepareRename", selected, prepared)
    preview = {"documentChanges": [{"textDocument": {"uri": URI, "version": 1 if fault == "stale" else 2},
                                    "edits": [{"range": s, "newText": "renamed"} for s in (span, use)]}]}
    exchange(1 if fault == "duplicate" else 2, "textDocument/rename", {**selected, "newName": "renamed"}, preview)
    changed(4, rename.RENAMED.replace("Other(Nat value)", "Other(Nat renamed)") if fault == "capture" else rename.RENAMED)
    lookup: dict[str, object] = {"textDocument": doc, "position": {"line": 4, "character": 12}}
    result = {**doc, "range": {"start": {"line": 3, "character": 8}, "end": {"line": 3, "character": 15}}}
    exchange(3, "textDocument/definition", lookup, result)
    if fault != "missing-replay":
        exchange(4, "textDocument/definition", lookup, result if fault != "wrong-definition" else None)
    observation: dict[str, object] = {
        "prepared": prepared, "preview": preview, "fresh": rename.RENAMED,
        "stale": rename.DISK if fault == "applied-twice" else rename.RENAMED,
        "stale_version": 2 if fault == "wrong-version" else 4, "definition": result, "again": result}
    if fault == "detached":
        observation["preview"] = {}
    rename.verify_session({"frames": frames, "exit_code": 0}, observation, URI)


def _refusals() -> None:
    for fault in ("unversioned", "stale", "duplicate", "capture", "missing-replay", "wrong-definition",
                  "applied-twice", "wrong-version", "detached"):
        try:
            _probe(fault)
        except ValueError:
            continue
        raise AssertionError(f"accepted rename qualification with {fault}")


def cases() -> list[Case]:
    return [Case("applied-rename-joins-both-editor-and-wire-evidence", _probe),
            Case("reject-detached-stale-and-incomplete-rename-evidence", _refusals)]
