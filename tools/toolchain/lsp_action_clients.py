# SPDX-License-Identifier: Apache-2.0
"""Qualify checked comparison edits in Neovim and Emacs Eglot."""

from toolchain import lsp_clients as clients
from toolchain.lsp_rename_clients import (
    ELISP_SETUP,
    ELISP_SHUTDOWN,
    NEOVIM_SETUP,
    NEOVIM_SHUTDOWN,
    _range,
    qualify_versioned_edits,
)

DISK = "// 😀 retain == in comments\nmodule Editor;\npublic bool Check(bool keep) => keep == false;\n"
SOURCE = DISK + "// unsaved\n"
EDITED = SOURCE.replace("keep == false", "!(keep)")
KIND = "refactor.rewrite"
METHOD = "textDocument/codeAction"

NEOVIM = NEOVIM_SETUP + r"""
local point = {line = 2, character = 37}
local function actions()
  local params = {textDocument = doc, range = {start = point, ["end"] = point},
    context = {diagnostics = {}, only = {"refactor.rewrite"}}}
  local reply = assert(client:request_sync("textDocument/codeAction", params, 15000, buf))
  assert(not reply.err, vim.inspect(reply.err))
  return assert(reply.result)
end
local preview = actions()
local function apply()
  vim.lsp.util.apply_workspace_edit(vim.deepcopy(preview[1].edit), client.offset_encoding)
end
apply()
local fresh = contents()
local after = actions()
local stale_version = vim.lsp.util.buf_versions[buf]
apply()
local stale = contents()
local again = actions()
local out = assert(io.open(vim.env.HOLDFAST_OBSERVATION, "wb"))
out:write(vim.json.encode({preview=preview, fresh=fresh, stale=stale, after=after,
  again=again, stale_version=stale_version}))
out:close()
""" + NEOVIM_SHUTDOWN

ELISP = ELISP_SETUP + r"""
  (let* ((point '(:line 2 :character 37))
         (params (list :textDocument (eglot--TextDocumentIdentifier)
                       :range (list :start point :end point)
                       :context '(:diagnostics [] :only ["refactor.rewrite"])))
         (preview (jsonrpc-request server :textDocument/codeAction params))
         (edit (plist-get (aref preview 0) :edit)))
    (eglot--apply-workspace-edit edit 'eglot-code-action-rewrite)
    (eglot--signal-textDocument/didChange)
    (let ((fresh (buffer-string))
          (after (jsonrpc-request server :textDocument/codeAction params)))
      (condition-case err
          (progn (eglot--apply-workspace-edit edit 'eglot-code-action-rewrite)
                 (error "Eglot accepted stale workspace edit"))
        (jsonrpc-error
         (unless (string-match-p "require version" (format "%S" err)) (signal (car err) (cdr err)))))
      (eglot--signal-textDocument/didChange)
      (let ((coding-system-for-write 'utf-8-unix)
            (eglot-version eglot--versioned-identifier)
            (stale (buffer-string))
            (again (jsonrpc-request server :textDocument/codeAction params)))
        (with-temp-file (getenv "HOLDFAST_OBSERVATION")
          (insert (json-serialize (list :preview preview :fresh fresh :stale stale :after after
                                        :again again :stale_version eglot-version)))))))
""" + ELISP_SHUTDOWN


def verify_session(wire: dict[str, object], observation: dict[str, object], uri: str) -> None:
    """Reconstruct the action's unsaved input and both post-application queries."""
    require, obj = clients._require, clients._object
    require(type(wire.get("exit_code")) is int and wire["exit_code"] == 0, "unclean editor exit")
    expected_sequence = ["initialize", "preview", "after", "again"]
    received: list[str] = []
    pending: dict[object, tuple[str, object]] = {}
    request_ids: set[object] = set()
    source, version, preview_version = "", -1, -1
    doc = {"uri": uri}
    for index, raw in enumerate(clients._array(wire.get("frames"))):
        frame = obj(raw)
        message = obj(frame.get("message"))
        require(frame.get("index") == index and message.get("jsonrpc") == "2.0", "invalid wire frame")
        direction = frame.get("direction")
        method, identifier = message.get("method"), message.get("id")
        if direction == "server_to_client":
            if method is None and identifier in pending:
                key, expected = pending.pop(identifier)
                require("error" not in message, f"editor request failed: {key}")
                result = message.get("result")
                if key == "initialize":
                    caps = obj(obj(result).get("capabilities"))
                    require(caps.get("codeActionProvider") == {"codeActionKinds": [KIND]}, "rewrite unavailable")
                else:
                    require(result == expected and observation.get(key) == result, f"{key} differs from the oracle")
                    if key == "preview":
                        action = obj(clients._array(result)[0])
                        change = obj(clients._array(obj(action["edit"])["documentChanges"])[0])
                        require(type(obj(change["textDocument"])["version"]) is int, "invalid workspace edit version")
                received.append(key)
            continue
        require(direction == "client_to_server", "invalid wire direction")
        if method is not None and identifier is not None:
            require(type(identifier) in (int, str) and identifier not in request_ids, "invalid or reused request id")
            request_ids.add(identifier)
        params = obj(message.get("params") or {})
        if method == "initialize":
            caps = obj(params.get("capabilities"))
            require(obj(obj(caps.get("workspace")).get("workspaceEdit")).get("documentChanges") is True,
                    "client lacks versioned edits")
            actions = obj(obj(caps.get("textDocument")).get("codeAction"))
            literal = obj(actions.get("codeActionLiteralSupport"))
            kinds = obj(literal.get("codeActionKind")).get("valueSet")
            require(KIND in clients._array(kinds), "client lacks literal rewrite actions")
            pending[identifier] = ("initialize", None)
        elif method in ("textDocument/didOpen", "textDocument/didChange"):
            updated = obj(params.get("textDocument"))
            next_version = updated.get("version")
            if updated.get("uri") != uri or type(next_version) is not int or next_version <= version:
                raise ValueError("unrelated or stale overlay")
            version = next_version
            if method == "textDocument/didOpen":
                require(updated.get("text") == DISK and source == "", "unexpected opening source")
                source = DISK
            else:
                for change in clients._array(params.get("contentChanges")):
                    source = clients._wire_source_edit(source, obj(change))
        elif method == METHOD:
            require(identifier is not None and not pending and 1 <= len(received) < len(expected_sequence),
                    "unsolicited rewrite request")
            require(params == {"textDocument": doc, "range": _range(2, 37, 37),
                               "context": {"diagnostics": [], "only": [KIND]}}, "wrong rewrite selection")
            key = expected_sequence[len(received)]
            if key == "preview":
                require(source == SOURCE and version > 0, "rewrite used the wrong overlay")
                preview_version = version
                expected = [{"title": "Simplify Boolean comparison (HOLDFAST103)", "kind": KIND,
                             "edit": {"documentChanges": [{"textDocument": {**doc, "version": version},
                                                           "edits": [{"range": _range(2, 32, 45),
                                                                      "newText": "!(keep)"}]}]}}]
            else:
                stale_version = observation.get("stale_version")
                require(source == EDITED and type(stale_version) is int and version == stale_version > preview_version,
                        "stale replay does not identify the changed overlay")
                expected = []
            pending[identifier] = (key, expected)
    require(received == expected_sequence and not pending, "incomplete rewrite sequence")
    require(observation.get("fresh") == observation.get("stale") == source == EDITED,
            "fresh application or stale replay changed unexpected bytes")


def qualify() -> dict[str, object]:
    return qualify_versioned_edits("--qualify-actions", "pure-comparison-action-application",
                                   DISK, NEOVIM, ELISP, verify_session)
