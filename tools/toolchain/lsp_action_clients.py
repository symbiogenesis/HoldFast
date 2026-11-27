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
    verify_edit_session,
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
    expected_sequence = ["initialize", "preview", "after", "again"]
    doc = {"uri": uri}
    preview_version = -1

    def _check_client_caps(caps: dict[str, object]) -> None:
        actions = obj(obj(caps.get("textDocument")).get("codeAction"))
        literal = obj(actions.get("codeActionLiteralSupport"))
        kinds = obj(literal.get("codeActionKind")).get("valueSet")
        require(KIND in clients._array(kinds), "client lacks literal rewrite actions")

    def _check_server_caps(caps: dict[str, object]) -> None:
        require(caps.get("codeActionProvider") == {"codeActionKinds": [KIND]}, "rewrite unavailable")

    def _check_preview(result: object) -> None:
        action = obj(clients._array(result)[0])
        change = obj(clients._array(obj(action["edit"])["documentChanges"])[0])
        require(type(obj(change["textDocument"])["version"]) is int, "invalid workspace edit version")

    def _handle_request(
        method: str,
        identifier: object,
        params: dict[str, object],
        source: str,
        version: int,
        _negotiated: bool,
        received: list[str],
        pending: dict[object, tuple[str, object]],
    ) -> None:
        nonlocal preview_version
        if method != METHOD:
            return
        require(identifier is not None and not pending and 1 <= len(received) < len(expected_sequence),
                "unsolicited rewrite request")
        require(params == {"textDocument": doc, "range": _range(2, 37, 37),
                           "context": {"diagnostics": [], "only": [KIND]}}, "wrong rewrite selection")
        key = expected_sequence[len(received)]
        if key == "preview":
            require(source == SOURCE and version > 0, "rewrite used the wrong overlay")
            preview_version = version
            expected: object = [{"title": "Simplify Boolean comparison (HOLDFAST103)", "kind": KIND,
                                 "edit": {"documentChanges": [{"textDocument": {**doc, "version": version},
                                                               "edits": [{"range": _range(2, 32, 45),
                                                                          "newText": "!(keep)"}]}]}}]
        else:
            stale_version = observation.get("stale_version")
            require(source == EDITED and type(stale_version) is int and version == stale_version > preview_version,
                    "stale replay does not identify the changed overlay")
            expected = []
        pending[identifier] = (key, expected)

    verify_edit_session(
        wire,
        observation,
        uri,
        disk=DISK,
        edited=EDITED,
        expected_sequence=expected_sequence,
        check_client_caps=_check_client_caps,
        check_server_caps=_check_server_caps,
        check_preview=_check_preview,
        handle_request=_handle_request,
        incomplete_message="incomplete rewrite sequence",
        changed_bytes_message="fresh application or stale replay changed unexpected bytes",
    )


def qualify() -> dict[str, object]:
    return qualify_versioned_edits("--qualify-actions", "pure-comparison-action-application",
                                   DISK, NEOVIM, ELISP, verify_session)
