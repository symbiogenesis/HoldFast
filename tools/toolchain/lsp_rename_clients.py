# SPDX-License-Identifier: Apache-2.0
"""Qualify versioned local rename application in Neovim and Emacs Eglot."""

import os
import subprocess
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path

from filelock import FileLock

from toolchain import lsp_clients as clients
from toolchain.hashing import file_sha256
from toolchain.protocol_json import decode_message

DISK = """// 😀 independent scopes
module Editor;
public Nat Keep(Nat seed) {
    let value = seed;
    return value;
}
public Nat Other(Nat value) => value;
"""
SOURCE = DISK + "// unsaved\n"
RENAMED = SOURCE.replace("let value", "let renamed").replace("return value;", "return renamed;")
EMACS = Path("/usr/bin/emacs-nox")
EGLOT = Path("/usr/share/emacs/30.2/lisp/progmodes/eglot.elc")
EMACS_PINS = {
    EMACS: "a9d9efb9c72a682034159aa53d90e1fe3ef9049f1dd25c82a4bee508bf694c24",
    EGLOT: "796f54ed251410639d115855243f520da0c6d46e93b2ea8700325724d0d01406",
    Path("/usr/share/emacs/30.2/etc/COPYING"):
        "3972dc9744f6499f0f9b2dbf76696f2ae7ad8af9b23dde66d6af86c9dfb36986",
    Path("/usr/share/doc/emacs-common/copyright"):
        "7c53ecb9593b0f5d607c01b54afec4c756e230b10141451c1c3536dbaff9ff18",
}

NEOVIM_SETUP = r"""
vim.cmd.edit(vim.fn.fnameescape(vim.env.HOLDFAST_FILE))
local buf = vim.api.nvim_get_current_buf()
vim.bo[buf].filetype = "holdfast"
local diagnostics = false
vim.api.nvim_create_autocmd("DiagnosticChanged", {buffer = buf, callback = function() diagnostics = true end})
local id = assert(vim.lsp.start({
  name = "holdfast", cmd = {vim.env.HOLDFAST_PY, vim.env.HOLDFAST_RUN, "holdfast-lsp", "--transcript", vim.env.HOLDFAST_WIRE},
  root_dir = vim.fn.getcwd(),
  capabilities = vim.tbl_deep_extend("force", vim.lsp.protocol.make_client_capabilities(), {
    workspace = {workspaceEdit = {documentChanges = true}},
  }),
}))
local client = assert(vim.lsp.get_client_by_id(id))
assert(vim.wait(15000, function() return client.initialized and diagnostics end))
local doc = {uri = vim.uri_from_bufnr(buf)}
local function contents()
  return table.concat(vim.api.nvim_buf_get_lines(buf, 0, -1, false), "\n") .. "\n"
end
vim.api.nvim_buf_set_lines(buf, -1, -1, false, {"// unsaved"})
"""

NEOVIM_SHUTDOWN = r"""
client:stop()
assert(vim.wait(15000, function() return client:is_stopped() end))
"""

NEOVIM = NEOVIM_SETUP + r"""
local function request(method, pos, new_name)
  local params = {textDocument = doc, position = pos, newName = new_name}
  local reply = assert(client:request_sync("textDocument/" .. method, params, 15000, buf))
  assert(not reply.err, vim.inspect(reply.err))
  return assert(reply.result)
end
local selected = {line = 3, character = 9}
local prepared = request("prepareRename", selected)
local preview = request("rename", selected, "renamed")
local function apply()
  vim.lsp.util.apply_workspace_edit(vim.deepcopy(preview), client.offset_encoding)
end
apply()
local fresh = contents()
local referred = {line = 4, character = 12}
local definition = request("definition", referred)
local stale_version = vim.lsp.util.buf_versions[buf]
apply()
local stale = contents()
local again = request("definition", referred)
local out = assert(io.open(vim.env.HOLDFAST_OBSERVATION, "wb"))
out:write(vim.json.encode({prepared=prepared, preview=preview, fresh=fresh, stale=stale,
  definition=definition, again=again, stale_version=stale_version}))
out:close()
""" + NEOVIM_SHUTDOWN

ELISP_SETUP = r"""
(require 'eglot)
(prefer-coding-system 'utf-8-unix)
(define-derived-mode holdfast-mode prog-mode "HoldFast")
(add-to-list 'auto-mode-alist '("\\.hf\\'" . holdfast-mode))
(add-to-list 'eglot-server-programs
             (cons 'holdfast-mode (list (getenv "HOLDFAST_PY") (getenv "HOLDFAST_RUN")
                                    "holdfast-lsp" "--transcript" (getenv "HOLDFAST_WIRE"))))
(setq eglot-sync-connect 15 eglot-confirm-server-edits nil
      make-backup-files nil auto-save-default nil)
(let ((coding-system-for-read 'utf-8-unix)) (find-file (getenv "HOLDFAST_FILE")))
(apply #'eglot--connect (eglot--guess-contact))
(let ((server (eglot-current-server)))
  (unless server (error "Buffer is unmanaged"))
  (goto-char (point-max))
  (insert "// unsaved\n")
  (eglot--signal-textDocument/didChange)
"""

ELISP_SHUTDOWN = r"""
  (eglot-shutdown server))
"""

ELISP = ELISP_SETUP + r"""
  (goto-char (point-min)) (forward-line 3) (forward-char 9)
  (let* ((selected (eglot--TextDocumentPositionParams))
         (prepared (jsonrpc-request server :textDocument/prepareRename selected))
         (preview (jsonrpc-request server :textDocument/rename (append selected '(:newName "renamed"))))
         (lookup (list :textDocument (eglot--TextDocumentIdentifier) :position '(:line 4 :character 12))))
    (eglot--apply-workspace-edit preview 'eglot-rename)
    (eglot--signal-textDocument/didChange)
    (let ((fresh (buffer-string))
          (definition (jsonrpc-request server :textDocument/definition lookup)))
      (condition-case err
          (progn (eglot--apply-workspace-edit preview 'eglot-rename)
                 (error "Eglot accepted stale workspace edit"))
        (jsonrpc-error
         (unless (string-match-p "require version" (format "%S" err)) (signal (car err) (cdr err)))))
      (eglot--signal-textDocument/didChange)
      (let ((coding-system-for-write 'utf-8-unix)
            (eglot-version eglot--versioned-identifier)
            (stale (buffer-string))
            (again (jsonrpc-request server :textDocument/definition lookup)))
        (with-temp-file (getenv "HOLDFAST_OBSERVATION")
          (insert (json-serialize (list :prepared prepared :preview preview :fresh fresh :stale stale
                                        :definition definition :again again
                                        :stale_version eglot-version)))))))
""" + ELISP_SHUTDOWN


def _range(line: int, start: int, end: int) -> dict[str, object]:
    return {"start": {"line": line, "character": start}, "end": {"line": line, "character": end}}


def verify_edit_session(
    wire: dict[str, object],
    observation: dict[str, object],
    uri: str,
    *,
    disk: str,
    edited: str,
    expected_sequence: list[str],
    check_server_caps: Callable[[dict[str, object]], None],
    check_preview: Callable[[object], None],
    handle_request: Callable[
        [str, object, dict[str, object], str, int, bool, list[str], dict[object, tuple[str, object]]],
        None,
    ],
    check_client_caps: Callable[[dict[str, object]], None] | None = None,
    incomplete_message: str = "incomplete edit sequence",
    changed_bytes_message: str = "fresh application or stale refusal changed unexpected bytes",
) -> None:
    """Reconstruct an editor overlay wire transcript and check oracle/observation agreement."""
    require, obj = clients._require, clients._object
    require(type(wire.get("exit_code")) is int and wire["exit_code"] == 0, "unclean editor exit")
    source, version = "", -1
    received: list[str] = []
    requests: dict[object, tuple[str, object]] = {}
    request_ids: set[object] = set()
    negotiated = False
    for index, raw in enumerate(clients._array(wire.get("frames"))):
        frame = obj(raw)
        message = obj(frame.get("message"))
        require(frame.get("index") == index and message.get("jsonrpc") == "2.0", "invalid wire frame")
        direction = frame.get("direction")
        method, identifier = message.get("method"), message.get("id")
        if direction == "server_to_client":
            if method is None and identifier in requests:
                key, expected = requests.pop(identifier)
                require("error" not in message, f"editor request failed: {key}")
                result = message.get("result")
                if key == "initialize":
                    check_server_caps(obj(obj(result).get("capabilities")))
                    negotiated = True
                else:
                    require(result == expected and observation.get(key) == result, f"{key} differs from the oracle")
                    if key == "preview":
                        check_preview(result)
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
            if check_client_caps is not None:
                check_client_caps(caps)
            requests[identifier] = ("initialize", None)
        elif method in ("textDocument/didOpen", "textDocument/didChange"):
            document = obj(params.get("textDocument"))
            next_version = document.get("version")
            if document.get("uri") != uri or type(next_version) is not int or next_version <= version:
                raise ValueError("unrelated or stale overlay")
            version = next_version
            if method == "textDocument/didOpen":
                require(document.get("text") == disk and source == "", "unexpected opening source")
                source = disk
            else:
                for change in clients._array(params.get("contentChanges")):
                    source = clients._wire_source_edit(source, obj(change))
        elif isinstance(method, str):
            handle_request(method, identifier, params, source, version, negotiated, received, requests)
    require(received == expected_sequence and not requests, incomplete_message)
    require(observation.get("fresh") == observation.get("stale") == source == edited, changed_bytes_message)


def verify_session(wire: dict[str, object], observation: dict[str, object], uri: str) -> None:
    """Reconstruct the overlay at each request and compare both editor and wire results."""
    require, obj = clients._require, clients._object
    doc = {"uri": uri}

    def _check_server_caps(caps: dict[str, object]) -> None:
        require(caps.get("renameProvider") == {"prepareProvider": True}, "rename unavailable")

    def _check_preview(result: object) -> None:
        change = obj(clients._array(obj(result)["documentChanges"])[0])
        require(type(obj(change["textDocument"])["version"]) is int, "invalid version in workspace edit")

    def _handle_request(
        method: str,
        identifier: object,
        params: dict[str, object],
        source: str,
        version: int,
        negotiated: bool,
        received: list[str],
        requests: dict[object, tuple[str, object]],
    ) -> None:
        if method not in ("textDocument/prepareRename", "textDocument/rename", "textDocument/definition"):
            return
        require(negotiated and obj(params.get("textDocument")) == doc, "wrong editor document")
        require(identifier is not None and identifier not in requests, "missing or reused request")
        if method == "textDocument/definition":
            require(source == RENAMED and received[-1:] in (["preview"], ["definition"]),
                    "lookup did not follow the applied rename")
            require(params.get("position") == {"line": 4, "character": 12}, "wrong renamed reference")
            require(type(observation.get("stale_version")) is int and observation["stale_version"] == version,
                    "stale application does not identify the newer version")
            key = "again" if "definition" in received else "definition"
            requests[identifier] = (key, {"uri": uri, "range": _range(3, 8, 15)})
            return
        require(source == SOURCE and version > 0, "rename used wrong source or version")
        require(params.get("position") == {"line": 3, "character": 9}, "wrong rename selection")
        if method == "textDocument/prepareRename":
            requests[identifier] = ("prepared", {"range": _range(3, 8, 13), "placeholder": "value"})
            return
        require(params.get("newName") == "renamed", "wrong rename target")
        requests[identifier] = ("preview", {"documentChanges": [{
            "textDocument": {"uri": uri, "version": version},
            "edits": [{"range": span, "newText": "renamed"} for span in (_range(3, 8, 13), _range(4, 11, 16))],
        }]})

    verify_edit_session(
        wire,
        observation,
        uri,
        disk=DISK,
        edited=RENAMED,
        expected_sequence=["initialize", "prepared", "preview", "definition", "again"],
        check_server_caps=_check_server_caps,
        check_preview=_check_preview,
        handle_request=_handle_request,
        incomplete_message="incomplete rename sequence",
        changed_bytes_message="fresh application or stale refusal changed unexpected bytes",
    )


def _session(folder: Path, command: list[str], script: str, filename: str, disk: str,
             verify: Callable[[dict[str, object], dict[str, object], str], None]) -> dict[str, object]:
    folder.mkdir()
    target, wire, observation = (folder / name for name in ("editor.hf", "wire.json", "observation.json"))
    target.write_bytes(disk.encode())
    harness = folder / filename
    harness.write_bytes(script.encode())
    env = {**os.environ, "HOLDFAST_FILE": str(target), "HOLDFAST_WIRE": str(wire),
           "HOLDFAST_OBSERVATION": str(observation), "HOLDFAST_PY": sys.executable,
           "HOLDFAST_RUN": str(Path(__file__).resolve().parents[1] / "run.py")}
    done = subprocess.run([*command, str(harness)], cwd=folder, env=env, capture_output=True,
                          encoding="utf-8", errors="replace", timeout=90, check=False)
    clients._require(done.returncode == 0,
                     f"{filename} exited {done.returncode}: {done.stderr[-1500:]} {done.stdout[:1800]}")
    clients._require(target.read_bytes() == disk.encode(), "editor wrote the unsaved edit to disk")
    wire_data, observed = (decode_message(path.read_bytes()) for path in (wire, observation))
    verify(wire_data, observed, target.as_uri())
    return {"wire": wire_data, "observation": observed, "uri": target.as_uri()}


def qualify() -> dict[str, object]:
    """Run both independently pinned editors against the same source through stdio."""
    return qualify_versioned_edits("--qualify-rename", "pure-local-rename-application", DISK, NEOVIM, ELISP,
                                   verify_session)


def qualify_versioned_edits(command: str, scope: str, disk: str, neovim: str, elisp: str,
                            verify: Callable[[dict[str, object], dict[str, object], str], None]) -> dict[str, object]:
    if sys.platform == "win32":
        result = subprocess.run(["wsl", "-u", "root", "-e", "python3", "tools/run.py", "holdfast-lsp", command],
                                cwd=Path(__file__).resolve().parents[2], capture_output=True,
                                timeout=420, check=False)
        if result.returncode:
            raise ValueError(result.stderr.decode("utf-8", errors="replace")[-3000:])
        return decode_message(result.stdout)
    if sys.platform != "linux" or clients._platform_key()[1] != "aarch64":
        raise ValueError("the Emacs versioned-edit client requires Ubuntu 26.04 ARM64")
    for path, expected in EMACS_PINS.items():
        clients._require(file_sha256(path) == expected, f"unexpected Emacs qualification file: {path}")
    cache = clients._default_cache_root()
    cache.mkdir(parents=True, exist_ok=True)
    with (FileLock(cache / "clients.lock", timeout=clients.TIMEOUT_SECONDS),
          tempfile.TemporaryDirectory(prefix="holdfast-versioned-edit-") as temp):
        root = Path(temp)
        executable, nvim_pin = clients._stage_neovim(cache / "downloads", root)
        emacs = _session(root / "eglot", [str(EMACS), "--batch", "-Q", "-l", str(EGLOT), "-l"],
                         elisp, "probe.el", disk, verify)
        nvim = _session(root / "vim-lsp", [str(executable), "--headless", "-u", "NONE", "-i", "NONE", "-n", "-l"],
                        neovim, "probe.lua", disk, verify)
        return {"schema": 1, "scope": scope, "status": "passed",
                "clients": {"neovim": nvim_pin, "emacs_eglot": {str(p): sha for p, sha in EMACS_PINS.items()}},
                "sessions": {"neovim": nvim, "emacs_eglot": emacs}}
