# SPDX-License-Identifier: Apache-2.0
"""Loopback-only HTTP transport for HoldFast's bounded development playground."""

import hashlib
import hmac
import os
import re
import secrets
import shutil
import socket
import subprocess
import sys
import threading
import time
from contextlib import suppress
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import cast, override

from toolchain import proofenv
from toolchain._isolated_worker import IsolatedBatchWorker
from toolchain.ast import IDENTIFIER, MAX_SOURCE_BYTES
from toolchain.authoring import (
    LINT_CODES,
    MATHEMATICAL_LINT_CODES,
    OPT_IN_MATHEMATICAL_LINTS,
    is_pascal_case,
)
from toolchain.elaborate import FRONTEND_SOURCES
from toolchain.elaborate_holes import MAX_GOAL_BYTES, MAX_HOLES
from toolchain.graded_source import SUPPORT_FILES
from toolchain.hashing import file_sha256
from toolchain.lsp import Server
from toolchain.parser import bytecode_interpreter
from toolchain.playground_worker import TIMEOUT_EXIT, require_parser
from toolchain.protocol_json import MAX_BODY_BYTES, decode_message, encode_body
from toolchain.source import SourceSnapshot

MAX_SESSIONS = 8
SESSION_SECONDS = 1800
READ_SECONDS = 10
WORKER_SECONDS = 5
MAX_AUTHORING_FINDINGS = 8192
_SUBPROCESS_RUN = subprocess.run
_BATCH_WORKER = IsolatedBatchWorker()
ASSETS = {"/": ("index.html", "text/html; charset=utf-8"),
          "/index.html": ("index.html", "text/html; charset=utf-8"),
          "/app.mjs": ("app.mjs", "text/javascript; charset=utf-8"),
          "/style.css": ("style.css", "text/css; charset=utf-8")}


def _validate_result(response: dict[str, object], request: dict[str, object], digest: str) -> None:
    if response.get("sourceHash") != digest or type(response.get("ok")) is not bool:
        raise ValueError("compiler worker returned an invalid source identity")
    compilation = request["action"] == "compile"
    if compilation and type(response.get("editorServices")) is not bool:
        raise ValueError("compiler worker returned invalid editor-service availability")
    if response["ok"]:
        if request["action"] == "authoring":
            _validate_authoring(response, cast("str", request["source"]))
            return
        fields = {"ok", "sourceHash", "module", "gallina", "findings", "editorServices"} if compilation else {
            "ok", "sourceHash", "valueType", "value"}
        if (set(response) != fields
                or not all(isinstance(response[key], str) for key in fields - {"ok", "findings", "editorServices"})):
            raise ValueError("compiler worker returned an invalid result")
        if compilation:
            if response["editorServices"] and response["findings"] != []:
                raise ValueError("pure editor tools do not support generic declarations")
            _validate_findings(response["findings"], cast("str", request["source"]), mathematical=True)
        if request["action"] == "evaluate":
            value = cast("str", response["value"])
            if (response["valueType"] != request["valueType"]
                    or (request["valueType"] == "bool" and value not in {"true", "false"})
                    or (request["valueType"] == "Nat" and (not value.isascii() or not value.isdecimal()))):
                raise ValueError("compiler worker returned an invalid typed value")
    else:
        error = response.get("error")
        kinds = {"syntax", "name", "type", "unsupported", "limit", "encoding"}
        if request["action"] != "authoring" and (not compilation or not response["editorServices"]):
            kinds.update({"protocol", "inference", "grade"})
        if request["action"] == "authoring":
            kinds.update({"inspection-limit", "lint-preview", "format"})
        fields = {"ok", "sourceHash", "error"} | ({"editorServices"} if compilation else set())
        if "goals" in response and compilation and response["editorServices"] is False:
            _validate_goals(response["goals"], cast("str", request["source"]))
            kinds.add("open-goals")
            fields.add("goals")
        if "assertionGoal" in response and compilation and response["editorServices"] is False:
            fields.add("assertionGoal")
        if (set(response) != fields or not isinstance(error, dict)
                or set(error) != {"kind", "message", "line", "column"}
                or not isinstance(error["kind"], str)
                or error["kind"] not in kinds
                or not isinstance(error["message"], str)
                or type(error["line"]) is not int or type(error["column"]) is not int
                or error["line"] < 1 or error["column"] < 1):
            raise ValueError("compiler worker returned an invalid refusal")
        if "assertionGoal" in fields:
            _validate_assertion_goal(response["assertionGoal"], error, cast("str", request["source"]))


def _validate_assertion_goal(goal: object, error: dict[str, object], source: str) -> None:
    if (not isinstance(goal, dict) or set(goal) != {"status", "expected", "context"}
            or goal["status"] != "unresolved" or error["kind"] not in {"type", "limit"}
            or not isinstance(goal["expected"], str) or not goal["expected"]
            or not isinstance(goal["context"], str) or not goal["context"]
            or len(goal["expected"].encode()) + len(goal["context"].encode()) > MAX_GOAL_BYTES):
        raise ValueError("invalid pending assertion diagnostic")
    lines = source.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    line, column = cast("int", error["line"]), cast("int", error["column"])
    if not 1 <= line <= len(lines):
        raise ValueError("invalid pending assertion location")
    text = lines[line - 1]
    if (re.match(r"assert(?![A-Za-z_0-9])", text[column - 1:]) is None
            or (column > 1 and re.fullmatch(r"[A-Za-z_0-9]", text[column - 2]))):
        raise ValueError("pending assertion diagnostic differs from source")


def _validate_goals(goals: object, source: str) -> None:
    if not isinstance(goals, list) or not 1 <= len(goals) <= MAX_HOLES:
        raise ValueError("invalid named-hole inventory")
    lines = source.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    previous = (0, 0)
    remaining = MAX_GOAL_BYTES
    for goal in goals:
        if (not isinstance(goal, dict) or set(goal) != {"name", "status", "expected", "context", "line", "column"}
                or goal["status"] not in ("unresolved", "unsupported", "limit", "timeout")
                or type(goal["line"]) is not int or type(goal["column"]) is not int
                or not isinstance(goal["context"], str) or not goal["context"]
                or (goal["expected"] is not None and (not isinstance(goal["expected"], str) or not goal["expected"]))
                or not isinstance(goal["name"], str) or not re.fullmatch(r"\?[A-Za-z_][A-Za-z_0-9]*", goal["name"])):
            raise ValueError("invalid named-hole diagnostic")
        if goal["expected"] is not None and goal["status"] != "unresolved":
            raise ValueError("unavailable named-hole judgment carries an expected type")
        remaining -= len(goal["context"].encode()) + len((goal["expected"] or "").encode())
        if remaining < 0:
            raise ValueError("named-hole reply exceeds the context budget")
        line, column = goal["line"], goal["column"]
        if not 1 <= line <= len(lines) or not 1 <= column <= len(lines[line - 1]) or (line, column) <= previous:
            raise ValueError("invalid named-hole location or order")
        match = re.match(r"\?[A-Za-z_][A-Za-z_0-9]*", lines[line - 1][column - 1:])
        if match is None or match.group() != goal["name"]:
            raise ValueError("named-hole diagnostic differs from source")
        previous = (line, column)


def _validate_authoring(response: dict[str, object], source: str) -> None:
    if set(response) != {"ok", "sourceHash", "findings", "bindingPreview"}:
        raise ValueError("authoring worker returned an invalid result")
    findings, preview = response["findings"], response["bindingPreview"]
    if (not isinstance(findings, list) or len(findings) > MAX_AUTHORING_FINDINGS
            or not isinstance(preview, str) or len(preview.encode("utf-8")) > MAX_SOURCE_BYTES):
        raise ValueError("authoring worker returned an invalid or oversized result")
    _validate_findings(findings, source)


def _validate_findings(findings: object, source: str, *, mathematical: bool = False) -> None:
    if not isinstance(findings, list) or len(findings) > MAX_AUTHORING_FINDINGS:
        raise ValueError("compiler worker returned oversized or invalid findings")
    snapshot = SourceSnapshot("holdfast:playground-findings", 0, source, 1)
    lines = source.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    previous = (0, 0, "")
    allowed = (
        set(MATHEMATICAL_LINT_CODES) - OPT_IN_MATHEMATICAL_LINTS if mathematical else LINT_CODES - {"HOLDFAST105"}
    )
    for finding in findings:
        if (not isinstance(finding, dict) or set(finding) != {"code", "message", "line", "column"}
                or not isinstance(finding["code"], str) or finding["code"] not in allowed
                or not isinstance(finding["message"], str) or not finding["message"]
                or type(finding["line"]) is not int or type(finding["column"]) is not int):
            raise ValueError("authoring worker returned an invalid finding")
        snapshot.diagnostic_position(finding["line"], finding["column"])
        if mathematical:
            code = finding["code"]
            site = (finding["line"], finding["column"], code)
            line, column = lines[site[0] - 1], site[1] - 1
            if site <= previous:
                raise ValueError("mathematical findings must be in source order")
            previous = site
            if code == "HOLDFAST107":
                if line[column:column + 1] not in {"&", "^", "|"} or line[column:column + 2] in {"&&", "||"}:
                    raise ValueError("mathematical precedence finding does not identify a bitwise operator")
                continue
            if code == "HOLDFAST103":
                if line[column:column + 2] not in {"==", "!="}:
                    raise ValueError("mathematical comparison finding does not identify an equality operator")
                continue
            if code in {"HOLDFAST105", "HOLDFAST108"}:
                name = IDENTIFIER.match(line, column)
                if (name is None or is_pascal_case(name.group())
                        or (column and (line[column - 1].isascii()
                                        and (line[column - 1].isalnum() or line[column - 1] == "_")))):
                    raise ValueError("mathematical naming finding does not identify a source name")
            elif not line[column:column + 1] or line[column].isspace():
                raise ValueError("mathematical finding does not identify a source token")


def _compiler_response(request: dict[str, object], digest: str, *,
                       mathematical_parser: Path, parser_sha256: str) -> dict[str, object]:
    directory = str(Path(__file__).resolve().parents[1])
    payload = encode_body(request)
    if getattr(subprocess, "run", None) is not _SUBPROCESS_RUN:
        # Leave time for the worker to reap a timed-out Rocq process.
        deadline = time.monotonic() + WORKER_SECONDS - 0.5
        script = (f"import sys; sys.path.insert(0, {directory!r}); from pathlib import Path; "
                  "from toolchain.playground_worker import main; "
                  f"raise SystemExit(main(mathematical_parser=Path({str(mathematical_parser)!r}), "
                  f"parser_sha256={parser_sha256!r}, deadline={deadline!r}))")
        done = subprocess.run([sys.executable, "-I", "-c", script], input=payload,
                              capture_output=True, timeout=WORKER_SECONDS, check=False)
        if done.returncode == TIMEOUT_EXIT:
            raise subprocess.TimeoutExpired(done.args, WORKER_SECONDS)
        if done.returncode != 0:
            raise ValueError("compiler worker unavailable or output exceeds its budget")
        stdout = done.stdout
    else:
        script = (f"import sys; sys.path.insert(0, {directory!r}); from pathlib import Path; "
                  "from toolchain.playground_worker import serve_batch; "
                  f"raise SystemExit(serve_batch(mathematical_parser=Path({str(mathematical_parser)!r}), "
                  f"parser_sha256={parser_sha256!r}))")
        key = (
            sys.executable,
            str(mathematical_parser),
            parser_sha256,
            os.environ.get("VOS_BUILD_ROOT"),
            os.environ.get("VOS_ROCQ"),
            os.environ.get("VOS_ROCQCHK"),
            os.environ.get("OPAMROOT"),
            MAX_BODY_BYTES,
        )
        header = f"{len(payload)} {WORKER_SECONDS - 0.5}\n".encode("ascii")
        code, stdout = _BATCH_WORKER.request(
            key,
            [sys.executable, "-I", "-c", script],
            header,
            payload,
            timeout_seconds=WORKER_SECONDS,
            max_body_bytes=MAX_BODY_BYTES,
            timeout_exit=TIMEOUT_EXIT,
        )
        if code != 0:
            raise ValueError("compiler worker unavailable or output exceeds its budget")
    response = decode_message(stdout)
    _validate_result(response, request, digest)
    encode_body(response)
    return response


def run_compiler(request: dict[str, object], *, mathematical_parser: Path,
                 parser_sha256: str) -> dict[str, object]:
    """Source is worker stdin data, never an executable argument or a disk path."""
    source = cast("str", request["source"]).encode("utf-8")
    digest = hashlib.sha256(source).hexdigest()
    response: dict[str, object]
    try:
        if request["action"] != "authoring":
            require_parser(mathematical_parser, parser_sha256)
        response = _compiler_response(request, digest, mathematical_parser=mathematical_parser,
                                      parser_sha256=parser_sha256)
        if request["action"] != "authoring":
            require_parser(mathematical_parser, parser_sha256)
    except subprocess.TimeoutExpired:
        response = {"ok": False, "sourceHash": digest,
                    "error": {"kind": "timeout", "line": 1, "column": 1,
                              "message": "Compiler exceeded five seconds; no result"}}
    except (OSError, ValueError):
        response = {"ok": False, "sourceHash": digest,
                    "error": {"kind": "internal", "line": 1, "column": 1,
                              "message": "Compiler worker unavailable or response exceeds its budget"}}
    else:
        return response
    if request["action"] == "compile":
        response["editorServices"] = False
    return response


@dataclass
class Session:
    server: Server = field(default_factory=Server)
    touched: float = field(default_factory=time.monotonic)


class PlaygroundServer(HTTPServer):
    """One synchronous request at a time bounds worker and overlay concurrency."""

    request_queue_size = 8

    def __init__(self, port: int = 8765, *, mathematical_parser: Path, assets: Path | None = None) -> None:
        self.token = secrets.token_urlsafe(32)
        self.mathematical_parser = mathematical_parser
        self.parser_sha256 = file_sha256(mathematical_parser)
        tools = Path(__file__).resolve().parent
        self.compiler_inputs = [tools / name for name in (*FRONTEND_SOURCES, "parser.py", "surface.py",
                                                          "mathematical.py", "playground_worker.py", "proofenv.py")]
        self.compiler_inputs.extend(tools.parent / "rocq" / name for name in SUPPORT_FILES)
        self.compiler_inputs.append(tools.parent / "opam" / "rocq.lock")
        self.compiler_inputs.extend((mathematical_parser, Path(sys.executable)))
        with mathematical_parser.open("rb") as stream:
            if stream.read(3) == b"#!/":
                self.compiler_inputs.append(bytecode_interpreter(mathematical_parser))
        self.generation = self.compiler_generation()
        self.sessions: dict[str, Session] = {}
        self.assets = (Path(__file__).resolve().parents[2] / "docs"
                       if assets is None else assets)
        super().__init__(("127.0.0.1", port), PlaygroundHandler)
        self.authority = f"127.0.0.1:{self.server_address[1]}"
        self.origin = f"http://{self.authority}"

    @property
    def launch_url(self) -> str:
        return f"{self.origin}/#token={self.token}"

    def compiler_generation(self) -> str:
        digest = hashlib.sha256()
        for path in self.compiler_inputs:
            digest.update(bytes.fromhex(file_sha256(path)))
        try:
            prover = shutil.which(proofenv.rocq_command()[0])
        except SystemExit:
            prover = None
        if prover is not None:
            digest.update(prover.encode("utf-8"))
            digest.update(bytes.fromhex(file_sha256(Path(prover))))
        return digest.hexdigest()

    def compiler_current(self) -> bool:
        try:
            return self.generation == self.compiler_generation()
        except OSError:
            return False

    @override
    def get_request(self) -> tuple[socket.socket, tuple[str, int]]:
        connection, address = super().get_request()
        connection.settimeout(READ_SECONDS)
        return connection, cast("tuple[str, int]", address)

    def expire_sessions(self) -> None:
        now = time.monotonic()
        self.sessions = {identity: item for identity, item in self.sessions.items()
                         if now - item.touched < SESSION_SECONDS}

    @override
    def server_close(self) -> None:
        self.sessions.clear()
        super().server_close()


class PlaygroundHandler(BaseHTTPRequestHandler):
    server_version = "HoldFastPlayground"
    _body_read = False

    @override
    def setup(self) -> None:
        super().setup()
        self._read_timer = threading.Timer(READ_SECONDS, self._end_read)
        self._read_timer.daemon = True
        self._read_timer.start()

    def _end_read(self) -> None:
        with suppress(OSError):
            self.connection.shutdown(socket.SHUT_RD)

    @override
    def handle(self) -> None:
        with suppress(ConnectionError, TimeoutError):
            super().handle()

    @override
    def finish(self) -> None:
        self._read_timer.cancel()
        super().finish()

    @property
    def playground(self) -> PlaygroundServer:
        return cast("PlaygroundServer", self.server)

    @override
    def log_message(self, format: str, *args: object) -> None:
        """Avoid logging source, request paths or authentication material."""

    def _send(self, status: int, body: bytes, content_type: str = "application/json; charset=utf-8") -> None:
        self._read_timer.cancel()
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        if status == 200 and self.path in {"/api/compile", "/api/evaluate"}:
            self.send_header("X-HoldFast-Compiler-Generation", self.playground.generation)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Connection", "close")
        self.end_headers()
        self.close_connection = True
        self.wfile.write(body)

    def _error(self, status: int, message: str) -> None:
        # Drain an ordinary bounded body before closing, so Windows can deliver
        # the error response without resetting a connection with unread bytes.
        lengths = self.headers.get_all("Content-Length", [])
        if (not self._body_read and len(lengths) == 1 and lengths[0].isascii()
                and lengths[0].isdecimal() and len(lengths[0]) <= 8
                and int(lengths[0]) <= MAX_BODY_BYTES
                and self.headers.get("Transfer-Encoding") is None):
            self._body_read = True
            try:
                self.rfile.read(int(lengths[0]))
            except OSError:
                self.close_connection = True
        self._send(status, encode_body({"error": message}))

    def _authority(self) -> bool:
        hosts = self.headers.get_all("Host", [])
        origins = self.headers.get_all("Origin", [])
        if hosts != [self.playground.authority] or origins not in ([], [self.playground.origin]):
            self._error(403, "Host or Origin does not match the local playground")
            return False
        return True

    def do_GET(self) -> None:
        if not self._authority():
            return
        asset = ASSETS.get(self.path)
        if asset is None:
            self._error(404, "Unknown playground asset")
            return
        try:
            body = (self.playground.assets / asset[0]).read_bytes()
        except OSError:
            self._error(503, "Playground assets unavailable")
            return
        self._send(200, body, asset[1])

    def _read_json(self, size: int) -> dict[str, object]:
        self._body_read = True
        raw = self.rfile.read(size)
        if len(raw) != size:
            raise ValueError("Truncated JSON body")
        self._read_timer.cancel()
        return decode_message(raw)

    def do_POST(self) -> None:
        if not self._authority():
            return
        authorization = self.headers.get_all("Authorization", [])
        if (len(authorization) != 1 or not hmac.compare_digest(
                authorization[0].encode("utf-8"), f"Bearer {self.playground.token}".encode())):
            self._error(401, "Missing or invalid playground token; reopen the printed launch URL")
            return
        if self.path not in {"/api/session", "/api/close", "/api/lsp", "/api/compile", "/api/evaluate",
                             "/api/authoring", "/api/compiler-generation"}:
            self._error(404, "Unknown playground operation")
            return
        lengths = self.headers.get_all("Content-Length", [])
        if (len(lengths) != 1 or not lengths[0].isascii() or not lengths[0].isdecimal()
                or len(lengths[0]) > 8 or self.headers.get("Transfer-Encoding") is not None):
            self._error(400, "One decimal Content-Length is required")
            return
        size = int(lengths[0])
        if size > MAX_BODY_BYTES:
            self._error(413, "Request exceeds the JSON byte budget")
            return
        if self.headers.get_all("Content-Type", []) != ["application/json"]:
            self._error(415, "Use application/json with UTF-8")
            return
        try:
            request = self._read_json(size)
            response = self._dispatch(request)
            encoded = encode_body(response)
        except TimeoutError:
            self._error(408, "Request read timed out")
            return
        except (ValueError, UnicodeError) as error:
            self._error(400, str(error))
            return
        except LookupError as error:
            self._error(410, str(error))
            return
        self._send(200, encoded)

    def _dispatch(self, request: dict[str, object]) -> dict[str, object]:
        self.playground.expire_sessions()
        if self.path == "/api/compiler-generation":
            if request:
                raise ValueError("Compiler generation requires an empty object")
            return {"generation": self.playground.generation, "current": self.playground.compiler_current()}
        if self.path == "/api/close":
            if set(request) != {"session"} or not isinstance(request["session"], str):
                raise ValueError("Expected a session identifier")
            self.playground.sessions.pop(request["session"], None)
            return {"closed": True}
        if self.path == "/api/session":
            if request:
                raise ValueError("Session creation requires an empty object")
            if len(self.playground.sessions) >= MAX_SESSIONS:
                raise ValueError("Session limit reached; close idle tabs and restart the playground")
            identity = secrets.token_urlsafe(24)
            self.playground.sessions[identity] = Session()
            return {"session": identity}
        if self.path == "/api/lsp":
            if (set(request) != {"session", "message"} or not isinstance(request["session"], str)
                    or not isinstance(request["message"], dict)):
                raise ValueError("Expected a session identifier and LSP message object")
            session = self.playground.sessions.get(request["session"])
            if session is None:
                raise LookupError("Session expired or unknown; reconnect to the playground")
            session.touched = time.monotonic()
            messages = session.server.handle(cast("dict[str, object]", request["message"]))
            if session.server.exit_code is not None:
                del self.playground.sessions[request["session"]]
            return {"messages": messages}
        expected = {"source", "expression", "valueType"} if self.path == "/api/evaluate" else {"source"}
        if set(request) != expected or not all(isinstance(value, str) for value in request.values()):
            raise ValueError("Compiler request has missing, extra or non-text fields")
        source = cast("str", request["source"])
        if len(source.encode("utf-8")) > MAX_SOURCE_BYTES:
            raise ValueError("Source exceeds the compiler's UTF-8 byte budget")
        if self.path == "/api/evaluate":
            if request["valueType"] not in {"Nat", "bool"}:
                raise ValueError("Expression result type must be Nat or bool")
            if len(cast("str", request["expression"]).encode("utf-8")) > 4096:
                raise ValueError("Expression exceeds 4096 UTF-8 bytes")
        operation = {**request, "action": self.path.rsplit("/", 1)[1]}
        authoring = self.path == "/api/authoring"
        if authoring or self.playground.compiler_current():
            result = run_compiler(operation, mathematical_parser=self.playground.mathematical_parser,
                                  parser_sha256=self.playground.parser_sha256)
            if authoring or self.playground.compiler_current():
                return result
        refusal: dict[str, object] = {"ok": False, "sourceHash": hashlib.sha256(source.encode()).hexdigest(),
                                      "error": {"kind": "internal", "line": 1, "column": 1,
                                                "message": "Compiler dependencies changed. Restart the local playground."}}
        if self.path == "/api/compile":
            refusal["editorServices"] = False
        return refusal
