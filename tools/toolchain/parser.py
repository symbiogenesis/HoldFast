# SPDX-License-Identifier: Apache-2.0
"""Build and exercise HoldFast's syntax-only Menhir development parser.

The parser is a native-lane build product. Its JSON syntax tree is no type,
elaboration, checked-parser or source-correspondence verdict.
"""

import atexit
import contextlib
import hashlib
import json
import os
import re
import selectors
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from collections.abc import Generator, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from importlib import import_module
from pathlib import Path
from typing import cast

from toolchain import (
    env,
    proofenv,
)
from toolchain import (
    surface as holdfast_surface,
)
from toolchain._isolated_worker import (
    close_worker_proc as _close_worker_proc,
)
from toolchain._isolated_worker import (
    parse_batch_reply_line,
)
from toolchain.ast import MAX_SOURCE_BYTES, MAX_SYNTAX_DEPTH, HoldFastError, trivia_end
from toolchain.atomic import atomic_path, publish_report
from toolchain.hashing import file_sha256 as _digest
from toolchain.jsonutil import exceeds_nesting, finite_float, unique_object

type Json = bool | int | float | str | list[Json] | dict[str, Json] | None

SOURCES = ("ast.ml", "parser.mly", "lexer.mll", "main.ml")
SURFACE_FIXTURE = "tools/tests/fixtures/surface.hf"
INPUT_PATHS = (
    *(f"tools/toolchain/parser/{name}" for name in SOURCES),
    "tools/opam/sail.lock", "tools/toolchain/parser.py", "tools/toolchain/surface.py",
    "tools/toolchain/_isolated_worker.py", "tools/toolchain/hashing.py",
    "tools/toolchain/jsonutil.py", "tools/toolchain/atomic.py",
    "examples/pure.hf", "examples/constants.hf", "examples/expressions.hf", SURFACE_FIXTURE,
)
GENERATED = ("parser.ml", "parser.mli", "lexer.ml")
GENERATION_FLAGS = ("--strict", "--infer", "--explain")
BUILD_TIMEOUT = 120
PARSE_TIMEOUT = 15
MAX_RESPONSE_BYTES = 8 * 1024 * 1024
# A syntax edge can add a node object and a child-list container. The response
# envelope, located names and span arrays require the remaining four levels.
MAX_RESPONSE_DEPTH = 2 * MAX_SYNTAX_DEPTH + 4
CACHE_RECEIPT_BYTES = 65_536
_CACHE_ENTRY = re.compile(r"entry-[0-9a-f]{64}-[0-9a-f]{32}")


@dataclass(frozen=True)
class Build:
    directory: Path
    executable: Path
    receipt: dict[str, object]


def bytecode_interpreter(executable: Path) -> Path:
    with executable.open("rb") as stream:
        line = stream.readline(4096)
    if not line.startswith(b"#!/") or not line.endswith(b"\n"):
        raise ValueError("missing bytecode interpreter")
    return Path(os.fsdecode(line[2:-1]))


def interpreter_digest(compiled: Build) -> str:
    runtime_digest = _digest(bytecode_interpreter(compiled.executable))
    toolchain = compiled.receipt.get("toolchain")
    binaries = toolchain.get("binary_sha256") if isinstance(toolchain, dict) else None
    if not isinstance(binaries, dict) or binaries.get("ocamlrun") != runtime_digest:
        raise ValueError("parser interpreter differs from its build")
    return runtime_digest


def _locked_versions(root: Path) -> dict[str, str]:
    text = (root / "tools/opam/sail.lock").read_text(encoding="utf-8")
    result: dict[str, str] = {}
    for package in ("menhir", "ocaml-base-compiler"):
        versions = set(re.findall(r'"' + re.escape(package) + r'\.([^"\s]+)"', text))
        if len(versions) != 1:
            raise ValueError(f"Sail snapshot must name one {package} version")
        result[package] = versions.pop()
    return result


def _sail_bin() -> Path | None:
    candidate = proofenv.opam_root() / env.SAIL_SWITCH / "bin"
    if all((candidate / name).is_file() for name in ("menhir", "ocamlc", "ocamllex", "ocamlrun")):
        return candidate
    return None


def _run(arguments: list[str], directory: Path, *, timeout: int = BUILD_TIMEOUT) -> str:
    run_env: dict[str, str] | None = None
    if arguments and (bin_dir := _sail_bin()) is not None and Path(arguments[0]).parent == bin_dir:
        run_env = os.environ.copy()
        run_env["PATH"] = f"{bin_dir}{os.pathsep}{run_env.get('PATH', '')}"
    try:
        done = subprocess.run(arguments, cwd=directory, env=run_env, capture_output=True,
                              text=True, encoding="utf-8", timeout=timeout, check=False)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"{arguments[0]} exceeded {timeout} seconds") from error
    if done.returncode:
        detail = (done.stderr or done.stdout).strip()
        raise RuntimeError(f"{arguments[0]} exited {done.returncode}: {detail}")
    return done.stdout.strip()


def _opam(arguments: list[str]) -> list[str]:
    if arguments and (bin_dir := _sail_bin()) is not None and (bin_dir / arguments[0]).is_file():
        return [str(bin_dir / arguments[0]), *arguments[1:]]
    return ["opam", "exec", "--switch", env.SAIL_SWITCH, "--", *arguments]


def _toolchain(root: Path) -> dict[str, object]:
    wanted = _locked_versions(root)
    menhir = _run(_opam(["menhir", "--version"]), root)
    ocaml = _run(_opam(["ocamlc", "-version"]), root)
    lexer = _run(_opam(["ocamllex", "-version"]), root)
    if menhir != f"menhir, version {wanted['menhir']}":
        raise ValueError(f"Menhir identity differs from Sail snapshot: {menhir}")
    if ocaml != wanted["ocaml-base-compiler"]:
        raise ValueError(f"OCaml identity differs from Sail snapshot: {ocaml}")
    if lexer != f"The OCaml lexer generator, version {ocaml}":
        raise ValueError(f"ocamllex identity differs from Sail snapshot: {lexer}")
    bin_dir = _sail_bin() if _unpatched("_run", _REAL_RUN) else None
    binary_dir = (bin_dir if bin_dir is not None
                  else Path(_run(["opam", "var", "bin", "--switch", env.SAIL_SWITCH], root)))
    if not binary_dir.is_absolute():
        raise ValueError("opam returned a relative tool directory")
    return {"switch": env.SAIL_SWITCH, "menhir": menhir, "ocamlc": ocaml,
            "ocamllex": lexer,
            "binary_sha256": {name: _digest(binary_dir / name)
                              for name in ("menhir", "ocamlc", "ocamllex", "ocamlrun")}}


def _unpatched(name: str, original: object) -> bool:
    return globals().get(name) is original


def _subprocess_unpatched() -> bool:
    return getattr(subprocess, "run", None) is _REAL_SUBPROCESS_RUN


_REAL_RUN = _run
_REAL_TOOLCHAIN = _toolchain
_REAL_DIGEST = _digest
_REAL_SUBPROCESS_RUN = subprocess.run

_TOOLCHAIN_CACHE_LOCK = threading.Lock()
_TOOLCHAIN_CACHE: tuple[tuple[object, ...], dict[str, object]] | None = None


def _stat_sig(path: Path) -> tuple[int, int, int, int] | None:
    try:
        st = path.stat()
    except OSError:
        return None
    return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns)


def _cached_toolchain(root: Path) -> dict[str, object]:
    global _TOOLCHAIN_CACHE  # noqa: PLW0603
    if not (_unpatched("_toolchain", _REAL_TOOLCHAIN) and _unpatched("_run", _REAL_RUN) and _unpatched("_digest", _REAL_DIGEST)):
        return _toolchain(root)
    bin_dir = _sail_bin()
    lock_sig = _stat_sig(root / "tools/opam/sail.lock")
    if bin_dir is None or lock_sig is None:
        return _toolchain(root)
    sigs = tuple(_stat_sig(bin_dir / name) for name in ("menhir", "ocamlc", "ocamllex", "ocamlrun"))
    if any(sig is None for sig in sigs):
        return _toolchain(root)
    cache_key: tuple[object, ...] = (env.SAIL_SWITCH, str(bin_dir), lock_sig, sigs)
    with _TOOLCHAIN_CACHE_LOCK:
        if _TOOLCHAIN_CACHE is not None and _TOOLCHAIN_CACHE[0] == cache_key:
            return _TOOLCHAIN_CACHE[1].copy()
    fresh = _toolchain(root)
    with _TOOLCHAIN_CACHE_LOCK:
        _TOOLCHAIN_CACHE = (cache_key, fresh.copy())
    return fresh


def _inputs(root: Path) -> dict[str, str]:
    return {name: _digest(root / name) for name in INPUT_PATHS}


def _commands() -> tuple[list[str], ...]:
    return (["ocamlc", "-c", "ast.ml"],
            ["menhir", *GENERATION_FLAGS, "parser.mly"],
            ["ocamllex", "lexer.mll"],
            ["ocamlc", "-c", "parser.mli"],
            ["ocamlc", "-c", "parser.ml"],
            ["ocamlc", "-c", "lexer.ml"],
            ["ocamlc", "-c", "main.ml"],
            ["ocamlc", "-o", "holdfast-parser", "ast.cmo", "parser.cmo", "lexer.cmo", "main.cmo"])


def _compile(root: Path, directory: Path, tools: dict[str, object]) -> Build:
    inputs = _inputs(root)
    for name in SOURCES:
        shutil.copyfile(root / "tools/toolchain/parser" / name, directory / name)
    commands = _commands()
    for arguments in commands:
        _run(_opam(arguments), directory)
    if _inputs(root) != inputs:
        raise ValueError("parser inputs changed during the build")
    if _toolchain(root) != tools:
        raise ValueError("parser toolchain changed during the build")
    executable = directory / "holdfast-parser"
    outputs = {name: _digest(directory / name) for name in (*GENERATED, "holdfast-parser")}
    receipt: dict[str, object] = {
        "schema": 1, "scope": "holdfast-syntax-only-development-parser", "status": "built",
        "inputs": inputs, "toolchain": tools, "commands": commands,
        "generated_sha256": outputs, "directory": str(directory),
    }
    publish_report(directory / "receipt.json", receipt)
    return Build(directory, executable, receipt)


def _work_root(root: Path) -> Path:
    directory = env.lane_root(env.lane_of(root)) / "holdfast-parser"
    kind = env.filesystem(directory)
    if kind in env.CROSS_OS_FILESYSTEMS | env.VOLATILE_FILESYSTEMS or not kind:
        raise ValueError(f"parser build directory needs a persistent native filesystem: {directory} ({kind})")
    directory.mkdir(parents=True, exist_ok=True)
    return directory


_REAL_WORK_ROOT = _work_root


def _cache_root(root: Path) -> Path:
    if not _unpatched("_work_root", _REAL_WORK_ROOT):
        native = _work_root(root)
        cache = native / "ordinary-cache"
        cache.mkdir(exist_ok=True)
        if cache.is_symlink() or cache.resolve().parent != native.resolve():
            raise ValueError(f"parser cache directory escapes its native build root: {cache}")
        return cache
    cache = env.build_root() / "holdfast-parser-cache"
    kind = env.filesystem(cache)
    if kind in env.CROSS_OS_FILESYSTEMS | env.VOLATILE_FILESYSTEMS or not kind:
        raise ValueError(f"parser cache directory needs a persistent native filesystem: {cache} ({kind})")
    cache.mkdir(parents=True, exist_ok=True)
    if cache.is_symlink():
        raise ValueError(f"parser cache directory cannot be a symlink: {cache}")
    return cache


def _file_lock(path: Path, timeout: int) -> contextlib.AbstractContextManager[object]:
    lock_cls = import_module("filelock").FileLock
    return cast("contextlib.AbstractContextManager[object]", lock_cls(path, timeout=timeout))


def build(root: Path) -> Build:
    """Make a fresh build; unsuccessful builds never acquire a passing receipt."""
    directory = _work_root(root)
    with _file_lock(directory / "build.lock", timeout=1):
        tools = _toolchain(root)
        output = Path(tempfile.mkdtemp(prefix="build-", dir=directory))
        return _compile(root, output, tools)


_UNPATCHED_BUILD = build


def _current_cache_entry(cache: Path) -> Path | None:
    try:
        with (cache / "current").open(encoding="utf-8") as stream:
            raw = stream.read(129)
        if len(raw) > 128:
            return None
        name = raw.strip()
        return cache / name if _CACHE_ENTRY.fullmatch(name) else None
    except (OSError, UnicodeDecodeError):
        return None


def _cache_hit(directory: Path, inputs: dict[str, str], tools: dict[str, object]) -> Build | None:
    try:
        if (directory.is_symlink() or not directory.is_dir()
                or directory.resolve().parent != directory.parent.resolve()
                or (directory / "receipt.json").is_symlink()):
            return None
        with (directory / "receipt.json").open("rb") as stream:
            raw = stream.read(CACHE_RECEIPT_BYTES + 1)
        if len(raw) > CACHE_RECEIPT_BYTES:
            return None
        value: object = json.loads(raw, object_pairs_hook=unique_object)
        if not isinstance(value, dict):
            return None
        receipt = cast("dict[str, object]", value)
        if (type(receipt.get("schema")) is not int or receipt["schema"] != 1
                or receipt.get("scope") != "holdfast-syntax-only-development-parser"
                or receipt.get("status") != "built" or receipt.get("inputs") != inputs
                or receipt.get("toolchain") != tools or receipt.get("directory") != str(directory)
                or receipt.get("commands") != list(_commands())):
            return None
        outputs = receipt.get("generated_sha256")
        if not isinstance(outputs, dict) or set(outputs) != {*GENERATED, "holdfast-parser"}:
            return None
        for name in (*GENERATED, "holdfast-parser"):
            path = directory / name
            if path.is_symlink() or _digest(path) != outputs[name]:
                return None
    except (OSError, ValueError, TypeError, RecursionError):
        return None
    return Build(directory, directory / "holdfast-parser", receipt)


def _cache_leased(cache: Path, entry: Path) -> bool:
    leased = False
    for marker in cache.glob(f"lease-{entry.name}-*.lock"):
        try:
            with _file_lock(marker, timeout=0):
                pass
        except TimeoutError:
            leased = True
        else:
            marker.unlink(missing_ok=True)
    return leased


def _prune_cache(cache: Path, current: Path | None) -> None:
    for entry in cache.glob("entry-*"):
        if _CACHE_ENTRY.fullmatch(entry.name):
            leased = _cache_leased(cache, entry)
            if entry == current or leased:
                continue
            if entry.is_symlink() or not entry.is_dir():
                entry.unlink(missing_ok=True)
                continue
            if entry.resolve().parent != cache.resolve():
                raise ValueError(f"parser cache entry escapes its cache directory: {entry}")
            shutil.rmtree(entry)


def _compile_cache_entry(root: Path, entry: Path, inputs: dict[str, str], tools: dict[str, object]) -> Build:
    compiled = _compile(root, entry, tools)
    if compiled.receipt["inputs"] != inputs:
        raise ValueError("parser inputs changed before cache construction")
    return compiled


@contextlib.contextmanager
def cached_build(root: Path) -> Generator[Build]:
    """Lease an immutable ordinary-use build; qualification keeps using fresh builds.

    Retain only the current generation and generations with live users. A unique
    OS-backed lease for each user allows concurrent readers and recovers after a
    crashed user. The cache lock serializes construction, publication and pruning.
    """
    cache = _cache_root(root)
    with contextlib.ExitStack() as lease:
        with _file_lock(cache / "cache.lock", timeout=BUILD_TIMEOUT):
            inputs, tools = _inputs(root), _cached_toolchain(root)
            identity = json.dumps({"inputs": inputs,
                                   "toolchain": tools, "commands": _commands()}, sort_keys=True)
            key = hashlib.sha256(identity.encode("utf-8")).hexdigest()
            entry = _current_cache_entry(cache)
            pointer_damaged = (cache / "current").exists() and entry is None
            compiled = (_cache_hit(entry, inputs, tools)
                        if entry is not None and entry.name.startswith(f"entry-{key}-") else None)
            if compiled is None and not pointer_damaged and entry is not None:
                for existing in sorted(cache.glob(f"entry-{key}-*")):
                    if _CACHE_ENTRY.fullmatch(existing.name):
                        hit = _cache_hit(existing, inputs, tools)
                        if hit is not None:
                            compiled = hit
                            with atomic_path(cache / "current") as pending:
                                pending.write_text(existing.name + "\n", encoding="utf-8", newline="")
                            break
            if compiled is None:
                entry = cache / f"entry-{key}-{uuid.uuid4().hex}"
                entry.mkdir()
                try:
                    compiled = _compile_cache_entry(root, entry, inputs, tools)
                    with atomic_path(cache / "current") as pending:
                        pending.write_text(entry.name + "\n", encoding="utf-8", newline="")
                except BaseException:
                    with contextlib.suppress(OSError, TimeoutError, ValueError):
                        _prune_cache(cache, _current_cache_entry(cache))
                    raise
            entry = compiled.directory
            marker = cache / f"lease-{entry.name}-{uuid.uuid4().hex}.lock"
            lease.enter_context(_file_lock(marker, timeout=0))
            _prune_cache(cache, entry)
        try:
            yield compiled
        finally:
            lease.close()
            with (contextlib.suppress(OSError, TimeoutError, ValueError),
                  _file_lock(cache / "cache.lock", timeout=0)):
                marker.unlink(missing_ok=True)
                _prune_cache(cache, _current_cache_entry(cache))
                if not compiled.executable.is_file():
                    _reset_worker_if_executable(compiled.executable)


def read_source(path: Path) -> bytes:
    with path.open("rb") as stream:
        source = stream.read(MAX_SOURCE_BYTES + 1)
    if len(source) > MAX_SOURCE_BYTES:
        raise HoldFastError("limit", 1, 1, f"source exceeds {MAX_SOURCE_BYTES} bytes")
    return source


def _object(value: Json, description: str) -> dict[str, Json]:
    if not isinstance(value, dict):
        raise TypeError(f"native parser returned invalid {description}")
    return value


def _response(raw: bytes) -> dict[str, Json]:
    """Bound nesting before the JSON decoder, and reject ambiguous objects."""
    if exceeds_nesting(raw, MAX_RESPONSE_DEPTH):
        raise ValueError("native parser response exceeds JSON nesting bound")

    def reject_constant(value: str) -> Json:
        raise ValueError(f"non-finite native JSON value: {value}")

    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object,
                           parse_float=finite_float, parse_constant=reject_constant)
        return _object(cast("Json", value), "JSON response")
    except (TypeError, ValueError, UnicodeError, RecursionError) as error:
        raise ValueError("native parser returned malformed JSON") from error


def _validate_tree(value: Json, source: bytes, *, check_surrogates: bool = True) -> None:
    try:
        source.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError("native parser accepted invalid UTF-8 source") from error
    source_len = len(source)
    pending = [(value, (0, source_len), 0)]
    while pending:
        current, parent, depth = pending.pop()
        if isinstance(current, list):
            pending.extend((child, parent, depth) for child in current)
        elif isinstance(current, dict):
            if check_surrogates:
                for key in current:
                    try:
                        key.encode("utf-8")
                    except UnicodeEncodeError as error:
                        raise ValueError("native parser returned a non-Unicode syntax key") from error
            if "kind" in current:
                depth += 1
                if depth > MAX_SYNTAX_DEPTH:
                    raise ValueError("native parser returned excessive syntax depth")
            if "kind" in current or "text" in current:
                span = current.get("span")
                if not isinstance(span, list) or len(span) != 2:
                    raise ValueError("native parser returned an invalid source span")
                start, end = span
                if type(start) is not int or type(end) is not int:
                    raise ValueError("native parser returned an invalid source span")
                if not 0 <= start <= end <= source_len:
                    raise ValueError("native parser returned a source span outside its input")
                if not parent[0] <= start <= end <= parent[1]:
                    raise ValueError("native parser returned a source span outside its parent")
                if ((start != source_len and (source[start] & 0xC0) == 0x80)
                        or (end != source_len and (source[end] & 0xC0) == 0x80)):
                    raise ValueError("native parser returned a span splitting a UTF-8 character")
                parent = (start, end)
            pending.extend((child, parent, depth) for child in current.values())
        elif check_surrogates and isinstance(current, str):
            try:
                current.encode("utf-8")
            except UnicodeEncodeError as error:
                raise ValueError("native parser returned a non-Unicode syntax string") from error


def _layout_ranges(source: bytes, tokens: Json) -> list[Json]:
    """Interleave the surface lexer's exact token ranges and all original comments."""
    if not isinstance(tokens, list):
        raise TypeError("native parser omitted its token ranges")
    parts: list[Json] = []
    def comment(start: int, end: int) -> None:
        parts.append([start, end])
    cursor = 0
    for span in tokens:
        if not isinstance(span, list) or len(span) != 2:
            raise ValueError("native parser returned a malformed token range")
        start, end = span
        if (type(start) is not int or type(end) is not int or not cursor <= start < end <= len(source)
                or trivia_end(source, cursor, block_comments=True, comment=comment) != start):
            raise ValueError("native parser tokens do not cover their source")
        source[start:end].decode("utf-8")
        parts.append(span)
        cursor = end
    if trivia_end(source, cursor, block_comments=True, comment=comment) != len(source):
        raise ValueError("native parser tokens omit trailing source")
    return parts


def decode_response(source: bytes, returncode: int, stdout: bytes, stderr: bytes = b"", *,
                    surface: bool = False, layout: bool = False) -> dict[str, Json]:
    """Validate one native parser process response against the input source."""
    if len(stdout) > MAX_RESPONSE_BYTES or stderr:
        raise ValueError("native parser returned excessive output or unexpected standard error")
    response = _response(stdout)
    if returncode == 1:
        kind, line, column, message = (response.get(key) for key in ("kind", "line", "column", "message"))
        if (set(response) != {"kind", "line", "column", "message"}
                or not isinstance(kind, str) or kind not in {"syntax", "unsupported", "encoding", "limit"}
                or type(line) is not int or type(column) is not int
                or line < 1 or column < 1 or not isinstance(message, str)):
            raise ValueError("native parser returned an invalid refusal")
        try:
            message.encode("utf-8")
        except UnicodeEncodeError as error:
            raise ValueError("native parser returned an invalid refusal message") from error
        raise HoldFastError(cast("str", kind), line, column, message)
    if returncode:
        raise RuntimeError(f"native parser exited {returncode}")
    ast = _object(response.get("ast"), "syntax tree")
    schema, kind = (2, "surface_file") if surface else (1, "file")
    fields = {"schema", "ast", "tokens"} if layout else {"schema", "ast"}
    if (set(response) != fields or type(response.get("schema")) is not int
            or response["schema"] != schema or ast.get("kind") != kind):
        raise ValueError("native parser returned an unsupported syntax-tree schema")
    _validate_tree(ast, source, check_surrogates=b"\\u" in stdout)
    result: dict[str, Json] = {"schema": schema, "ast": ast, "source_sha256": hashlib.sha256(source).hexdigest()}
    if layout:
        result["layout"] = _layout_ranges(source, response["tokens"])
    return result


_DEV_WORKER_LOCK = threading.Lock()
_DEV_WORKER: dict[str, object] = {"proc": None, "executable": None, "buf": bytearray()}
_VERIFIED_EXE_LOCK = threading.Lock()
_VERIFIED_EXECUTABLES: dict[str, tuple[str, tuple[int, int, int, int, int]]] = {}


def reset_worker() -> None:
    """Terminate any persistent development-parser `--batch` worker."""
    with _DEV_WORKER_LOCK:
        proc = cast("subprocess.Popen[bytes] | None", _DEV_WORKER.get("proc"))
        _DEV_WORKER["proc"] = None
        _DEV_WORKER["executable"] = None
        _DEV_WORKER["buf"] = bytearray()
        _close_worker_proc(proc)


def _reset_worker_if_executable(executable: Path) -> None:
    target = str(executable)
    with _DEV_WORKER_LOCK:
        if _DEV_WORKER.get("executable") == target:
            proc = cast("subprocess.Popen[bytes] | None", _DEV_WORKER.get("proc"))
            _DEV_WORKER["proc"] = None
            _DEV_WORKER["executable"] = None
            _DEV_WORKER["buf"] = bytearray()
            _close_worker_proc(proc)


atexit.register(reset_worker)


def _verify_executable(compiled: Build) -> None:
    outputs = cast("dict[str, str]", compiled.receipt["generated_sha256"])
    expected = outputs["holdfast-parser"]
    if not _unpatched("_digest", _REAL_DIGEST) or not _subprocess_unpatched():
        if _digest(compiled.executable) != expected:
            raise ValueError("native parser executable changed after its build")
        return
    try:
        st = compiled.executable.stat()
    except OSError as error:
        raise ValueError("native parser executable is missing") from error
    stat_sig = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
    exe_key = str(compiled.executable)
    with _VERIFIED_EXE_LOCK:
        cached = _VERIFIED_EXECUTABLES.get(exe_key)
    if cached == (expected, stat_sig):
        return
    if _digest(compiled.executable) != expected:
        with _VERIFIED_EXE_LOCK:
            _VERIFIED_EXECUTABLES.pop(exe_key, None)
        _reset_worker_if_executable(compiled.executable)
        raise ValueError("native parser executable changed after its build")
    with _VERIFIED_EXE_LOCK:
        _VERIFIED_EXECUTABLES[exe_key] = (expected, stat_sig)


def _read_batch_line(proc: subprocess.Popen[bytes], buf: bytearray) -> tuple[bytes, bytes]:
    assert proc.stdout is not None and proc.stderr is not None  # noqa: S101
    out_fd = proc.stdout.fileno()
    err_fd = proc.stderr.fileno()
    deadline = time.monotonic() + PARSE_TIMEOUT
    stderr_chunks: list[bytes] = []
    with selectors.DefaultSelector() as selector:
        selector.register(out_fd, selectors.EVENT_READ)
        selector.register(err_fd, selectors.EVENT_READ)
        while True:
            newline = buf.find(b"\n")
            if newline != -1:
                line = bytes(buf[: newline + 1])
                del buf[: newline + 1]
                return line, b"".join(stderr_chunks)
            if len(buf) > MAX_RESPONSE_BYTES + 32:
                raise ValueError("native parser returned excessive output or unexpected standard error")
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise HoldFastError("limit", 1, 1, f"parser exceeded {PARSE_TIMEOUT} seconds")
            ready = selector.select(timeout=remaining)
            if not ready:
                raise HoldFastError("limit", 1, 1, f"parser exceeded {PARSE_TIMEOUT} seconds")
            for key, _events in ready:
                if key.fd == err_fd:
                    err_chunk = os.read(err_fd, 4096)
                    if err_chunk:
                        stderr_chunks.append(err_chunk)
                        raise ValueError("native parser returned excessive output or unexpected standard error")
                    selector.unregister(err_fd)
                elif key.fd == out_fd:
                    chunk = os.read(out_fd, 65_536)
                    if not chunk:
                        return b"", b"".join(stderr_chunks)
                    buf.extend(chunk)


def _parse_batch(compiled: Build, source: bytes, *, surface: bool, layout: bool) -> tuple[int, bytes, bytes]:
    mode = "surface-layout" if layout else ("surface" if surface else "pure")
    frame = f"{mode} {len(source)}\n".encode("ascii") + source
    exe_str = str(compiled.executable)
    with _DEV_WORKER_LOCK:
        for attempt in range(2):
            proc = cast("subprocess.Popen[bytes] | None", _DEV_WORKER.get("proc"))
            buf = cast("bytearray", _DEV_WORKER["buf"])
            if proc is None or _DEV_WORKER.get("executable") != exe_str or proc.poll() is not None:
                _close_worker_proc(proc)
                buf = bytearray()
                proc = subprocess.Popen(
                    [exe_str, "--batch"],
                    cwd=compiled.directory,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                _DEV_WORKER["proc"] = proc
                _DEV_WORKER["executable"] = exe_str
                _DEV_WORKER["buf"] = buf
            assert proc.stdin is not None  # noqa: S101
            line = b""
            stderr_bytes = b""
            try:
                proc.stdin.write(frame)
                proc.stdin.flush()
                line, stderr_bytes = _read_batch_line(proc, buf)
            except HoldFastError:
                _DEV_WORKER["proc"] = None
                _DEV_WORKER["executable"] = None
                _DEV_WORKER["buf"] = bytearray()
                with contextlib.suppress(OSError):
                    proc.kill()
                _close_worker_proc(proc)
                raise
            except ValueError:
                _DEV_WORKER["proc"] = None
                _DEV_WORKER["executable"] = None
                _DEV_WORKER["buf"] = bytearray()
                _close_worker_proc(proc)
                raise
            except OSError:
                line = b""
            if line:
                try:
                    code, payload = parse_batch_reply_line(
                        line, error_message="native parser returned malformed JSON",
                    )
                except ValueError:
                    _DEV_WORKER["proc"] = None
                    _DEV_WORKER["executable"] = None
                    _DEV_WORKER["buf"] = bytearray()
                    _close_worker_proc(proc)
                    raise
                return code, payload, stderr_bytes
            _DEV_WORKER["proc"] = None
            _DEV_WORKER["executable"] = None
            _DEV_WORKER["buf"] = bytearray()
            _close_worker_proc(proc)
            if attempt == 1:
                if stderr_bytes:
                    return 1, b"{}", stderr_bytes
                raise RuntimeError("native parser batch worker terminated without a response")
        raise RuntimeError("native parser batch worker failed")


def parse_source(compiled: Build, source: bytes, *, surface: bool = False, layout: bool = False) -> dict[str, Json]:
    """Decode one complete native response, refusing any unsuccessful process."""
    if len(source) > MAX_SOURCE_BYTES:
        raise HoldFastError("limit", 1, 1, f"source exceeds {MAX_SOURCE_BYTES} bytes")
    _verify_executable(compiled)
    if (
        sys.platform != "win32"
        and _subprocess_unpatched()
        and compiled.receipt.get("scope") == "holdfast-syntax-only-development-parser"
    ):
        returncode, stdout, stderr = _parse_batch(compiled, source, surface=surface, layout=layout)
        return decode_response(source, returncode, stdout, stderr, surface=surface or layout, layout=layout)
    try:
        arguments = [str(compiled.executable)]
        if layout:
            arguments.append("--surface-layout")
        elif surface:
            arguments.append("--surface")
        done = subprocess.run(arguments, input=source, capture_output=True,
                              timeout=PARSE_TIMEOUT, check=False)
    except subprocess.TimeoutExpired as error:
        raise HoldFastError("limit", 1, 1, f"parser exceeded {PARSE_TIMEOUT} seconds") from error
    return decode_response(source, done.returncode, done.stdout, done.stderr, surface=surface or layout, layout=layout)


def _body(result: dict[str, Json]) -> dict[str, Json]:
    ast = _object(result["ast"], "file")
    functions = ast.get("declarations")
    if not isinstance(functions, list) or not functions:
        raise ValueError("fixture has no function")
    function = _object(functions[0], "function")
    body = _object(function.get("body"), "block")
    terminal = _object(body.get("exit"), "return")
    return _object(terminal.get("value"), "expression")


def _shape(value: dict[str, Json]) -> Json:
    kind = value.get("kind")
    if kind in {"nat", "bool"}:
        return [kind, value.get("value")]
    if kind == "binary":
        operator = _object(value.get("operator"), "operator")
        return [operator.get("text"), _shape(_object(value.get("left"), "left expression")),
                _shape(_object(value.get("right"), "right expression"))]
    if kind == "unary":
        operator = _object(value.get("operator"), "unary operator")
        return [operator.get("text"), _shape(_object(value.get("value"), "unary expression"))]
    if kind == "group":
        return ["group", _shape(_object(value.get("value"), "group expression"))]
    raise ValueError(f"unexpected fixture expression: {kind}")


def _precedence_oracle() -> dict[str, Json]:
    # Authored independently of grammar actions by the contract reviewer.
    return {"kind": "file", "span": [0, 46], "name": {"text": "M", "span": [7, 8]},
            "declarations": [{"kind": "function", "span": [10, 46],
                           "name": {"text": "F", "span": [21, 22]},
                           "result": {"kind": "type", "span": [17, 20], "name": "Nat"},
                           "parameters": [],
                           "body": {"kind": "block", "span": [25, 46], "bindings": [],
                                    "exit": {"kind": "return", "span": [27, 44],
                                             "value": {"kind": "binary", "span": [34, 43],
                                                       "operator": {"text": "+", "span": [36, 37]},
                                                       "left": {"kind": "nat", "span": [34, 35], "value": "1"},
                                                       "right": {"kind": "binary", "span": [38, 43],
                                                                 "operator": {"text": "*", "span": [40, 41]},
                                                                 "left": {"kind": "nat", "span": [38, 39], "value": "2"},
                                                                 "right": {"kind": "nat", "span": [42, 43], "value": "3"}}}}}}]}


def _concise_fixture(compiled: Build) -> str:
    source = (b"// caf\xc3\xa9\r\nmodule Concise;\r\n"
              b"public Nat Add(Nat left, Nat right,) => left + right;\r\n"
              b"public Nat Use() => Add(1, 2,);")
    result = parse_source(compiled, source)
    functions = _object(result["ast"], "concise pure file").get("declarations")
    if not isinstance(functions, list) or len(functions) != 2:
        raise ValueError("concise pure syntax changed declaration boundaries")
    add, use = [_object(value, "concise pure function") for value in functions]
    for function, spelling in ((add, b"=> left + right;"), (use, b"=> Add(1, 2,);")):
        body = _object(function.get("body"), "concise pure body")
        start = source.index(spelling)
        if set(body) != {"kind", "span", "value"} or body.get("kind") != "expression_body" or body.get("span") != [start, start + len(spelling)]:
            raise ValueError("concise pure body lost its value or exact arrow/semicolon span")
    parameters = add.get("parameters")
    if not isinstance(parameters, list) or len(parameters) != 2:
        raise ValueError("pure trailing comma fabricated a parameter")
    for raw, spelling in zip(parameters, (b"Nat left", b"Nat right"), strict=True):
        parameter = _object(raw, "concise pure parameter")
        start = source.index(spelling)
        if parameter.get("span") != [start, start + len(spelling)]:
            raise ValueError("pure trailing comma entered a parameter span")
    call = _object(_object(use.get("body"), "concise call body").get("value"), "concise pure call")
    arguments = call.get("arguments")
    if call.get("kind") != "call" or not isinstance(arguments, list) or len(arguments) != 2:
        raise ValueError("pure trailing comma fabricated an argument or changed call syntax")
    for spelling in (b"F(,)", b"F(Nat x,,)", b"F() => Add(1,,)"):
        invalid = b"module M; public Nat " + spelling
        invalid += b";" if b"=>" in spelling else b" => 0;"
        try:
            parse_source(compiled, invalid)
        except HoldFastError as error:
            if error.kind != "syntax":
                raise ValueError("malformed concise pure list has wrong refusal") from error
        else:
            raise ValueError("malformed concise pure list unexpectedly parsed")
    return "concise-expression-body-and-lists"


def _constant_callable_fixture(compiled: Build) -> str:
    source = (b"// caf\xc3\xa9\r\nmodule Static;\r\n"
              b"public const Nat Square(Nat value) => value * value;\r\n"
              b"public Nat Scale(const Nat factor, Nat value) { "
              b"const Nat multiplier = Square(factor); return multiplier * value; }\r\n"
              b"public const Nat Answer = Square(4);")
    result = parse_source(compiled, source)
    declarations = _object(result["ast"], "constant callable file").get("declarations")
    if not isinstance(declarations, list) or len(declarations) != 3:
        raise ValueError("constant function changed pure declaration boundaries")
    square, scale, answer = [_object(value, "constant callable declaration") for value in declarations]
    if (square.get("kind") != "function" or square.get("const") is not True
            or scale.get("kind") != "function" or "const" in scale
            or answer.get("kind") != "constant" or "const" in answer):
        raise ValueError("pure constant function/value roles differ from the independent oracle")
    parameters = scale.get("parameters")
    if not isinstance(parameters, list) or len(parameters) != 2:
        raise ValueError("static parameter changed pure callable arity")
    factor, value = [_object(parameter, "pure constant parameter") for parameter in parameters]
    start = source.index(b"const Nat factor")
    if (factor.get("const") is not True or "const" in value
            or factor.get("span") != [start, start + len(b"const Nat factor")]
            or _object(factor.get("type"), "static parameter type").get("span") != [start + 6, start + 9]):
        raise ValueError("pure required-static parameter qualifier or byte spans differ")
    square_parameters = square.get("parameters")
    if (not isinstance(square_parameters, list) or len(square_parameters) != 1
            or "const" in _object(square_parameters[0], "ordinary constant-function input")):
        raise ValueError("constant function incorrectly requires all inputs statically")
    return "compositional-constant-function-and-parameter-roles"


def _typed_local_fixture(compiled: Build) -> str:
    source = (b"// caf\xc3\xa9\r\nmodule Typed;\r\npublic Nat F() { "
              b"let inferred = 1; let Nat annotated = inferred; "
              b"let Nat second = annotated; let bool ready = true; let bool selected = ready; return second; }")
    parsed = parse_source(compiled, source)
    tree = _object(parsed.get("ast"), "typed local file")
    declarations = tree.get("declarations")
    if not isinstance(declarations, list) or len(declarations) != 1:
        raise ValueError("typed local fixture changed pure declaration boundaries")
    function = _object(declarations[0], "typed local function")
    bindings = _object(function.get("body"), "typed local block").get("bindings")
    if not isinstance(bindings, list) or len(bindings) != 5:
        raise ValueError("typed local syntax lost an immutable binding")
    for binding, kind, type_name, spelling in zip(bindings,
            ("let", "let", "let", "let", "let"),
            (None, "Nat", "Nat", "bool", "bool"),
            (b"let inferred = 1;", b"let Nat annotated = inferred;", b"let Nat second = annotated;",
             b"let bool ready = true;", b"let bool selected = ready;"), strict=True):
        node = _object(binding, "typed local binding")
        start = source.index(spelling)
        if node.get("kind") != kind or node.get("span") != [start, start + len(spelling)]:
            raise ValueError("typed local kind or original UTF-8 byte span differs")
        if type_name is None:
            if "type" in node:
                raise ValueError("unannotated pure let acquired a fabricated annotation")
        elif _object(node.get("type"), "pure local annotation").get("name") != type_name:
            raise ValueError("pure local annotation changed its scalar type")
    try:
        parse_source(compiled, b"module M; public Nat F() { Nat bare = 1; return bare; }")
    except HoldFastError as error:
        if error.kind != "syntax" or "let" not in error.message or "var" not in error.message:
            raise ValueError("bare local declaration did not produce let/var syntax refusal") from error
    else:
        raise ValueError("bare local declaration unexpectedly parsed in pure grammar")
    # Mismatched types are valid syntax for the existing semantic consumer.
    parse_source(compiled, b"module M; public Nat F() { let bool wrong = 1; return wrong; }")
    return "typed-immutable-locals-and-original-byte-spans"


def _extended_expression_fixture(compiled: Build) -> str:
    for newline in (b"\n", b"\r\n", b"\r"):
        source = (b"// caf\xc3\xa9" + newline + b"module M; public bool F() { return ! // hidden !"
                  + newline + b" !false || 3 >= 2 && true; }")
        first = source.index(b"!", source.index(b"return"))
        second = source.index(b"!false")
        false = second + 1
        disjunction = source.index(b"||")
        three = source.index(b"3 >=")
        comparison = source.index(b">=")
        two = source.index(b"2 &&")
        conjunction = source.index(b"&&")
        true = source.index(b"true;")
        expected: dict[str, Json] = {
            "kind": "binary", "span": [first, true + 4],
            "operator": {"text": "||", "span": [disjunction, disjunction + 2]},
            "left": {"kind": "unary", "span": [first, false + 5],
                     "operator": {"text": "!", "span": [first, first + 1]},
                     "value": {"kind": "unary", "span": [second, false + 5],
                               "operator": {"text": "!", "span": [second, second + 1]},
                               "value": {"kind": "bool", "span": [false, false + 5], "value": False}}},
            "right": {"kind": "binary", "span": [three, true + 4],
                      "operator": {"text": "&&", "span": [conjunction, conjunction + 2]},
                      "left": {"kind": "binary", "span": [three, two + 1],
                               "operator": {"text": ">=", "span": [comparison, comparison + 2]},
                               "left": {"kind": "nat", "span": [three, three + 1], "value": "3"},
                               "right": {"kind": "nat", "span": [two, two + 1], "value": "2"}},
                      "right": {"kind": "bool", "span": [true, true + 4], "value": True}},
        }
        if _body(parse_source(compiled, source)) != expected:
            raise ValueError("extended expression precedence or original operator/operand byte spans differ")
        source = (b"// caf\xc3\xa9" + newline + b"module M; public Nat F() { return 20 / // / %"
                  + newline + b"3 % 2 * 4; }")
        first = source.index(b"20 /")
        divide = first + 3
        three = source.index(b"3 %")
        modulo = three + 2
        two = source.index(b"2 *")
        multiply = two + 2
        four = source.index(b"4;")
        expected = {
            "kind": "binary", "span": [first, four + 1],
            "operator": {"text": "*", "span": [multiply, multiply + 1]},
            "left": {"kind": "binary", "span": [first, two + 1],
                     "operator": {"text": "%", "span": [modulo, modulo + 1]},
                     "left": {"kind": "binary", "span": [first, three + 1],
                              "operator": {"text": "/", "span": [divide, divide + 1]},
                              "left": {"kind": "nat", "span": [first, first + 2], "value": "20"},
                              "right": {"kind": "nat", "span": [three, three + 1], "value": "3"}},
                     "right": {"kind": "nat", "span": [two, two + 1], "value": "2"}},
            "right": {"kind": "nat", "span": [four, four + 1], "value": "4"},
        }
        if _body(parse_source(compiled, source)) != expected:
            raise ValueError("division/remainder associativity or original operator/operand byte spans differ")
    return "extended-expression-precedence-and-original-byte-spans"


def _fixtures(compiled: Build) -> list[str]:
    """Expected pure trees selected by the independent grammar reviewer."""
    passed: list[str] = [_concise_fixture(compiled), _constant_callable_fixture(compiled),
                        _typed_local_fixture(compiled), _extended_expression_fixture(compiled)]
    prefix = b"module M; public Nat F() { return "
    expressions: tuple[tuple[bytes, Json], ...] = (
        (b"1 + 2 * 3", ["+", ["nat", "1"], ["*", ["nat", "2"], ["nat", "3"]]]),
        (b"1 * 2 * 3", ["*", ["*", ["nat", "1"], ["nat", "2"]], ["nat", "3"]]),
        (b"1 + 2 + 3", ["+", ["+", ["nat", "1"], ["nat", "2"]], ["nat", "3"]]),
        (b"9 - 3 - 2", ["-", ["-", ["nat", "9"], ["nat", "3"]], ["nat", "2"]]),
        (b"20 / 3 * 2", ["*", ["/", ["nat", "20"], ["nat", "3"]], ["nat", "2"]]),
        (b"20 % 6 * 2", ["*", ["%", ["nat", "20"], ["nat", "6"]], ["nat", "2"]]),
        (b"30 / 4 % 3", ["%", ["/", ["nat", "30"], ["nat", "4"]], ["nat", "3"]]),
        (b"2 + 3 * 4 - 5", ["-", ["+", ["nat", "2"], ["*", ["nat", "3"], ["nat", "4"]]], ["nat", "5"]]),
        (b"!false == true", ["==", ["!", ["bool", False]], ["bool", True]]),
        (b"!false || false && false", ["||", ["!", ["bool", False]], ["&&", ["bool", False], ["bool", False]]]),
        (b"!!true", ["!", ["!", ["bool", True]]]),
        (b"(1 + 2) * 3", ["*", ["group", ["+", ["nat", "1"], ["nat", "2"]]], ["nat", "3"]]),
        (b"0001", ["nat", "0001"]),
        (b"0_001", ["nat", "0_001"]),
        (b"1_024 + 2_048", ["+", ["nat", "1_024"], ["nat", "2_048"]]),
        (b"_".join([b"9"] * 256), ["nat", "_".join(["9"] * 256)]),
    )
    expressions += tuple((b"3 " + operator + b" 4", cast("Json", [operator.decode(), ["nat", "3"], ["nat", "4"]]))
                         for operator in (b"==", b"!=", b"<", b"<=", b">", b">="))
    for expression, expected in expressions:
        result = parse_source(compiled, prefix + expression + b"; }")
        if _shape(_body(result)) != expected:
            raise ValueError(f"independent AST oracle failed: {expression!r}")
        passed.append(f"expression:{expression.decode()}")
    source = prefix + b"1 + 2 * 3; }"
    baseline = parse_source(compiled, source)
    if baseline["ast"] != _precedence_oracle():
        raise ValueError("complete independent AST/span oracle differs")
    trailing = parse_source(compiled, source + b" \n//comment")
    if baseline["ast"] != trailing["ast"] or baseline["source_sha256"] == trailing["source_sha256"]:
        raise ValueError("trivia changed the AST or failed to change the source binding")
    passed.append("independent-spans-and-trivia")
    utf8 = b"// caf\xc3\xa9\r\nmodule M;\r\npublic Nat F() { return 0001; }\r\n"
    located = parse_source(compiled, utf8)
    if _object(located["ast"], "file").get("span") != [10, 52] or _body(located).get("span") != [45, 49]:
        raise ValueError("UTF-8/CRLF original-byte spans differ")
    passed.append("original-byte-spans")
    source = b"module M; public Nat as(Nat as) { return as; }"
    pure_identifier = parse_source(compiled, source)
    functions = _object(pure_identifier["ast"], "pure file").get("declarations")
    if not isinstance(functions, list) or len(functions) != 1:
        raise ValueError("pure surface-keyword regression lost its function")
    function = _object(functions[0], "pure function named as")
    parameters = function.get("parameters")
    if (_object(function.get("name"), "pure function name").get("text") != "as"
            or not isinstance(parameters, list) or len(parameters) != 1
            or _object(_object(parameters[0], "pure parameter").get("name"), "pure parameter name").get("text") != "as"
            or _object(_body(pure_identifier).get("name"), "pure returned identifier").get("text") != "as"):
        raise ValueError("surface match keyword changed a pure identifier")
    passed.append("pure-identifier-as")
    for word in (b"null", b"lifts", b"open", b"trait", b"operation"):
        source = b"module M; public Nat " + word + b"(Nat " + word + b") { return " + word + b"; }"
        pure_identifier = parse_source(compiled, source)
        functions = _object(pure_identifier["ast"], "pure file").get("declarations")
        if not isinstance(functions, list) or len(functions) != 1:
            raise ValueError("surface-only reserved word changed pure declaration syntax")
        function = _object(functions[0], "pure reserved-word identifier")
        parameters = function.get("parameters")
        if (_object(function.get("name"), "pure function name").get("text") != word.decode()
                or not isinstance(parameters, list) or len(parameters) != 1
                or _object(_object(parameters[0], "pure parameter").get("name"), "pure parameter name").get("text") != word.decode()
                or _object(_body(pure_identifier).get("name"), "pure returned identifier").get("text") != word.decode()):
            raise ValueError("surface-only reserved word changed pure identifier AST roles")
        passed.append("pure-identifier-" + word.decode())
    # These are deliberately invalid programs accepted as syntax.
    for source in (
            b"module M; public Nat F() { return true + 1; } public Nat F() { return missing; }",
            b"module M; public Nat F() { if (true) { let x = 1; return x; } else { let x = 2; return x; } }",
            b"module M; public Nat F(Nat x, bool b) { return F(x, b); }",
            b"module M; public Nat interface(Nat state) { let register = state; return register; }"):
        parse_source(compiled, source)
    passed.append("syntax-only-and-scoped-constructs")
    for newline in (b"\n", b"\r\n", b"\r"):
        source = b"// caf\xc3\xa9" + newline + b"module M;" + newline + b"public Nat F() { return @; }"
        try:
            parse_source(compiled, source)
        except HoldFastError as error:
            if (error.kind, error.line, error.column) != ("syntax", 3, 25):
                raise ValueError("newline/UTF-8 diagnostic position differs") from error
        else:
            raise ValueError("invalid character unexpectedly parsed")
    passed.append("newline-and-utf8-comment-positions")
    refusals = (
        (b"module M; public const const Nat F() => 1;", "syntax"),
        (b"module M; public Nat F(const const Nat value) => value;", "syntax"),
        (b"module M; public Nat F(const Nat) => 0;", "syntax"),
        (b"", "syntax"), (b"module M;", "syntax"),
        (prefix + b"1; } garbage", "syntax"),
        (prefix + b"1 == 2 <= 3; }", "syntax"),
        (prefix + b"1 < 2 < 3; }", "syntax"),
        (prefix + b"-1; }", "syntax"),
        (prefix + b"1--2; }", "syntax"),
        (prefix + b"true &&; }", "syntax"),
        (prefix + b"!; }", "syntax"),
        (prefix + b"true | false; }", "syntax"),
        (prefix + b"8 /; }", "syntax"),
        (prefix + b"8 %; }", "syntax"),
        (prefix + b"8 / / 2; }", "syntax"),
        (prefix + b"8 %% 2; }", "syntax"),
        (prefix + b"8 /= 2; }", "syntax"),
        (prefix + b"8 %= 2; }", "syntax"),
        (prefix + b"1; return 2; }", "syntax"),
        (prefix + b"1", "syntax"),
        (prefix + b"await 1; }", "unsupported"),
        (b"module M; public Nat out() => 0;", "unsupported"),
        (b"// invalid \xff\n" + source, "encoding"),
        (b"\xef\xbb\xbf" + source, "encoding"),
        (prefix + b"9" * 257 + b"; }", "limit"),
        (prefix + b"_".join([b"9"] * 257) + b"; }", "limit"),
        (prefix + b"1__0; }", "syntax"),
        (prefix + b"1_; }", "syntax"),
        (prefix + b"1_Nat; }", "syntax"),
        (prefix + b"(" * 2000 + b"0" + b")" * 2000 + b"; }", "limit"),
        (prefix + b" + ".join([b"1"] * 2000) + b"; }", "limit"),
        (prefix + b"!" * 2000 + b"true; }", "limit"),
        (b"module M; public Nat F() { " + b"let x = 1; " * 1000 + b"return 0; }", "limit"),
        (b" " * (MAX_SOURCE_BYTES + 1), "limit"),
    )
    for number, (source, kind) in enumerate(refusals):
        try:
            parse_source(compiled, source)
        except HoldFastError as error:
            if error.kind != kind:
                raise ValueError(f"refusal fixture {number}: expected {kind}, got {error.kind}") from error
        else:
            raise ValueError(f"refusal fixture {number} unexpectedly parsed")
        passed.append(f"refusal:{number}:{kind}")
    return passed


def _surface_layout_fixture(compiled: Build) -> str:
    lexemes = [b"module", b"M", b";", b"/* outer /* inner */ */", b"public", b"definition",
               b"Text", b"F", b"(", b")", b"=>", b'""" a // b """', b";", "// π".encode()]
    source = b"  ".join(lexemes) + b"\r\n"
    layout = parse_source(compiled, source, layout=True)
    if [source[a:b] for a, b in cast("Sequence[Sequence[int]]", layout.pop("layout"))] != lexemes:
        raise ValueError("layout splits literal or comment content, or loses original token spelling")
    if layout != parse_source(compiled, source, surface=True):
        raise ValueError("formatting and ordinary surface parsing differ")
    return "original-surface-tokens-and-comments"


def qualify(root: Path) -> dict[str, object]:
    latest = _work_root(root) / "qualification.json"
    latest.unlink(missing_ok=True)
    if cast("object", build) is not _UNPATCHED_BUILD:
        first = build(root)
        second = build(root)
    else:
        directory = _work_root(root)
        with _file_lock(directory / "build.lock", timeout=1):
            tools = _toolchain(root)
            outputs = [Path(tempfile.mkdtemp(prefix="build-", dir=directory)) for _ in range(2)]
            with ThreadPoolExecutor(max_workers=2) as pool:
                first, second = list(pool.map(lambda out: _compile(root, out, tools), outputs))
    first_outputs = cast("dict[str, str]", first.receipt["generated_sha256"])
    second_outputs = cast("dict[str, str]", second.receipt["generated_sha256"])
    if first.receipt["inputs"] != second.receipt["inputs"] or first.receipt["toolchain"] != second.receipt["toolchain"]:
        raise ValueError("qualification inputs changed between fresh builds")
    if any(first_outputs[name] != second_outputs[name] for name in GENERATED):
        raise ValueError("fresh parser regeneration changed generated bytes")
    passed = _fixtures(first)
    surface_passed = holdfast_surface.qualify(lambda source: parse_source(first, source, surface=True))
    surface_passed.append(_surface_layout_fixture(first))
    example_path = root / "examples/pure.hf"
    example = read_source(example_path)
    parse_source(first, example)
    surface_path = root / SURFACE_FIXTURE
    surface_fixture = read_source(surface_path)
    parse_source(first, surface_fixture, surface=True)
    constant_path = root / "examples/constants.hf"
    constant_example = read_source(constant_path)
    parse_source(first, constant_example)
    parse_source(first, constant_example, surface=True)
    expression_path = root / "examples/expressions.hf"
    expression_example = read_source(expression_path)
    parse_source(first, expression_example)
    parse_source(first, expression_example, surface=True)
    if _inputs(root) != first.receipt["inputs"]:
        raise ValueError("qualification inputs changed after fixtures")
    if _toolchain(root) != first.receipt["toolchain"]:
        raise ValueError("qualification toolchain changed after fixtures")
    for compiled in (first, second):
        outputs = cast("dict[str, str]", compiled.receipt["generated_sha256"])
        if any(_digest(compiled.directory / name) != outputs[name]
               for name in (*GENERATED, "holdfast-parser")):
            raise ValueError("parser generated output changed after fixtures")
    if read_source(example_path) != example:
        raise ValueError("example changed during qualification")
    if read_source(surface_path) != surface_fixture:
        raise ValueError("surface fixture changed during qualification")
    if read_source(constant_path) != constant_example:
        raise ValueError("constant example changed during qualification")
    if read_source(expression_path) != expression_example:
        raise ValueError("expression example changed during qualification")
    report: dict[str, object] = {
        "schema": 1, "scope": "holdfast-syntax-only-development-parser",
        "status": "passed", "checked_parser": False,
        "build": first.receipt, "regeneration": second.receipt,
        "example": {"path": "examples/pure.hf",
                    "source_sha256": hashlib.sha256(example).hexdigest()},
        "constant_example": {"path": "examples/constants.hf",
                             "source_sha256": hashlib.sha256(constant_example).hexdigest()},
        "expression_example": {"path": "examples/expressions.hf",
                               "source_sha256": hashlib.sha256(expression_example).hexdigest()},
        "fixtures": [*passed, "authored-example", "authored-compositional-constants", "authored-extended-expressions"],
        "syntax_entries": {
            "pure": {"schema": 1, "status": "passed"},
            "surface": {"schema": 2, "status": "passed", "fixtures": surface_passed,
                        "example": {"path": SURFACE_FIXTURE,
                                    "source_sha256": hashlib.sha256(surface_fixture).hexdigest()}},
        },
    }
    publish_report(first.directory / "qualification.json", report)
    publish_report(latest, report)
    return report
