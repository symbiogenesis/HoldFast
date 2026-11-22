# SPDX-License-Identifier: Apache-2.0
"""Emit one pure Boolean ES module after exhaustive execution and Gallina replay."""

import hashlib
import itertools
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

from toolchain import _translate, ast, gallina_module_name, parse_module, proofenv
from toolchain.atomic import atomic_path
from toolchain.hashing import file_sha256
from toolchain.parser import read_source

MAX_PARAMETERS = 8
MAX_NODES = 128
MAX_JS_BYTES = 16_384
NODE_SHA256 = "1ea16f5e8d590ca819f1db81e61a6bc4c8e7d8b69776c9236f8ebbf717113225"
_OPERATORS = {"==": "===", "!=": "!==", "&&": "&&", "||": "||"}

# The independent engine enumerates tuples in binary order, including the empty tuple.
_ENGINE = """import entry from './output.mjs';
const arity = Number(process.argv[2]);
if (entry.length !== arity) throw Error('entry arity');
const rows = [];
for (let mask = 0; mask < 2 ** arity; mask++) {
    const bits = Array.from({length: arity}, (_, i) => Boolean(mask & (1 << (arity - i - 1))));
    const value = entry(...bits);
    if (typeof value !== 'boolean') throw Error('entry returned a non-Boolean');
    rows.push([bits.map(Number).join(''), value]);
}
const args = Array(arity).fill(false);
if (entry(...args, false) !== undefined || (arity && entry(...args.slice(1)) !== undefined))
    throw Error('accepted wrong arity');
for (let i = 0; i < arity; i++) {
    for (const invalid of [0, 'true', null, undefined, Object(true)]) {
        args[i] = invalid;
        if (entry(...args) !== undefined) throw Error('accepted a non-Boolean');
    }
    args[i] = false;
}
process.stdout.write(JSON.stringify(rows));
"""


def _refuse(site: ast.Site, message: str) -> ast.VelaError:
    return ast.VelaError("web-output", site.line, site.column, message)


def _emit(entry: ast.Function, source_hash: str) -> bytes:
    if entry.result != "bool" or any(value_type != "bool" for _, value_type in entry.parameters):
        raise _refuse(entry.name.site, "web entry requires primitive bool parameters and result")
    if entry.const_parameters or entry.is_const:
        raise _refuse(entry.name.site, "web entry requires an ordinary function without static parameters")
    arity = len(entry.parameters)
    if arity > MAX_PARAMETERS:
        raise _refuse(entry.name.site, f"web entry exceeds {MAX_PARAMETERS} Boolean parameters")
    if entry.body.bindings or not isinstance(entry.body.terminal, ast.Return):
        raise _refuse(entry.body.site, "web entry requires a single return expression")
    parameters = {name.text: f"p{i}" for i, (name, _) in enumerate(entry.parameters)}
    nodes = 0

    def render(node: ast.Expression) -> str:
        nonlocal nodes
        nodes += 1
        if nodes > MAX_NODES:
            raise _refuse(node.site, f"web expression exceeds {MAX_NODES} nodes")
        if node.kind == "bool":
            return "true" if node.value else "false"
        if node.kind == "name" and isinstance(node.value, str) and node.value in parameters:
            return parameters[node.value]
        if node.kind == "group":
            return render(node.children[0])
        if node.kind == "unary" and node.value == "!":
            return f"(!{render(node.children[0])})"
        if node.kind == "binary" and isinstance(node.value, str) and node.value in _OPERATORS:
            left, right = node.children
            return f"({render(left)} {_OPERATORS[node.value]} {render(right)})"
        raise _refuse(node.site, "web expression permits only Boolean literals, parameters and Boolean operators")

    expression = render(entry.body.terminal.value)
    guards = [f"arguments.length !== {arity}", *(f"typeof {p} !== 'boolean'" for p in parameters.values())]
    code = (f"// Vela source SHA-256 {source_hash}, entry {entry.name.text}\n"
            f"export default function({', '.join(parameters.values())}) {{\n"
            f"    if ({' || '.join(guards)}) return undefined;\n"
            f"    return {expression};\n}}\n").encode("ascii")
    if len(code) > MAX_JS_BYTES:
        raise _refuse(entry.name.site, f"web output exceeds {MAX_JS_BYTES} bytes")
    return code


def _run(command: list[str], directory: Path, *, timeout: int) -> bytes:
    process = subprocess.run(command, cwd=directory, stdin=subprocess.DEVNULL, capture_output=True,
                             env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"}, timeout=timeout, check=False)
    if process.returncode:
        detail = (process.stderr or process.stdout)[-2048:].decode("utf-8", errors="replace")
        raise ValueError(f"{Path(command[0]).name} refused web correspondence: {detail.strip()}")
    return process.stdout


def _equations(observations: bytes, subject: str, arity: int) -> tuple[str, list[bool]]:
    if len(observations) > MAX_JS_BYTES:
        raise ValueError("web engine observations exceed the byte budget")
    rows = json.loads(observations)
    if not isinstance(rows, list) or len(rows) != 2 ** arity:
        raise ValueError("web engine returned an incomplete or oversized truth table")
    equations: list[str] = []
    results: list[bool] = []
    for i, (bits, row) in enumerate(zip(itertools.product((False, True), repeat=arity), rows, strict=True)):
        key = "".join("1" if bit else "0" for bit in bits)
        if not isinstance(row, list) or len(row) != 2 or row[0] != key or type(row[1]) is not bool:
            raise ValueError("web engine returned an invalid observation or input tuple")
        arguments = " ".join("true" if bit else "false" for bit in bits)
        result = row[1]
        results.append(result)
        equations.append(f"Example web_case_{i} : {subject} {arguments} = {'true' if result else 'false'} := eq_refl.")
    return "\n".join(equations), results


def _qualify(code: bytes, gallina: str, subject: str, arity: int) -> list[bool]:
    found = shutil.which("node")
    if found is None or file_sha256(Path(found)) != NODE_SHA256:
        raise ValueError("web qualification needs the pinned Node.js 22.22.1 Ubuntu ARM64 executable")
    node = str(Path(found).resolve())
    prover_bin = proofenv.opam_root() / proofenv.ROCQ_SWITCH / "bin"
    with tempfile.TemporaryDirectory(prefix="vela-web-") as tmp:
        directory = Path(tmp)
        (directory / "output.mjs").write_bytes(code)
        (directory / "observe.mjs").write_text(_ENGINE, encoding="ascii")
        observed = _run([node, "--max-old-space-size=32", "observe.mjs", str(arity)], directory, timeout=10)
        equations, results = _equations(observed, subject, arity)
        (directory / "Web.v").write_text(f"{gallina}\n{equations}\n", encoding="ascii")
        _run([str(prover_bin / "rocq"), "c", "-q", "-Q", ".", "VelaWeb", "Web.v"], directory, timeout=30)
        _run([str(prover_bin / "rocqchk"), "-silent", "-Q", ".", "VelaWeb", "VelaWeb.Web"],
             directory, timeout=30)
        if (directory / "output.mjs").read_bytes() != code or file_sha256(Path(node)) != NODE_SHA256:
            raise ValueError("web output or execution engine changed during replay")
    return results


def publish(source_path: Path, entry_name: str, output: Path) -> dict[str, object]:
    def check_paths() -> None:
        if source_path.is_symlink() or not source_path.is_file():
            raise ValueError("web source must be a regular file")
        if output.resolve() == source_path.resolve() or (output.exists() and output.samefile(source_path)):
            raise ValueError("web output aliases the source")
        if output.suffix != ".mjs" or output.is_symlink() or (output.exists() and not output.is_file()):
            raise ValueError("web output must be a regular .mjs destination")

    check_paths()
    source = read_source(source_path)
    module = parse_module(source)
    translated = _translate(source, module)
    entry = next((decl for decl in module.declarations if decl.name.text == entry_name), None)
    if not isinstance(entry, ast.Function):
        raise _refuse(module.name.site, "select a declared public function for web output")
    source_hash = hashlib.sha256(source).hexdigest()
    code = _emit(entry, source_hash)
    subject = f"{gallina_module_name(module.name.text)}.f_{entry.name.text}"
    results = _qualify(code, translated.gallina, subject, len(entry.parameters))
    with atomic_path(output) as pending:
        pending.write_bytes(code)
        check_paths()
        if read_source(source_path) != source:
            raise ValueError("web source changed during qualification")
    return {"function": entry_name, "source_sha256": source_hash, "output_sha256": hashlib.sha256(code).hexdigest(),
            "gallina_sha256": hashlib.sha256(translated.gallina.encode("ascii")).hexdigest(),
            "node_sha256": NODE_SHA256, "rocq_switch": proofenv.ROCQ_SWITCH, "boolean_results": results}
