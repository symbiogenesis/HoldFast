# SPDX-License-Identifier: Apache-2.0
"""Parse HoldFast, elaborate mathematical terms, or qualify development tooling."""

import argparse
import contextlib
import json
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Generator
from itertools import pairwise
from pathlib import Path

from filelock import Timeout

from toolchain import (
    HoldFastError,
    bsp,
    bsp_client,
    contract_diff,
    env,
    gallina_source_map,
    graded_source,
    mathematical_authoring,
    mathematical_preview,
    packages,
    remarks_reader,
    scip,
    scip_reader,
    simulator_debug,
    simulator_debug_check,
    solver_ledger,
    source_map_check,
    web_output,
    web_output_check,
)
from toolchain import (
    elaboration_check as holdfast_elaboration_check,
)
from toolchain import (
    first_slice as holdfast_first_slice,
)
from toolchain import (
    mathematical as holdfast_mathematical,
)
from toolchain import (
    migration as holdfast_migration,
)
from toolchain import (
    parser as holdfast_parser,
)
from toolchain import (
    parser_checked as holdfast_parser_checked,
)
from toolchain import (
    syntax_campaigns as holdfast_syntax_campaigns,
)
from toolchain.ast import MAX_SOURCE_BYTES
from toolchain.atomic import atomic_path
from toolchain.authoring import MATHEMATICAL_LINT_CODES, OPT_IN_MATHEMATICAL_LINTS, Finding
from toolchain.cli import report_findings
from toolchain.elaborate import check_client_upgrade
from toolchain.elaborate import elaborate as elaborate_source
from toolchain.hashing import file_sha256
from toolchain.source_file import check_destination, ensure_unchanged, read_source, rewrite_source


def _packet_bytes(argument: str) -> bytes:
    try:
        packet = bytes.fromhex(argument)
    except ValueError as error:
        raise argparse.ArgumentTypeError("supply complete hexadecimal bytes, for example '56 02 6b 01 11 22'") from error
    if len(packet) > 8:
        raise argparse.ArgumentTypeError("the packet example accepts at most eight bytes")
    return packet


def _compile_bridge(directory: Path, compiler: str, options: list[str],
                    source: Path, executable: Path, *, export: bool) -> None:
    arguments = [compiler, *options, str(source), "-o", str(executable)]
    build = subprocess.run(arguments, cwd=directory, capture_output=True, text=True, check=False, timeout=30)
    if build.returncode:
        raise RuntimeError(f"packet example C build failed: {build.stderr.strip()}")
    if export:
        row = {"directory": str(directory), "arguments": arguments, "file": str(source), "output": str(executable)}
        with atomic_path(directory / "compile_commands.json") as pending:
            pending.write_text(json.dumps([row], indent=2) + "\n", encoding="utf-8")


@contextlib.contextmanager
def _packet_directory(destination: Path | None) -> Generator[Path]:
    if destination is None:
        with tempfile.TemporaryDirectory() as tmp:
            yield Path(tmp).resolve()
        return
    destination.mkdir(mode=0o700)
    directory = destination.resolve()
    try:
        yield directory
    except BaseException:
        for name in ("compile_commands.json", "packet-example", "packet.c"):
            with contextlib.suppress(OSError):
                (directory / name).unlink(missing_ok=True)
        with contextlib.suppress(OSError):
            directory.rmdir()
        raise


def _packet_example(root: Path, source_path: Path, packet: bytes, *, bridge_dir: Path | None = None) -> str:
    source = holdfast_parser.read_source(source_path)
    with holdfast_parser.cached_build(root) as compiled:
        parsed = holdfast_parser.parse_source(compiled, source, surface=True)
    checked = elaborate_source(source, parsed)
    obligations = solver_ledger.ledger(checked.gallina)
    if obligations:
        first = obligations[0]
        raise HoldFastError("proof", first.line, first.column, f"unproved packet contract: {first.export}")
    generated, _ = holdfast_first_slice.lower_to_c(source, parsed, checked=checked)
    compiler = shutil.which("cc")
    if compiler is None:
        raise RuntimeError("packet example requires the C11 compiler cc")
    with _packet_directory(bridge_dir) as directory:
        (directory / "packet.c").write_text(generated, encoding="utf-8")
        driver = root / "tools/toolchain/packet_example.c"
        executable = directory / "packet-example"
        _compile_bridge(directory, compiler, ["-std=c11", "-I", str(directory)], driver, executable,
                        export=bridge_dir is not None)
        run = subprocess.run([str(executable)], input=packet, capture_output=True, check=False, timeout=5)
        if run.returncode:
            raise RuntimeError(f"packet example exited {run.returncode}: {run.stderr.decode(errors='replace').strip()}")
        return run.stdout.decode("ascii")


def _publish(source: Path, destination: Path, gallina: str) -> None:
    if (source.resolve() == destination.resolve()
            or (destination.exists() and source.samefile(destination))):
        raise HoldFastError("io", 1, 1, "output aliases the input")
    with atomic_path(destination) as pending:
        pending.write_text(gallina, encoding="utf-8", newline="")


def _qualify_compilation_database(root: Path, scanner: Path) -> dict[str, object]:
    scanner = scanner.resolve(strict=True)
    reader_hash = file_sha256(scanner)
    if reader_hash != "268678d396d51830acbe20f958005cecc9ac155de5822807e3390c0ed3cde995":
        raise ValueError("expected the qualified Ubuntu ARM64 clang-scan-deps 21.1.8 reader")

    def inspect(directory: Path, source: Path, expected_output: Path,
                dependency: Path, flags: list[tuple[str, str]]) -> None:
        argv = [str(scanner), "-compilation-database", str(directory / "compile_commands.json"),
                "-format", "experimental-full", "-j", "1"]
        result = subprocess.run(argv, capture_output=True, check=True, timeout=30)
        if len(result.stdout) > 1024 * 1024:
            raise ValueError("compilation database reader exceeded its output budget")
        [unit] = json.loads(result.stdout)["translation-units"]
        commands = unit["commands"]
        frontend = commands[0]
        if frontend["input-file"] != str(source) or str(dependency) not in frontend["file-deps"]:
            raise ValueError("reader lost the translation unit or its included source")
        arguments = frontend["command-line"]
        pairs = set(pairwise(arguments))
        if ("-I", str(directory)) not in pairs or any(flag not in pairs for flag in flags):
            raise ValueError("reader lost the include, definition or target flags")
        if f"-fdebug-compilation-dir={directory}" not in arguments or not any(
            ("-o", str(expected_output)) in pairwise(command["command-line"]) for command in commands
        ):
            raise ValueError("reader lost the working directory or output association")

    with tempfile.TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        packet = workspace / "packet build with spaces"
        output = _packet_example(root, root / holdfast_first_slice.EXAMPLE, bytes.fromhex("56026b011122"), bridge_dir=packet)
        if "payload 11 22" not in output:
            raise ValueError("compiled packet bridge returned unexpected bytes")
        inspect(packet, root / "tools/toolchain/packet_example.c", packet / "packet-example", packet / "packet.c", [])
        control = workspace / "target and define"
        control.mkdir()
        header = control / "measured.h"
        header.write_text("#if WIDTH != 42 || !defined(__riscv)\n#error wrong configuration\n#endif\n")
        source = workspace / "target control.c"
        source.write_text("#include <measured.h>\nint width(void) { return WIDTH; }\n")
        target = "riscv64-unknown-unknown-elf"
        obj = control / "target.o"
        _compile_bridge(control, "clang", ["--target=" + target, "-DWIDTH=42", "-I", str(control), "-c"],
                        source, obj, export=True)
        inspect(control, source, obj, header, [("-triple", target), ("-D", "WIDTH=42")])
    return {"status": "qualified", "reader_sha256": reader_hash, "packet_payload": [17, 34],
            "control_target": target, "control_define": "WIDTH=42"}


def _lint_preview(root: Path, path: Path, line: int, column: int) -> dict[str, object]:
    source = holdfast_parser.read_source(path)
    with holdfast_parser.cached_build(root) as compiled:
        edit = mathematical_preview.preview(compiled, source, line, column)
    if holdfast_parser.read_source(path) != source:
        raise ValueError("source changed before mathematical preview publication")
    return edit


def _with_annotations(
    findings: tuple[Finding, ...], compiled: holdfast_parser.Build, source: bytes, enabled: bool,
) -> tuple[Finding, ...]:
    if not enabled:
        return findings
    extra = mathematical_authoring.annotation_findings(compiled, source)
    return tuple(sorted((*findings, *extra), key=lambda finding: (finding.line, finding.column, finding.code)))


def _authoring(root: Path, args: argparse.Namespace, allowed: set[str], denied: set[str], annotations: bool) -> int:
    if args.command == "fmt" and args.source == Path("-"):
        if not args.syntax_only:
            raise ValueError("fmt - requires --syntax-only for an editor buffer")
        source = sys.stdin.buffer.read(MAX_SOURCE_BYTES + 1)
        with holdfast_parser.cached_build(root) as compiled:
            formatted = mathematical_authoring.format_syntax(compiled, source)
        if not args.check:
            sys.stdout.buffer.write(formatted)
        elif formatted != source:
            raise HoldFastError("format", 1, 1, "source differs from canonical mathematical layout")
        return 0
    snapshot = read_source(args.source)
    with holdfast_parser.cached_build(root) as compiled:
        if args.command == "lint":
            findings = _with_annotations(
                mathematical_authoring.lint_source(compiled, snapshot.data), compiled, snapshot.data, annotations,
            )
            ensure_unchanged(snapshot)
            return 0 if report_findings(args.source, findings, allowed, denied) else 1
        if args.command == "fmt" and args.syntax_only:
            candidate = mathematical_authoring.format_syntax(compiled, snapshot.data)
            compilations = None
        else:
            candidate, original, checked = mathematical_authoring.format_checked(compiled, snapshot.data)
            compilations = (
                checked.gallina,
                _with_annotations(original.findings, compiled, snapshot.data, annotations),
                _with_annotations(checked.findings, compiled, candidate, annotations),
            )
    ensure_unchanged(snapshot)
    check_only = args.check if args.command == "fmt" else args.format == "check"
    if check_only and candidate != snapshot.data:
        raise HoldFastError("format", 1, 1, "source differs from mathematical style; run holdfast-parser fmt")
    if args.command == "fmt":
        rewrite_source(snapshot, candidate)
        return 0
    if compilations is None:
        raise RuntimeError("elaboration requires checked mathematical formatting")
    gallina, original_findings, checked_findings = compilations
    if any(finding.code in denied for finding in original_findings):
        report_findings(args.source, original_findings, allowed, denied)
        return 1
    if not report_findings(args.source, checked_findings, allowed, denied):
        return 1
    if args.output is None:
        current = rewrite_source(snapshot, candidate)
        ensure_unchanged(current)
        print(gallina, end="")
    else:
        check_destination(snapshot.path, args.output)
        with atomic_path(args.output) as pending:
            pending.write_text(gallina, encoding="utf-8", newline="")
            check_destination(snapshot.path, args.output)
            current = rewrite_source(snapshot, candidate)
            ensure_unchanged(current)
    return 0


def _debug_simulator(args: argparse.Namespace) -> dict[str, object]:
    loaded = env.load()
    simulator = args.simulator or loaded.simulator
    profile = args.profile or loaded.profile
    with tempfile.TemporaryDirectory(prefix="holdfast-sail-debug-") as temporary:
        directory = Path(temporary)
        if args.qualify:
            if args.operations or args.control != "pass":
                raise ValueError("qualification runs its own controls and operations")
            return simulator_debug_check.qualify_controls(simulator, profile, directory)
        operations = args.operations or ["where"]
        if len(operations) > 64:
            raise ValueError("a batch permits up to 64 inspection commands")
        session = simulator_debug.Session(args.control, simulator, profile, directory)
        return {"control": args.control, "sha256": session.identities,
                "results": [simulator_debug.command(session, op) for op in operations]}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(suggest_on_error=True, description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    web = commands.add_parser("emit-web", help="export one exhaustively checked pure Boolean function to JavaScript")
    web.add_argument("source", type=Path)
    web.add_argument("function", help="public HoldFast function to export as the default ES module function")
    web.add_argument("--output", required=True, type=Path, help="destination .mjs file")
    commands.add_parser("qualify-web", help="check independent Boolean client tables and corrupted outputs")
    debugger = commands.add_parser("debug-simulator", help="inspect a packet assembly control on Sail")
    debugger.add_argument("--control", choices=simulator_debug.CONTROLS, default="pass")
    debugger.add_argument("--simulator", type=Path, help="local Sail executable (defaults to the current lane)")
    debugger.add_argument("--profile", type=Path, help="matching Sail JSON profile")
    debugger.add_argument("--command", action="append", dest="operations",
                          help="repeat source, where, step, until LINE, stack, eval REGISTER.FIELD, disconnect, reconnect or continue")
    debugger.add_argument("--qualify", action="store_true", help="replay independently expected live stops and refusals")
    commands.add_parser("build", help="make a fresh native parser and receipt")
    commands.add_parser("qualify", help="check independent AST/refusal fixtures and regeneration")
    arithmetic = commands.add_parser("check-arithmetic", help="kernel-check partial word operations against their checked variants")
    arithmetic.add_argument("source", type=Path)
    grading = commands.add_parser("check-grades", help="replay a pure graded definition and report its binder demand")
    grading.add_argument("source", type=Path)
    grading.add_argument("definition", help="mathematical definition to check")
    grading.add_argument("--domain", type=graded_source.GradeDomain, choices=tuple(graded_source.GradeDomain),
                         default=graded_source.GradeDomain.EXACT, help="select the computation grade domain (default: NatExact)")
    grading.add_argument("--modal", action="store_true", help="replay natural-valued promotion and explicit Box motives")
    mapping = commands.add_parser("source-map", help="publish mathematical Gallina, an ECMA-426 map and its bindings")
    mapping.add_argument("source", type=Path)
    mapping.add_argument("--output", type=Path, required=True, metavar="NEW_DIRECTORY")
    lookup = commands.add_parser("source-map-query", help="locate a generated Gallina position with the checked map")
    lookup.add_argument("source", type=Path)
    lookup.add_argument("directory", type=Path)
    lookup.add_argument("--node", type=Path, required=True, help="pinned Node.js reader executable")
    lookup.add_argument("--line", type=int, required=True, help="one-based generated line")
    lookup.add_argument("--column", type=int, required=True, help="one-based generated UTF-16 column")
    map_check = commands.add_parser("qualify-source-maps", help="exercise the independent source-map reader and stale refusals")
    map_check.add_argument("--node", type=Path, required=True)
    remark_check = commands.add_parser("qualify-remarks", help="read specialization decisions with independent LLVM tools")
    remark_check.add_argument("reader", type=Path, help="pinned Ubuntu ARM64 LLVM 21.1.8 llvm-remarkutil")
    upgrade = commands.add_parser("check-upgrade", help="re-elaborate the same clients against two module revisions")
    upgrade.add_argument("baseline", type=Path)
    upgrade.add_argument("candidate", type=Path)
    upgrade.add_argument("--client", required=True, action="append", type=Path, help="dependent client module (repeatable)")
    upgrade.add_argument("--dependency", action="append", type=Path, default=[], help="fixed dependency module (repeatable)")
    diff = commands.add_parser("diff-contract", help="compare authored public declarations and authority clauses")
    diff.add_argument("baseline", type=Path)
    diff.add_argument("candidate", type=Path)
    lock = commands.add_parser("lock-package", help="lock an offline mathematical package and its declared inputs")
    lock.add_argument("workspace", type=Path)
    lock.add_argument("name")
    lock.add_argument("revision")
    lock.add_argument("--output", required=True, type=Path, help="destination lockfile")
    index = commands.add_parser("scip", help="index a locked mathematical package for offline navigation")
    index.add_argument("workspace", type=Path)
    index.add_argument("lock", type=Path)
    index.add_argument("--output", required=True, type=Path, help="new bundle directory")
    verify = commands.add_parser("scip-check", help="verify a SCIP bundle against the current package")
    verify.add_argument("workspace", type=Path)
    verify.add_argument("lock", type=Path)
    verify.add_argument("directory", type=Path)
    verify.add_argument("--require-complete", action="store_true", help="require coverage for authored reference absence")
    build = commands.add_parser("build-package", help="check a locked module graph and optionally publish its Gallina bundle")
    build.add_argument("workspace", type=Path)
    build.add_argument("lock", type=Path)
    build.add_argument("--output", type=Path, help="atomically publish the generated module bundle")
    commands.add_parser("qualify-bsp-client", help="check the locked build graph in the pinned Neovim BSP client")
    reader = commands.add_parser("qualify-scip-reader", help="query two locked package revisions in the pinned offline SCIP reader")
    reader.add_argument("reader", type=Path, help="upstream v0.10.0 Linux ARM64 scip executable")
    server = commands.add_parser("bsp", help="serve the locked package graph over BSP 2.1.1 stdio")
    server.add_argument("workspace", type=Path)
    server.add_argument("locks", type=Path, nargs="+", metavar="LOCK")
    commands.add_parser("migration", help="compare pure parser outputs against independent fixtures")
    syntax_campaigns = commands.add_parser(
        "syntax-campaigns",
        help="qualify Menhir-generated syntax campaigns and independent AST/span oracles",
    )
    syntax_campaigns.add_argument(
        "--seed-start",
        type=int,
        default=holdfast_syntax_campaigns.DEFAULT_SEED_START,
        help="starting seed for Menhir --random-sentence generation",
    )
    syntax_campaigns.add_argument(
        "--count",
        type=int,
        default=holdfast_syntax_campaigns.DEFAULT_CAMPAIGN_COUNT,
        help="number of deterministic sentences to generate",
    )
    syntax_campaigns.add_argument(
        "--goal-length",
        type=int,
        default=holdfast_syntax_campaigns.DEFAULT_GOAL_LENGTH,
        help="goal sentence length passed to Menhir --random-sentence-length",
    )
    commands.add_parser("elaborate-qualify", help="replay pure and mathematical elaboration through the locked kernel")
    first_slice = commands.add_parser(
        "first-slice",
        help="replay packet-validator source proofs in Rocq and assembly controls in Sail",
    )
    first_slice.add_argument("--ccomp", type=Path, help="require compiler replay with this VerifiedOS typed ccomp")
    first_slice.add_argument("--trace", action="store_true", help="retain a bounded packet compiler timeline alongside the receipt")
    packet = commands.add_parser("packet-example", help="run a packet through the validator and display the destination bytes")
    packet.add_argument("packet", type=_packet_bytes, metavar="HEX", help="up to eight hexadecimal bytes")
    packet.add_argument("--source", type=Path, default=Path(holdfast_first_slice.EXAMPLE), help="validator source to elaborate and run")
    packet.add_argument("--compile-commands", type=Path, metavar="NEW_DIRECTORY",
                        help="retain the actual C build and compilation database in a new directory")
    database = commands.add_parser("qualify-compile-commands", help="check actual C bridge commands in pinned clang-scan-deps")
    database.add_argument("scanner", type=Path)
    bindings = commands.add_parser(
        "first-slice-bindings", help="check retained first-slice identities without proof replay or admission",
    )
    bindings.add_argument("receipt", type=Path)
    elaborate = commands.add_parser(
        "elaborate", help="emit unqualified Gallina for the bounded generic/dependent mathematical fragment",
        description="Elaborate the supported mathematical fragment and emit Gallina. "
                    "Run kernel replay separately to check emitted proof terms. "
                    "The elaborator reports unsupported constructs and refuses unresolved holes.")
    elaborate.add_argument("source", type=Path)
    elaborate.add_argument("--format", choices=("off", "check", "write"), default="off",
                           help="explicitly check or write canonical mathematical layout before emission")
    elaborate.add_argument("--output", type=Path,
                           help="atomically replace a file in an existing directory")
    elaborate.add_argument("--allow", action="append", choices=MATHEMATICAL_LINT_CODES, default=[],
                           help="suppress an advisory mathematical lint (repeatable)")
    elaborate.add_argument("--deny", action="append", choices=MATHEMATICAL_LINT_CODES, default=[],
                           help="make an advisory mathematical lint an error (repeatable)")
    elaborate.add_argument("--warn", action="append", choices=sorted(OPT_IN_MATHEMATICAL_LINTS), default=[],
                           help="enable an opt-in mathematical lint (repeatable)")
    fmt = commands.add_parser("fmt", help="check and format a mathematically elaborated source")
    fmt.add_argument("source", type=Path, help="source file, or - for an editor buffer with --syntax-only")
    fmt.add_argument("--check", action="store_true", help="report a style difference without writing")
    fmt.add_argument("--syntax-only", action="store_true", help="check syntax and preservation without elaborating")
    lint = commands.add_parser("lint", help="check mathematical declarations, documentation and expression lints")
    lint.add_argument("source", type=Path)
    codes = ("HOLDFAST100", "HOLDFAST101", "HOLDFAST102", *MATHEMATICAL_LINT_CODES)
    lint.add_argument("--allow", action="append", choices=codes, default=[])
    lint.add_argument("--deny", action="append", choices=codes, default=[])
    lint.add_argument("--warn", action="append", choices=sorted(OPT_IN_MATHEMATICAL_LINTS), default=[],
                      help="enable an opt-in mathematical lint (repeatable)")
    preview = commands.add_parser("lint-preview", help="preview checked grouping for a mathematical HOLDFAST107 warning")
    preview.add_argument("source", type=Path)
    preview.add_argument("--line", type=int, required=True, help="one-based warning line")
    preview.add_argument("--column", type=int, required=True, help="one-based warning column")
    support = commands.add_parser("support", help="build and kernel-check the pinned Rocq support library")
    support.add_argument("--archive", type=Path, help="use an already downloaded authenticated release archive")
    parse = commands.add_parser("parse", help="emit a complete located syntax tree as JSON")
    parse.add_argument("--surface", action="store_true", help="parse the full development surface and emit its AST")
    parse.add_argument("source", type=Path)
    args = parser.parse_args(argv)
    allowed = set(getattr(args, "allow", []))
    denied = set(getattr(args, "deny", []))
    warned = set(getattr(args, "warn", []))
    if allowed & denied:
        parser.error("a lint cannot be both allowed and denied")
    if allowed & warned:
        parser.error("a lint cannot be both allowed and set to warn")
    enabled = denied | warned
    annotations = "HOLDFAST133" in enabled
    allowed.update(OPT_IN_MATHEMATICAL_LINTS - enabled)
    root = Path(__file__).resolve().parents[3]
    try:
        if args.command == "bsp":
            return bsp.serve(root, args.workspace, args.locks, sys.stdin.buffer, sys.stdout.buffer)
        if args.command == "packet-example":
            print(_packet_example(root, args.source, args.packet, bridge_dir=args.compile_commands), end="")
            return 0
        if args.command in ("fmt", "lint") or (args.command == "elaborate" and args.format != "off"):
            return _authoring(root, args, allowed, denied, annotations)
        if args.command == "elaborate":
            source = holdfast_parser.read_source(args.source)
            with holdfast_parser.cached_build(root) as compiled:
                parsed = holdfast_parser.parse_source(compiled, source, surface=True)
                translation = holdfast_mathematical.inspect_source(source, parsed)
                findings = _with_annotations(translation.findings, compiled, source, annotations)
            if not report_findings(args.source, findings, allowed, denied):
                return 1
            if args.output is None:
                print(translation.gallina, end="")
            else:
                _publish(args.source, args.output, translation.gallina)
            return 0
        if args.command == "emit-web":
            output = web_output.publish(args.source, args.function, args.output)
        elif args.command == "qualify-web":
            output = web_output_check.qualify(root)
        elif args.command == "debug-simulator":
            output = _debug_simulator(args)
        elif args.command == "qualify-compile-commands":
            output = _qualify_compilation_database(root, args.scanner)
        elif args.command == "lint-preview":
            output = _lint_preview(root, args.source, args.line, args.column)
        elif args.command == "check-arithmetic":
            output = holdfast_elaboration_check.check_arithmetic(root, args.source)
        elif args.command == "check-grades":
            output = graded_source.check(root, args.source, args.definition, modal=args.modal, domain=args.domain)
        elif args.command == "source-map":
            output = gallina_source_map.export(root, args.source, args.output)
        elif args.command == "qualify-remarks":
            output = remarks_reader.qualify(args.reader)
        elif args.command == "source-map-query":
            output = gallina_source_map.query(root, args.source, args.directory, args.node, args.line, args.column)
        elif args.command == "qualify-source-maps":
            output = source_map_check.qualify(root, args.node)
        elif args.command == "check-upgrade":
            with holdfast_parser.cached_build(root) as compiled:
                def load_module(path: Path) -> tuple[bytes, object]:
                    source = holdfast_parser.read_source(path)
                    try:
                        return source, holdfast_parser.parse_source(compiled, source, surface=True)
                    except HoldFastError as error:
                        raise HoldFastError(error.kind, error.line, error.column, f"{path}: {error.message}") from error
                output = check_client_upgrade(load_module(args.baseline), load_module(args.candidate),
                                              [load_module(path) for path in args.client],
                                              [load_module(path) for path in args.dependency])
        elif args.command == "diff-contract":
            baseline, candidate = read_source(args.baseline), read_source(args.candidate)
            with holdfast_parser.cached_build(root) as compiled:
                old_tree = holdfast_parser.parse_source(compiled, baseline.data, surface=True)
                new_tree = holdfast_parser.parse_source(compiled, candidate.data, surface=True)
            output = contract_diff.compare(baseline.data, old_tree, candidate.data, new_tree)
            ensure_unchanged(baseline)
            ensure_unchanged(candidate)
        elif args.command == "qualify-bsp-client":
            output = bsp_client.qualify(root)
        elif args.command == "qualify-scip-reader":
            output = scip_reader.qualify(root, args.reader)
        elif args.command == "lock-package":
            output = packages.lock_package(root, args.workspace, args.name, args.revision, args.output)
        elif args.command == "scip":
            output = scip.export(root, args.workspace, args.lock, args.output)
        elif args.command == "scip-check":
            output = scip.check(root, args.workspace, args.lock, args.directory, require_complete=args.require_complete)
        elif args.command == "build-package":
            def report_package_lints(path: Path, findings: tuple[Finding, ...]) -> None:
                report_findings(path, findings, set(), set())

            output = packages.build_package(root, args.workspace, args.lock, args.output, report_lints=report_package_lints)
        elif args.command == "elaborate-qualify":
            output = holdfast_elaboration_check.qualify(root)
        elif args.command == "first-slice":
            output = holdfast_first_slice.qualify(root, ccomp_path=getattr(args, "ccomp", None), trace_phases=args.trace)
        elif args.command == "first-slice-bindings":
            output = holdfast_first_slice.verify_bindings(root, args.receipt)
        elif args.command == "support":
            output = holdfast_parser_checked.qualify(root, archive=args.archive)
        elif args.command == "migration":
            output = holdfast_migration.qualify(root)
        elif args.command == "syntax-campaigns":
            output = holdfast_syntax_campaigns.qualify(
                root,
                seed_start=args.seed_start,
                count=args.count,
                goal_length=args.goal_length,
            )
        elif args.command == "qualify":
            output = holdfast_parser.qualify(root)
        elif args.command == "build":
            output = holdfast_parser.build(root).receipt
        else:
            source = holdfast_parser.read_source(args.source)
            with holdfast_parser.cached_build(root) as compiled:
                output = holdfast_parser.parse_source(compiled, source, surface=args.surface)
    except HoldFastError as error:
        site = str(args.source) if hasattr(args, "source") else args.command
        print(f"{site}:{error.line}:{error.column}: {error.kind}: {error.message}", file=sys.stderr)
        return 1
    except (OSError, RuntimeError, TypeError, ValueError, Timeout, subprocess.TimeoutExpired) as error:
        print(f"FAIL holdfast-parser: {error}", file=sys.stderr)
        return 1
    print(json.dumps(output, indent=2, sort_keys=True))
    if args.command == "migration" and output["status"] != "agreed":
        return 1
    return 0
