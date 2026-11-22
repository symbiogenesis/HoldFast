# SPDX-License-Identifier: Apache-2.0
"""Parse Vela, elaborate mathematical terms, or qualify development tooling."""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from filelock import Timeout

from toolchain import (
    VelaError,
    mathematical_preview,
    solver_ledger,
)
from toolchain import (
    elaboration_check as vela_elaboration_check,
)
from toolchain import (
    first_slice as vela_first_slice,
)
from toolchain import (
    mathematical as vela_mathematical,
)
from toolchain import (
    migration as vela_migration,
)
from toolchain import (
    parser as vela_parser,
)
from toolchain import (
    parser_checked as vela_parser_checked,
)
from toolchain import (
    syntax_campaigns as vela_syntax_campaigns,
)
from toolchain.atomic import atomic_path
from toolchain.authoring import MATHEMATICAL_LINT_CODES, Finding
from toolchain.elaborate import check_client_upgrade
from toolchain.elaborate import elaborate as elaborate_source


def _packet_bytes(argument: str) -> bytes:
    try:
        packet = bytes.fromhex(argument)
    except ValueError as error:
        raise argparse.ArgumentTypeError("supply complete hexadecimal bytes, for example '56 02 6b 01 11 22'") from error
    if len(packet) > 8:
        raise argparse.ArgumentTypeError("the packet example accepts at most eight bytes")
    return packet


def _packet_example(root: Path, source_path: Path, packet: bytes) -> str:
    source = vela_parser.read_source(source_path)
    with vela_parser.cached_build(root) as compiled:
        parsed = vela_parser.parse_source(compiled, source, surface=True)
    checked = elaborate_source(source, parsed)
    obligations = solver_ledger.ledger(checked.gallina)
    if obligations:
        first = obligations[0]
        raise VelaError("proof", first.line, first.column, f"unproved packet contract: {first.export}")
    generated, _ = vela_first_slice.lower_to_c(source, parsed, checked=checked)
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory / "packet.c").write_text(generated, encoding="utf-8")
        driver = root / "tools/toolchain/packet_example.c"
        executable = directory / "packet-example"
        build = subprocess.run(["cc", "-std=c11", "-I", tmp, str(driver), "-o", str(executable)],
                               capture_output=True, text=True, check=False, timeout=30)
        if build.returncode:
            raise RuntimeError(f"packet example C build failed: {build.stderr.strip()}")
        run = subprocess.run([str(executable)], input=packet, capture_output=True, check=False, timeout=5)
        if run.returncode:
            raise RuntimeError(f"packet example exited {run.returncode}: {run.stderr.decode(errors='replace').strip()}")
        return run.stdout.decode("ascii")


def _publish(source: Path, destination: Path, gallina: str) -> None:
    if (source.resolve() == destination.resolve()
            or (destination.exists() and source.samefile(destination))):
        raise VelaError("io", 1, 1, "output aliases the input")
    with atomic_path(destination) as pending:
        pending.write_text(gallina, encoding="utf-8", newline="")


def _lint_preview(root: Path, path: Path, line: int, column: int) -> dict[str, object]:
    source = vela_parser.read_source(path)
    with vela_parser.cached_build(root) as compiled:
        edit = mathematical_preview.preview(compiled, source, line, column)
    if vela_parser.read_source(path) != source:
        raise ValueError("source changed before mathematical preview publication")
    return edit


def _report_findings(source: Path, findings: tuple[Finding, ...], allowed: set[str], denied: set[str]) -> bool:
    failed = False
    for finding in findings:
        if finding.code in allowed:
            continue
        is_error = finding.code in denied
        failed |= is_error
        level = "error" if is_error else "warning"
        print(f"{source}:{finding.line}:{finding.column}: {level} {finding.code}: {finding.message}",
              file=sys.stderr)
    return not failed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(suggest_on_error=True, description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("build", help="make a fresh native parser and receipt")
    commands.add_parser("qualify", help="check independent AST/refusal fixtures and regeneration")
    arithmetic = commands.add_parser("check-arithmetic", help="kernel-check partial word operations against their checked variants")
    arithmetic.add_argument("source", type=Path)
    upgrade = commands.add_parser("check-upgrade", help="re-elaborate the same clients against two module revisions")
    upgrade.add_argument("baseline", type=Path)
    upgrade.add_argument("candidate", type=Path)
    upgrade.add_argument("--client", required=True, action="append", type=Path, help="dependent client module (repeatable)")
    upgrade.add_argument("--dependency", action="append", type=Path, default=[], help="fixed dependency module (repeatable)")
    commands.add_parser("migration", help="compare generated AST translation with the retained prototype")
    syntax_campaigns = commands.add_parser(
        "syntax-campaigns",
        help="qualify Menhir-generated syntax campaigns and independent AST/span oracles",
    )
    syntax_campaigns.add_argument(
        "--seed-start",
        type=int,
        default=vela_syntax_campaigns.DEFAULT_SEED_START,
        help="starting seed for Menhir --random-sentence generation",
    )
    syntax_campaigns.add_argument(
        "--count",
        type=int,
        default=vela_syntax_campaigns.DEFAULT_CAMPAIGN_COUNT,
        help="number of deterministic sentences to generate",
    )
    syntax_campaigns.add_argument(
        "--goal-length",
        type=int,
        default=vela_syntax_campaigns.DEFAULT_GOAL_LENGTH,
        help="goal sentence length passed to Menhir --random-sentence-length",
    )
    commands.add_parser("elaborate-qualify", help="replay pure and mathematical elaboration through the locked kernel")
    first_slice = commands.add_parser(
        "first-slice",
        help="qualify the Q25w Span<byte> carrier and vela-first-slice validator across Rocq and Sail",
    )
    first_slice.add_argument("--ccomp", type=Path, help="require compiler replay with this VerifiedOS typed ccomp")
    first_slice.add_argument("--trace", action="store_true", help="retain a bounded packet compiler timeline alongside the receipt")
    packet = commands.add_parser("packet-example", help="run a packet through the validator and display the destination bytes")
    packet.add_argument("packet", type=_packet_bytes, metavar="HEX", help="up to eight hexadecimal bytes")
    packet.add_argument("--source", type=Path, default=Path(vela_first_slice.EXAMPLE), help="validator source to elaborate and run")
    bindings = commands.add_parser(
        "first-slice-bindings", help="check retained first-slice identities without proof replay or admission",
    )
    bindings.add_argument("receipt", type=Path)
    elaborate = commands.add_parser(
        "elaborate", help="emit unqualified Gallina for the bounded generic/dependent mathematical fragment",
        description="Elaborate generic dependent mathematics and explicit proofs. Development prototype; "
                    "emission supplies no kernel or source-correspondence verdict. "
                    "Unsupported contracts, effects, resource syntax and unresolved holes are refused.")
    elaborate.add_argument("source", type=Path)
    elaborate.add_argument("--output", type=Path,
                           help="atomically replace a file in an existing directory")
    elaborate.add_argument("--allow", action="append", choices=MATHEMATICAL_LINT_CODES, default=[],
                           help="suppress an advisory mathematical lint (repeatable)")
    elaborate.add_argument("--deny", action="append", choices=MATHEMATICAL_LINT_CODES, default=[],
                           help="make an advisory mathematical lint an error (repeatable)")
    preview = commands.add_parser("lint-preview", help="preview checked grouping for a mathematical VELA107 warning")
    preview.add_argument("source", type=Path)
    preview.add_argument("--line", type=int, required=True, help="one-based warning line")
    preview.add_argument("--column", type=int, required=True, help="one-based warning column")
    support = commands.add_parser("support", help="build and kernel-check the pinned Rocq support library")
    support.add_argument("--archive", type=Path, help="use an already downloaded authenticated release archive")
    parse = commands.add_parser("parse", help="emit a complete located syntax tree as JSON")
    parse.add_argument("--surface", action="store_true", help="parse the full development surface as schema 2")
    parse.add_argument("source", type=Path)
    args = parser.parse_args(argv)
    allowed = set(getattr(args, "allow", []))
    denied = set(getattr(args, "deny", []))
    if allowed & denied:
        parser.error("a lint cannot be both allowed and denied")
    root = Path(__file__).resolve().parents[3]
    try:
        if args.command == "packet-example":
            print(_packet_example(root, args.source, args.packet), end="")
            return 0
        if args.command == "elaborate":
            source = vela_parser.read_source(args.source)
            with vela_parser.cached_build(root) as compiled:
                parsed = vela_parser.parse_source(compiled, source, surface=True)
            translation = vela_mathematical.inspect_source(source, parsed)
            if not _report_findings(args.source, translation.findings, allowed, denied):
                return 1
            if args.output is None:
                print(translation.gallina, end="")
            else:
                _publish(args.source, args.output, translation.gallina)
            return 0
        if args.command == "lint-preview":
            output = _lint_preview(root, args.source, args.line, args.column)
        elif args.command == "check-arithmetic":
            output = vela_elaboration_check.check_arithmetic(root, args.source)
        elif args.command == "check-upgrade":
            with vela_parser.cached_build(root) as compiled:
                def load_module(path: Path) -> tuple[bytes, object]:
                    source = vela_parser.read_source(path)
                    try:
                        return source, vela_parser.parse_source(compiled, source, surface=True)
                    except VelaError as error:
                        raise VelaError(error.kind, error.line, error.column, f"{path}: {error.message}") from error
                output = check_client_upgrade(load_module(args.baseline), load_module(args.candidate),
                                              [load_module(path) for path in args.client],
                                              [load_module(path) for path in args.dependency])
        elif args.command == "elaborate-qualify":
            output = vela_elaboration_check.qualify(root)
        elif args.command == "first-slice":
            output = vela_first_slice.qualify(root, ccomp_path=getattr(args, "ccomp", None), trace_phases=args.trace)
        elif args.command == "first-slice-bindings":
            output = vela_first_slice.verify_bindings(root, args.receipt)
        elif args.command == "support":
            output = vela_parser_checked.qualify(root, archive=args.archive)
        elif args.command == "migration":
            output = vela_migration.qualify(root)
        elif args.command == "syntax-campaigns":
            output = vela_syntax_campaigns.qualify(
                root,
                seed_start=args.seed_start,
                count=args.count,
                goal_length=args.goal_length,
            )
        elif args.command == "qualify":
            output = vela_parser.qualify(root)
        elif args.command == "build":
            output = vela_parser.build(root).receipt
        else:
            source = vela_parser.read_source(args.source)
            with vela_parser.cached_build(root) as compiled:
                output = vela_parser.parse_source(compiled, source, surface=args.surface)
    except VelaError as error:
        site = str(args.source) if hasattr(args, "source") else args.command
        print(f"{site}:{error.line}:{error.column}: {error.kind}: {error.message}", file=sys.stderr)
        return 1
    except (OSError, RuntimeError, TypeError, ValueError, Timeout, subprocess.TimeoutExpired) as error:
        print(f"FAIL vela-parser: {error}", file=sys.stderr)
        return 1
    print(json.dumps(output, indent=2, sort_keys=True))
    if args.command == "migration" and output["status"] != "agreed":
        return 1
    return 0
