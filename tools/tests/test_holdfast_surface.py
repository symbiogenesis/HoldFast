# SPDX-License-Identifier: Apache-2.0
"""The wider parser entry cannot bypass schema or qualification boundaries."""

import hashlib
import json
import subprocess
import tempfile
from contextlib import nullcontext, redirect_stderr, redirect_stdout
from functools import partial
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from toolchain import parser, surface
from toolchain.cli import holdfast_parser as cli


def _build(directory: Path) -> parser.Build:
    executable = directory / "holdfast-parser"
    executable.write_bytes(b"fixture executable")
    return parser.Build(directory, executable, {
        "generated_sha256": {"holdfast-parser": hashlib.sha256(executable.read_bytes()).hexdigest()},
    })


def _entry_protocol() -> None:
    source = b"module M;"
    tree: dict[str, parser.Json] = {"kind": "surface_file", "span": [0, 9],
                                   "name": {"text": "M", "span": [7, 8]}, "declarations": []}
    with tempfile.TemporaryDirectory(prefix="holdfast-surface-") as temporary:
        compiled = _build(Path(temporary))
        response = subprocess.CompletedProcess([], 0, json.dumps({"schema": 2, "ast": tree}).encode(), b"")
        with patch.object(parser.subprocess, "run", return_value=response) as run:
            result = parser.parse_source(compiled, source, surface=True)
        ensure(run.call_args.args[0] == [str(compiled.executable), "--surface"],
               "surface request used the pure native entry")
        ensure(result == {"schema": 2, "source_sha256": hashlib.sha256(source).hexdigest(), "ast": tree},
               "surface source binding or syntax changed")
        for surface, schema, kind in ((False, 2, "surface_file"), (True, 1, "file"),
                                      (True, True, "surface_file"), (True, 2, "file")):
            payload = {"schema": schema, "ast": {**tree, "kind": kind}}
            response = subprocess.CompletedProcess([], 0, json.dumps(payload).encode(), b"")
            with patch.object(parser.subprocess, "run", return_value=response):
                with raises(ValueError, msg="cross-entry or boolean schema accepted") as raised:
                    parser.parse_source(compiled, source, surface=surface)
                ensure("schema" in str(raised.exception), "entry mismatch has no schema refusal")


def _entry_cli() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-surface-") as temporary:
        directory = Path(temporary)
        source = directory / "surface.hf"
        source.write_bytes(b"module M;")
        compiled = _build(directory)
        with redirect_stdout(output := StringIO()), redirect_stderr(errors := StringIO()), \
                patch.object(cli.holdfast_parser, "cached_build", return_value=nullcontext(compiled)), \
                patch.object(cli.holdfast_parser, "parse_source", return_value={"schema": 2}) as parse:
            code = cli.main(["parse", "--surface", str(source)])
        ensure(code == 0 and json.loads(output.getvalue()) == {"schema": 2} and not errors.getvalue(),
               "surface CLI failed or mixed diagnostics with syntax")
        parse.assert_called_once_with(compiled, source.read_bytes(), surface=True)
        with redirect_stdout(output := StringIO()), redirect_stderr(errors := StringIO()), \
                patch.object(cli.holdfast_parser, "cached_build", return_value=nullcontext(compiled)), \
                patch.object(cli.holdfast_parser, "parse_source", side_effect=ValueError("invalid surface schema")) as parse:
            code = cli.main(["parse", "--surface", str(source)])
        ensure(code == 1 and not output.getvalue() and "invalid surface schema" in errors.getvalue(),
               "failed surface request emitted output or hid refusal")
        ensure(parse.call_count == 1, "surface failure retried through a fallback parser")


def _qualification_input_binding() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-surface-") as temporary:
        root = Path(temporary)
        for name in parser.INPUT_PATHS:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(name.encode())
        initial = parser._inputs(root)
        for name in ("tools/toolchain/surface.py", "tools/toolchain/hashing.py",
                     "tools/toolchain/jsonutil.py", "tools/toolchain/atomic.py", parser.SURFACE_FIXTURE,
                     "examples/constants.hf", "examples/expressions.hf"):
            path = root / name
            original = path.read_bytes()
            path.write_bytes(original + b" changed")
            changed = parser._inputs(root)
            ensure(changed[name] != initial[name], f"qualification omitted changed {name}")
            path.write_bytes(original)


def _failed_surface_qualification() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-surface-") as temporary:
        root = Path(temporary)
        hashes = dict.fromkeys(parser.GENERATED, "same")
        compiled = parser.Build(root, root / "unused", {
            "inputs": {}, "toolchain": {}, "generated_sha256": hashes,
        })
        latest = root / "qualification.json"
        latest.write_text('{"status":"passed"}', encoding="utf-8")
        with patch.object(parser, "_work_root", return_value=root), \
                patch.object(parser, "build", return_value=compiled), \
                patch.object(parser, "_fixtures", return_value=["pure-passed"]), \
                patch.object(parser.holdfast_surface, "qualify", side_effect=ValueError("surface oracle differs")):
            with raises(ValueError, msg="failed surface oracle produced passing qualification") as raised:
                parser.qualify(root)
            ensure(str(raised.exception) == "surface oracle differs", "surface qualification failure was replaced")
        ensure(not latest.exists(), "failed surface oracle preserved stale passing evidence")


def _fixture_oracle(name: str, oracle_name: str, *, source_bound: bool = True) -> None:
    fixture = next(value for value in surface.POSITIVE if value.name == name)
    result: dict[str, parser.Json] = {"ast": [{"kind": kind} for kind in fixture.kinds]}
    fault = ValueError(f"{oracle_name} rejected {name}")
    with (
        patch.object(surface, "POSITIVE", (fixture,)),
        patch.object(surface, "_precedence_and_spans"),
        patch.object(surface, "_literal_and_comment_boundaries"),
        patch.object(surface, "_numeric_separator_limits"),
        patch.object(surface, "_argument_roles"),
        patch.object(surface, oracle_name, side_effect=fault) as oracle,
        raises(ValueError, msg=f"qualification bypassed {oracle_name}") as raised,
    ):
        surface.qualify(lambda _source: result)
    ensure(raised.exception is fault, f"qualification replaced the {oracle_name} failure")
    if source_bound:
        oracle.assert_called_once_with(fixture.source.encode(), result)
    else:
        oracle.assert_called_once_with(result)


def _binder_initializer_oracles_required() -> None:
    _fixture_oracle("generic-binders-and-typed-initializers", "_binder_initializer_roles")
    _fixture_oracle("binder-initializer-errors-remain-syntax", "_binder_initializer_error_roles",
                    source_bound=False)


def _explicit_value_oracles_required() -> None:
    _fixture_oracle("explicit-values-loans-and-options", "_explicit_value_roles")
    _fixture_oracle("explicit-pointer-operators", "_pointer_roles")
    _fixture_oracle("explicit-values-errors-remain-syntax", "_explicit_error_roles", source_bound=False)
    _fixture_oracle("expressions-and-closures", "_propagation_member_role", source_bound=False)


def _numeric_separator_limits_required() -> None:
    with patch.object(surface, "_precedence_and_spans"), \
            patch.object(surface, "_literal_and_comment_boundaries"), \
            patch.object(surface, "_numeric_separator_limits", side_effect=ValueError("separator limit changed")) as oracle:
        with raises(ValueError, msg="numeric separator limit oracle was bypassed") as raised:
            surface.qualify(lambda _source: {})
        ensure(str(raised.exception) == "separator limit changed", "numeric limit oracle failure was replaced")
    oracle.assert_called_once()


def _familiar_authoring_oracles_required() -> None:
    for name, oracle_name in (("expressions-patterns-updates-guards-and-properties", "_ergonomic_expression_and_property_roles"),
                              ("familiar-generic-calls-and-expression-arms", "_familiar_call_roles"),
                              ("bounded-collection-iteration", "_collection_iteration_roles"),
                              ("raw-strings-and-checked-formatting", "_raw_string_and_format_roles"),
                              ("container-resource-contracts", "_container_resource_roles"),
                              ("mathematical-definitions-and-proofs", "_indexed_constructor_roles")):
        _fixture_oracle(name, oracle_name)


def _generic_probe_limits_required() -> None:
    with patch.object(surface, "POSITIVE", ()), \
            patch.object(surface, "_precedence_and_spans"), \
            patch.object(surface, "_literal_and_comment_boundaries"), \
            patch.object(surface, "_numeric_separator_limits"), \
            patch.object(surface, "_generic_probe_limits", side_effect=ValueError("probe budget changed")) as oracle:
        with raises(ValueError, msg="generic probe inspection controls were bypassed") as raised:
            surface.qualify(lambda _source: {})
        ensure(str(raised.exception) == "probe budget changed", "probe budget refusal was replaced")
    oracle.assert_called_once()


def cases() -> list[Case]:
    return [Case("familiar-authoring-oracles-are-required", _familiar_authoring_oracles_required),
            Case("generic-probe-limits-are-required", _generic_probe_limits_required),
            Case("constant-callable-oracle-is-required",
                 partial(_fixture_oracle, "compositional-constant-callables", "_compositional_constant_roles")),
            Case("concise-authoring-oracle-is-required",
                 partial(_fixture_oracle, "concise-authoring-syntax", "_concise_authoring_roles")),
            Case("constant-declaration-order-and-span-oracle-is-required",
                 partial(_fixture_oracle, "required-static-constants", "_required_static_roles")),
            Case("surface-entry-schema-and-source-binding", _entry_protocol),
            Case("surface-cli-and-no-fallback", _entry_cli),
            Case("surface-fixture-input-identities", _qualification_input_binding),
            Case("surface-oracle-failure-without-receipt", _failed_surface_qualification),
            Case("shared-primitive-oracle-is-required",
                 partial(_fixture_oracle, "shared-syntax-primitives", "_shared_primitive_roles")),
            Case("expression-binding-oracle-is-required",
                 partial(_fixture_oracle, "expression-local-bindings", "_expression_binding_roles")),
            Case("binder-initializer-oracles-are-required", _binder_initializer_oracles_required),
            Case("explicit-value-oracles-are-required", _explicit_value_oracles_required),
            Case("numeric-separator-oracle-is-required",
                 partial(_fixture_oracle, "numeric-separator-values-patterns-and-indices", "_numeric_separator_roles")),
            Case("numeric-separator-limits-are-required", _numeric_separator_limits_required)]
