# SPDX-License-Identifier: Apache-2.0
"""Kernel consumers of resolved modules and locked mathematical packages."""

import json
import re
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from tests.test_vela_elaborate import (
    _binary,
    _boolean,
    _call,
    _Fixture,
    _import_decl,
    _natural,
    _type,
    _variable,
)
from tests.test_vela_packages import _write
from toolchain import packages, parser, proofenv
from toolchain.elaborate import elaborate_package
from toolchain.elaborate_types import PackageScope


def _exercise(compiled: parser.Build | None = None) -> str:
    left, right, other, client = (_Fixture(name) for name in ("Left", "Right", "Other", "Client"))
    left.definition("EchoNat", _type("Nat"), (("x", _type("Nat")),), _variable("x"))
    right.definition("EchoBool", _type("bool"), (("x", _type("bool")),), _variable("x"))
    other.definition("Unused", _type("Nat"), (("n", _type("Nat")),), _variable("n"))
    _import_decl(client, "Left")
    _import_decl(client, "Right")
    client.definition("Check", _type("bool"), (),
                      _binary("&&", _binary("==", _call("EchoNat", _natural(7)), _natural(7)),
                              _call("EchoBool", _boolean(True))))
    scopes = {"Left": PackageScope("1" * 64, frozenset({"Left"})),
              "Right": PackageScope("2" * 64, frozenset({"Right"})),
              "Other": PackageScope("3" * 64, frozenset({"Other"})),
              "Client": PackageScope("4" * 64, frozenset({"Left", "Right", "Client"}))}
    inputs = {}
    for name, fixture in zip(scopes, (left, right, other, client), strict=True):
        source, tree = fixture.response()
        inputs[name] = (source, parser.parse_source(compiled, source, surface=True) if compiled else tree)

    def build(names: tuple[str, ...]) -> dict[str, str]:
        output = elaborate_package([inputs[name] for name in names], scopes={name: scopes[name] for name in names})
        return {name: result.gallina for name, result in output.items()}

    expected = build(("Left", "Right", "Client"))
    extra = build(("Other", "Right", "Left", "Client"))
    ensure(all(expected[name] == extra[name] for name in expected),
           "rebuilding alongside a disjoint sibling changed a module's Gallina bytes")
    for name in ("Left", "Right"):
        ensure(expected[name] == build((name,))[name], "standalone and linked dependency output differ")
    binders = re.findall(r"^Definition \w+_Echo(?:Nat|Bool) : \(forall \((vela_v\d+) :", expected["Client"], re.MULTILINE)
    ensure(len(binders) == len(set(binders)) == 2, "different providers shared a binder identity")
    return expected["Client"]


def _in_memory() -> None:
    _exercise()


def _kernel_consumer(gallina: str, name: str, expected: str) -> None:
    [module] = re.findall(r"^Module (VelaPackage_\w+)\.$", gallina, re.MULTILINE)
    [operation] = re.findall(rf"^Definition (\w+_{name}) :", gallina, re.MULTILINE)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "Consumer.v").write_text(
            gallina + f"Example read_inputs : {module}.{operation} tt = {expected} := eq_refl.\n", encoding="utf-8")
        for arguments in (["rocq", "c", "-q", "Consumer.v"], ["rocqchk", "-silent", "Consumer"]):
            result = subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *arguments],
                                    cwd=tmp, capture_output=True, timeout=180, check=False)
            ensure(result.returncode == 0, f"kernel replay failed: {(result.stdout + result.stderr)[-3000:]!r}")


def _native_replay() -> None:
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = _exercise(compiled)
    _kernel_consumer(gallina, "Check", "true")


def _locked_static_text() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        workspace = Path(tmp)
        table = _write(workspace, "tables", "v1", {}, "Tables")
        client = _write(workspace, "consumer", "v1", {"tables": "v1"}, "Consumer")
        provider = table / "module.vela"
        provider.write_text('module Tables; public const Vec<Nat,2> Tag = "é";\n', encoding="utf-8")
        (client / "module.vela").write_text(
            "module Consumer; import Tables; public definition Nat ReadByte() => Tag[1];\n", encoding="utf-8")
        lock, output = workspace / "lock.json", workspace / "bundle.json"

        def build() -> bytes:
            packages.build_package(TOOLS.parent, workspace, lock, output)
            return output.read_bytes()

        packages.lock_package(TOOLS.parent, workspace, "consumer", "v1", lock)
        initial = build()
        _kernel_consumer(json.loads(initial)["modules"]["Consumer"], "ReadByte", "169")
        ensure(build() == initial, "same locked static table produced different output")
        provider.write_text('module Tables; public const Vec<Nat,2> Tag = "Å";\n', encoding="utf-8")
        with raises(ValueError) as stale:
            build()
        ensure("stale package lock" in str(stale.exception), "provider edit missed the package freshness check")
        ensure(output.read_bytes() == initial, "a changed static dependency replaced the old bundle")
        packages.lock_package(TOOLS.parent, workspace, "consumer", "v1", lock)
        updated = build()
        _kernel_consumer(json.loads(updated)["modules"]["Consumer"], "ReadByte", "133")
        manifest = client / packages.MANIFEST
        manifest.write_text(manifest.read_text(encoding="utf-8").replace("rocq-gallina", "host-native"),
                            encoding="utf-8")
        with raises(ValueError) as changed:
            build()
        ensure("stale package lock" in str(changed.exception), "edited target reused the original lock")
        with raises(ValueError) as unsupported:
            packages.lock_package(TOOLS.parent, workspace, "consumer", "v1", lock)
        ensure("edition or target" in str(unsupported.exception), "host target passed manifest validation")
        ensure(output.read_bytes() == updated, "a refused target replaced the last built bundle")


def cases() -> list[Case]:
    return [Case("module-local deterministic locked binder identities", _in_memory),
            Case("kernel composes stable locked providers with different binder types", _native_replay,
                 slow=True, lane="toolchain"),
            Case("locked static text survives replay and refuses stale dependency and target", _locked_static_text,
                 slow=True, lane="toolchain")]
