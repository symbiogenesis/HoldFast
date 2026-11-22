# SPDX-License-Identifier: Apache-2.0
"""A locked module's own inputs determine its binders and complete output."""

import re
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
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
from toolchain import parser, proofenv
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


def _native_replay() -> None:
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = _exercise(compiled)
    [module] = re.findall(r"^Module (VelaPackage_\w+)\.$", gallina, re.MULTILINE)
    [operation] = re.findall(r"^Definition (\w+_Check) :", gallina, re.MULTILINE)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "Consumer.v").write_text(
            gallina + f"Example read_inputs : {module}.{operation} tt = true := eq_refl.\n", encoding="utf-8")
        for arguments in (["rocq", "c", "-q", "Consumer.v"], ["rocqchk", "-silent", "Consumer"]):
            result = subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *arguments],
                                    cwd=tmp, capture_output=True, timeout=180, check=False)
            ensure(result.returncode == 0, f"kernel replay failed: {(result.stdout + result.stderr)[-3000:]!r}")


def cases() -> list[Case]:
    return [Case("module-local deterministic locked binder identities", _in_memory),
            Case("kernel composes stable locked providers with different binder types", _native_replay,
                 slow=True, lane="toolchain")]
