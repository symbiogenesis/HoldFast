# SPDX-License-Identifier: Apache-2.0
"""Package navigation, complete reference coverage and retained bundle controls."""

from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from tests.test_holdfast_elaborate import _call, _Fixture, _import_decl, _natural, _type, _variable
from toolchain import packages, parser, scip
from toolchain.elaborate import elaborate_package
from toolchain.elaborate_types import PackageScope
from toolchain.package_navigation import Navigation


def _project() -> None:
    provider, client = _Fixture("Provider"), _Fixture("Client")
    provider.definition("Echo", _type("Nat"), (("x", _type("Nat")),), _variable("x"))
    provider.definition("Unused", _type("Nat"), (), _natural(3))
    _import_decl(client, "Provider", items=(("Echo", None),))
    client.definition("Call", _type("Nat"), (("x", _type("Nat")),), _call("Echo", _variable("x")))
    inputs = [fixture.response() for fixture in (provider, client)]
    scopes = {"Provider": PackageScope("1" * 64, frozenset({"Provider"})),
              "Client": PackageScope("2" * 64, frozenset({"Provider", "Client"}))}
    nav = Navigation()
    outputs = elaborate_package(inputs, scopes=scopes, navigation=nav)
    sources = dict(zip(scopes, (source for source, _ in inputs), strict=True))
    ensure(scip._complete("Provider", outputs["Provider"], nav), "complete scalar definitions marked partial")
    ensure(not scip._complete("Client", outputs["Client"], nav), "unqualified import coverage marked complete")
    uses = [(use.module, sources[use.module][use.start:use.end], dest.module,
             sources[dest.module][dest.start:dest.end]) for use, dest in nav.references]
    ensure(sorted(uses) == sorted([("Client", b"Echo", "Provider", b"Echo"), ("Provider", b"x", "Provider", b"x"),
                                   ("Client", b"x", "Client", b"x")]), "incorrect imported/local binding")
    ensure(all(nav.declarations[dest].name != "Unused" for _, dest in nav.references), "invented a reference")
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        closure = packages.Closure({"packages": {
            "pkg": {"revision": "v1", "instance": "fixed",
                    "modules": {module: module + ".hf" for module in outputs}}}}, sources, scopes, set())
        dest = root / "index"
        def checked(*_args: object, navigation: Navigation) -> tuple[bytes, packages.Closure, object]:
            return b"locked", closure, elaborate_package(inputs, scopes=scopes, navigation=navigation)
        with patch.object(packages, "checked_modules", side_effect=checked), patch.object(scip, "_current_inputs"):

            exported = scip.export(root, root, root / "lock", dest)
            ensure(exported["complete"] is False and (dest / "index.scip").is_file(), "missing partial index")
            ensure(scip.check(root, root, root / "lock", dest)["status"] == "current", "fresh bundle refused")
            with raises(ValueError, msg="incomplete index asserted absence of references") as raised:
                scip.check(root, root, root / "lock", dest, require_complete=True)
            ensure("incomplete" in str(raised.exception), "complete-only handoff reached the wrong refusal")
            for path in (dest / "index.scip", dest / "manifest.json", dest / "__generated__/Provider.v",
                         dest / "pkg/v1/Client.hf"):
                original = path.read_bytes()
                path.write_bytes(b"X" + original[1:])
                with raises(ValueError, msg=f"corrupt SCIP handoff accepted: {path}") as raised:
                    scip.check(root, root, root / "lock", dest)
                error = raised.exception
                ensure("stale or corrupt" in str(error), f"unexpected corruption refusal: {error}")
                path.write_bytes(original)


def _producer_changed() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        lock = root / "package.lock"
        lock.write_bytes(b'{"root":["main","v1"],"packages":{},"producer":{"revision":"old"}}')
        manifest: packages.Object = {"lock_sha256": packages._sha(lock.read_bytes())}
        with (patch.object(parser, "cached_build"), patch.object(packages, "_recheck_parser"),
              patch.object(packages, "_producer", return_value={"revision": "new"})):
            with raises(ValueError, msg="accepted a producer replaced during SCIP publication") as raised:
                scip._current_inputs(root, root, lock, manifest)
            ensure("compiler or parser changed" in str(raised.exception), "changed producer reached the wrong refusal")


def cases() -> list[Case]:
    return [Case("locked-import-resolution-coverage-and-stale-scip-handoffs", _project),
            Case("changed-compiler-refused-at-scip-handoff", _producer_changed)]
