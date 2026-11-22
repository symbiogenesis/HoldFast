# SPDX-License-Identifier: Apache-2.0
"""Package navigation, complete reference coverage and retained bundle controls."""

from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from tests.harness import Case, ensure
from tests.test_vela_elaborate import _call, _Fixture, _import_decl, _natural, _type, _variable
from toolchain import packages, scip
from toolchain.elaborate import elaborate_package
from toolchain.elaborate_types import PackageScope
from toolchain.package_navigation import Navigation


def _project() -> None:
    provider, client = _Fixture("Provider"), _Fixture("Client")
    provider.definition("Echo", _type("Nat"), (("x", _type("Nat")),), _variable("x"))
    provider.definition("Unused", _type("Nat"), (), _natural(3))
    _import_decl(client, "Provider")
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
                    "modules": {module: module + ".vela" for module in outputs}}}}, sources, scopes, set())
        dest = root / "index"
        def checked(*args: object, navigation: Navigation) -> tuple[bytes, packages.Closure, object]:
            return b"locked", closure, elaborate_package(inputs, scopes=scopes, navigation=navigation)
        with patch.object(packages, "checked_modules", side_effect=checked), patch.object(scip, "_current_inputs"):

            exported = scip.export(root, root, root / "lock", dest)
            ensure(exported["complete"] is False and (dest / "index.scip").is_file(), "missing partial index")
            ensure(scip.check(root, root, root / "lock", dest)["status"] == "current", "fresh bundle refused")
            try:
                scip.check(root, root, root / "lock", dest, require_complete=True)
            except ValueError as error:
                ensure("incomplete" in str(error), "complete-only handoff reached the wrong refusal")
            else:
                raise AssertionError("incomplete index asserted absence of references")
            for path in (dest / "index.scip", dest / "manifest.json", dest / "__generated__/Provider.v",
                         dest / "pkg/v1/Client.vela"):
                original = path.read_bytes()
                path.write_bytes(b"X" + original[1:])
                try:
                    scip.check(root, root, root / "lock", dest)
                except ValueError as error:
                    ensure("stale or corrupt" in str(error), f"unexpected corruption refusal: {error}")
                else:
                    raise AssertionError(f"corrupt SCIP handoff accepted: {path}")
                path.write_bytes(original)


def cases() -> list[Case]:
    return [Case("locked-import-resolution-coverage-and-stale-scip-handoffs", _project)]
