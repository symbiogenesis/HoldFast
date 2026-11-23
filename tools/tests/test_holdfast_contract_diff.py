# SPDX-License-Identifier: Apache-2.0
"""Review the authored delta through the native parser command."""

import hashlib
import json
import tempfile
from pathlib import Path

from tests.harness import Case, ensure
from tests.test_holdfast_elaboration_cli import _invoke


def _public_changes() -> None:
    original = b"""module Review;
import Base as B;
public Nat Body(Nat value) => value;
public Nat Check(Nat value) requires value > 0 ensures result > 0 effects Read => value;
public union Answer { Yes(); }
public definition Nat Limit() => 4;
public definition bool Gone() => true;
"""
    revised = b"""module Review;
import Base as Base;
public Nat Body(Nat value) => value + 1;
public Nat Check(Nat value) requires value > 1 ensures result >= 0 effects Read, Write => value;
public union Answer { Yes(); No(); }
public definition Nat Limit() => 8;
public definition bool Added() => true;
"""
    with tempfile.TemporaryDirectory() as temp:
        old, new = Path(temp) / "old.hf", Path(temp) / "new.hf"
        old.write_bytes(original)
        new.write_bytes(revised)
        code, out, err = _invoke(["diff-contract", str(old), str(new)])
        ensure(code == 0 and not err, f"public contract comparison refused: {err}")
        report = json.loads(out)
        ensure(report["status"] == "authored-contract-diff" and report["module"] == "Review", f"bad report: {report}")
        ensure(report["baseline_sha256"] == hashlib.sha256(original).hexdigest()
               and report["candidate_sha256"] == hashlib.sha256(revised).hexdigest(), "detached contract report")
        ensure(set(report["added"]) == {"Added"} and set(report["removed"]) == {"Gone"}, "missing declaration delta")
        changes = report["changed"]
        ensure(set(changes) == {"Check", "Answer", "Limit"} and set(changes["Check"]) == {"contracts"}
               and set(changes["Answer"]) == {"constructors"} and set(changes["Limit"]) == {"value"},
               "public contract changes lost or an ordinary implementation body leaked")
        clauses = changes["Check"]["contracts"]
        ensure([row.get("role", row["kind"]) for row in clauses["after"]] == ["requires", "ensures", "effects"]
               and len(clauses["after"][2]["values"]) == 2 and report["resolution"],
               "precondition, postcondition, authority or import delta missing")
        new.write_bytes(b"// extra trivia\n" + original)
        code, out, err = _invoke(["diff-contract", str(old), str(new)])
        ensure(code == 0 and not err and not json.loads(out)["changed"] and not json.loads(out)["resolution"],
               "trivia changed the authored contract")
        new.write_bytes(revised.replace(b"module Review", b"module Unrelated"))
        code, out, err = _invoke(["diff-contract", str(old), str(new)])
        ensure(code == 1 and not out and "same module" in err, "accepted unrelated modules as revisions")


def cases() -> list[Case]:
    return [Case("diff authored public contracts and authority without granting compatibility", _public_changes, lane="toolchain")]
