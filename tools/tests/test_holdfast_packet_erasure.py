# SPDX-License-Identifier: Apache-2.0
"""Exercise proof erasure through packet elaboration, C lowering and execution."""

import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, first_slice, parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError


def _kernel_check(gallina: str) -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        (directory / "Phases.v").write_text(gallina, encoding="utf-8", newline="\n")
        for command in (["rocq", "c", "-q", "Phases.v"], ["rocqchk", "-silent", "Phases"]):
            process = subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *command],
                                     cwd=directory, capture_output=True, check=False, timeout=180)
            ensure(process.returncode == 0, f"{command} refused proof replay: {process.stderr[-1600:]!r}")


def _inline_packet_proofs() -> None:
    root = TOOLS.parent
    source = (root / first_slice.EXAMPLE).read_bytes()
    body = b"    var u8 acc = 0x5A ^ rawLen;"
    ensure(source.count(body) == 1, "missing checksum insertion site")
    assertion = b"    assert payloadLen <= 4usize;"
    proof = b"""
    proof {
        let byteBefore = rawLen;
        assert byteBefore == rawLen;
    }
    calc { assert rawLen == rawLen; }
"""
    annotated = source.replace(body, assertion + proof + body)
    with parser.cached_build(root) as compiled:
        def lower(program: bytes, *, replay: bool = False) -> str:
            ast = parser.parse_source(compiled, program, surface=True)
            checked = elaborate.elaborate(program, ast)
            ensure(not solver_ledger.ledger(checked.gallina), "erasure case has solver-trusted obligations")
            if replay:
                _kernel_check(checked.gallina)
            return first_slice.lower_to_c(program, ast, checked=checked)[0]

        original_c = lower(source)
        annotated_c = lower(annotated, replay=True)
        invalid = annotated.replace(assertion, b"    assert 0u8 == 1u8;")
        with raises(HoldFastError, msg="false inline proof reached C lowering") as failure:
            lower(invalid)
        ensure(failure.exception.line == annotated[:annotated.index(assertion)].count(b"\n") + 1
               and "assertion" in str(failure.exception), f"wrong refusal: {failure.exception}")

    with tempfile.TemporaryDirectory() as temporary:
        binary = Path(temporary) / "packet"

        def build_and_run(program: str, optimization: str) -> bytes:
            subprocess.run(["cc", "-std=c11", optimization, "-x", "c", "-", "-o", str(binary)],
                           input=program.encode(), check=True, timeout=30)
            subprocess.run([str(binary)], check=True, timeout=5)
            return binary.read_bytes()

        for optimization in ("-O0", "-O2"):
            ensure(build_and_run(original_c, optimization) == build_and_run(annotated_c, optimization),
                   f"inline proof changed the guest executable at {optimization}")


def _proof_resource_boundary() -> None:
    declarations = b"""module Trial.Phases;
private bool Init(out u8 slot) effects writes(slot) { slot = 7u8; return true; }
private bool Bump(ref u8 slot) effects writes(slot) { slot = 1u8; return true; }
private u8 Read(in u8 slot) effects reads(slot) => slot;
"""
    readonly = b"""public u8 Observe(in u8 slot) effects none {
    proof { let seen = Read(in slot); assert seen == slot; }
    calc { let same = slot; assert same == slot; }
    return 0u8;
}
public Unit Produce(out u8 slot) effects writes(slot) {
    slot = 7u8;
    assert slot == 7u8;
    return;
}
public u8 AfterRead(ref u8 slot) effects writes(slot) {
    let writable = ref slot;
    writable = 9u8;
    return slot;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(body: bytes) -> str:
            program = declarations + body
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(readonly)
        ensure(not solver_ledger.ledger(gallina), "read-only proof introduced an assumption")
        for signature, statement, diagnostic in (
            ("out u8 slot", "assert Init(out slot) == true;", "'out' argument"),
            ("out u8 slot", "proof { let ok = Init(out slot); assert ok == true; }", "'out' argument"),
            ("ref u8 slot", "calc { assert Bump(ref slot) == true; }", "'ref' argument"),
            ("u8 slot", "proof { let taken = move slot; assert taken == taken; }", "move a runtime value"),
        ):
            body = f"public Unit Bad({signature}) {{\n    {statement}\n    return;\n}}\n".encode()
            with raises(HoldFastError, msg=f"erased resource operation accepted: {statement}") as failure:
                check(body)
            ensure(failure.exception.line == declarations.count(b"\n") + 2
                   and diagnostic in str(failure.exception), f"wrong phase refusal: {failure.exception}")
        with raises(HoldFastError, msg="executable read escaped its declared effects") as failure:
            check(readonly.replace(b"return 0u8;", b"return Read(in slot);"))
        ensure("not declared in effects reads" in str(failure.exception), f"wrong runtime refusal: {failure.exception}")
        use_name = b"""public Nat Reuse(ref Nat slot, Nat n) {
    proof { let inner = ref slot; assert inner == slot; }
    match (n) {
        Succ(inner) => { inner = 6; return slot; }
        0 => { return slot; }
    }
}
"""
        with raises(HoldFastError, msg="a proof-local alias made a later pattern binding writable") as failure:
            check(use_name)
        ensure("cannot assign to immutable binding 'inner'" in str(failure.exception)
               and failure.exception.line == declarations.count(b"\n") + 4, f"wrong alias refusal: {failure.exception}")

    _kernel_check(gallina)


def cases() -> list[Case]:
    return [Case("inline proofs erase from the compiled packet", _inline_packet_proofs, lane="guest"),
            Case("erased proofs preserve runtime resource duties", _proof_resource_boundary, lane="guest")]
