# SPDX-License-Identifier: Apache-2.0
"""A proof consumer of the packet validator's public outcome contract."""

import re
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, first_slice, parser, proofenv, rocq_cache, solver_ledger
from toolchain.ast import HoldFastError

INDEPENDENT_CASES = True

CLIENT = b"""module Protocol.Consumer;
import HoldFast.FirstSlice;
public definition Span<byte> Destination() => Span.AllocZeroed(64usize, 8usize);
public definition Span<byte> ConflictingHeader() => MakePacket8(128usize, 0x56u8, 0x05u8, 0x00u8, 0x00u8,
    0x11u8, 0x22u8, 0x33u8, 0x44u8);
public theorem ObserveHeader(ref Span<byte> dst, in Span<byte> pkt)
    requires dst.CanRead
    requires dst.CanWrite
    requires pkt.CanRead
    ensures PacketOutcome(PrepareAndValidatePacket(ref dst, in pkt)) == SpecPacketOutcome(in dst, in pkt)
    proof
    {
        assert PacketOutcome(PrepareAndValidatePacket(ref dst, in pkt)) == SpecPacketOutcome(in dst, in pkt);
    }
"""


def _opaque_error_precedence() -> None:
    root = TOOLS.parent
    source = (root / first_slice.EXAMPLE).read_bytes()
    contract = b"ensures PacketOutcome(result) == SpecPacketOutcome(in old(dst), in pkt)"
    ensure(source.count(contract) == 1, "exact outcome contract moved")
    with parser.cached_build(root) as compiled:
        client = (CLIENT, parser.parse_source(compiled, CLIENT, surface=True))

        def build(provider: bytes) -> str:
            parsed = parser.parse_source(compiled, provider, surface=True)
            package = elaborate.elaborate_package([(provider, parsed), client])
            return package["Protocol.Consumer"].gallina

        gallina = build(source)
        ensure(not solver_ledger.ledger(gallina), "the packet client or its provider needed a solver assumption")
        weak = source.replace(contract, b"")
        with raises(HoldFastError, msg="an opaque caller recovered the unpublished error law") as refusal:
            build(weak)
        error = refusal.exception
        ensure(error.kind == "type" and "module 'Protocol.Consumer': assertion could not be established" in error.message
               and error.line == CLIENT[:CLIENT.index(b"        assert ")].count(b"\n") + 1,
               f"weak contract missed the caller's assertion: {error}")

        # Check the provider law before its scenario theorems enter scope.
        provider = source.split(b"public theorem ValidateEmptyPacketOk(", 1)[0]
        branch = b"return Err(BadMagicOrFlags);"
        ensure(provider.count(branch) == 1, "bad-header exit moved")
        wrong = provider.replace(branch, b"return Err(if (payloadLen > 4) LengthOutOfBounds else BadMagicOrFlags);")
        parsed = parser.parse_source(compiled, wrong, surface=True)
        with raises(HoldFastError, msg="provider law accepted wrong error precedence with identical writes") as refusal:
            elaborate.elaborate(wrong, parsed)
        error = refusal.exception
        ensure(error.kind == "type" and error.line == wrong[:wrong.index(contract)].count(b"\n") + 1,
               f"wrong error missed the provider's public law: {error}")

    def symbol(suffix: str) -> str:
        [match] = re.finditer(rf"^Definition (\w+_{suffix}) :", gallina, re.MULTILINE)
        return str(match[1])

    [module] = re.findall(r"^Module (HoldFastPackage_\w+)\.$", gallina, re.MULTILINE)
    validate = symbol("PrepareAndValidatePacket")
    ensure(f"Opaque {validate}." in gallina, "client was allowed to unfold the validator")
    fixture = f"""
Import {module}.
Definition dst := {symbol("Destination")} tt.
Definition pkt := {symbol("ConflictingHeader")} tt.
Example bad_flags_before_length :
  {symbol("PacketOutcome")} ({validate} dst pkt) = holdfast_Result_Err _ _ ({symbol("ValidationError_BadMagicOrFlags")} tt)
  := {symbol("ObserveHeader")} dst pkt eq_refl eq_refl eq_refl.
"""
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + fixture, directory, compiler=compiler)
        (directory / "Consumer.v").write_text(unit_text, encoding="utf-8")
        output = subprocess.run([*compiler, "Consumer.v"], cwd=directory, capture_output=True, timeout=180, check=False)
        ensure(output.returncode == 0, f"rocq c refused the opaque caller: {output.stderr[-1800:]!r}")
        rocq_cache.check_kernel(directory, ["HoldFastPrelude", "Consumer"] if used_prelude else ["Consumer"])


def cases() -> list[Case]:
    return [Case("packet caller derives exact competing error from opaque validator",
                 _opaque_error_precedence, lane="toolchain")]
