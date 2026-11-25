# SPDX-License-Identifier: Apache-2.0
"""Positive and negative semantic lint controls for control flow and proof authoring."""

import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure
from tests.test_holdfast_elaboration_cli import _invoke
from toolchain import elaborate, elaborate_flow_lints, parser

_ROOT = Path(__file__).resolve().parents[2]

_SOURCE = b"""module FlowLints;

private bool Compare(bool p) => p == true;

private Nat Always(Nat n)
    requires n < 4
{
    if (n < 8) { return n; }
    else { return 0; }
}

private Nat Vary()
{
    var Nat total = 0;
    foreach (let i in 0..2)
    {
        if (i == 0) { total += 1; }
    }
    foreach (let j in 2..2) { total += j; }
    return total;
}

private Result<u8, ArithmeticError> SafeAdd(u8 a, u8 b)
    requires a <= 10 && b <= 10
{
    return CheckedAdd(a, b);
}

private Result<u8, ArithmeticError> MaybeAdd(u8 a, u8 b)
{
    return CheckedAdd(a, b);
}

private Result<u8, ConversionError> SafeConvert(Nat n)
    requires n < 16
{
    return u8.TryFrom(n);
}

private Result<Nat, ArithmeticError> Forward(Result<Nat, ArithmeticError> value)
{
    return match (value) { Ok(x) => Ok(x), Err(e) => Err(e) };
}

public union Option<TValue>
{
    None();
    Some(TValue Value);
}

private Option<Nat> ForwardOption(Option<Nat> original)
{
    match (original)
    {
        None => { return None<Nat>; },
        Some(value) => { return Some<Nat>(value); }
    }
}

private Unit Initialize(ref byte value)
    effects writes(value)
{
    value = 1byte;
    return;
}

private Unit ProjectedCall()
{
    var buf = Span.AllocZeroed(1usize);
    Initialize(ref buf[0usize]);
    return;
}

private definition Nat Id<ghost Nat unused>(Nat n)
    decreases n
    => n;

private Nat Limits(Nat n)
    requires n >= 1
{
    foreach (let i in 0..n)
        invariant i <= n
        invariant n >= 1
        decreases n - i
    {}
    return n;
}

private lemma Repeated(Nat n)
    ensures n == n
proof
{
    assert n == n;
    assert n == n;
    assert n == n;
}

private lemma Calculation(Nat a, Nat b, Nat c)
    requires a == b
    requires b == c
    ensures a == c
proof
{
    calc
    {
        assert a == b;
        assert b == b;
        assert b == c;
    }
}
"""

_ANNOTATIONS = b"""module AnnotationLint;
private definition T Id<T>(T x) => x;
public union Option<TValue>
{
    None();
    Some(TValue Value);
}
private Option<Nat> Empty() => None<Nat>;
private Nat Use(Nat n)
{
    let Nat copy = n;
    return Id<Nat>(copy);
}
private u8 Width()
{
    let u8 byteValue = 1;
    return byteValue;
}
"""


def _flow() -> None:
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "flow.hf"
        path.write_bytes(_SOURCE)
        code, stdout, stderr = _invoke(["lint", str(path)])
        ensure(code == 0 and not stdout, stderr)
        expected = {
            "HOLDFAST103": 1, "HOLDFAST125": 2, "HOLDFAST126": 2, "HOLDFAST127": 2,
            "HOLDFAST128": 1, "HOLDFAST129": 1, "HOLDFAST130": 1, "HOLDFAST131": 3, "HOLDFAST132": 1,
        }
        for rule, count in expected.items():
            ensure(stderr.count(f"warning {rule}:") == count, f"expected {count} {rule} findings:\n{stderr}")
        ensure("HOLDFAST123" not in stderr, "suggested an initialization loan for an indexed caller")
        ensure(path.read_bytes() == _SOURCE, "semantic lint changed authored source")


def _annotations() -> None:
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "annotation.hf"
        path.write_bytes(_ANNOTATIONS)
        code, stdout, stderr = _invoke(["lint", str(path)])
        ensure(code == 0 and not stdout and "HOLDFAST133" not in stderr, stderr)
        code, stdout, stderr = _invoke(["lint", str(path), "--warn", "HOLDFAST133"])
        ensure(code == 0 and not stdout and stderr.count("warning HOLDFAST133:") == 3, stderr)
        code, stdout, stderr = _invoke(["lint", str(path), "--deny", "HOLDFAST133"])
        ensure(code == 1 and not stdout and stderr.count("error HOLDFAST133:") == 3
               and path.read_bytes() == _ANNOTATIONS, stderr)


def _proof_output() -> None:
    source = (_ROOT / "examples" / "first_slice.hf").read_bytes()
    with parser.cached_build(_ROOT) as compiled:
        parsed = parser.parse_source(compiled, source, surface=True)
    with patch.object(elaborate_flow_lints, "_truth", return_value=None) as suppressed:
        reference = elaborate.elaborate(source, parsed)
    checked = elaborate.elaborate(source, parsed)
    ensure(suppressed.called and checked.gallina == reference.gallina,
           "an advisory flow probe changed emitted packet proof terms")


def cases() -> list[Case]:
    return [Case("checked control-flow and proof lints", _flow, lane="guest"),
            Case("opt-in annotation lint replays exact inference", _annotations, lane="guest"),
            Case("lint probes preserve emitted proof terms", _proof_output, lane="guest")]
