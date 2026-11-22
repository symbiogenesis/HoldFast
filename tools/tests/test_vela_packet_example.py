# SPDX-License-Identifier: Apache-2.0
"""Run the packet walkthrough's examples and check the three documented edits."""

import re
import sys
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import VelaError
from toolchain.cli.vela_parser import (
    _compile_bridge,
    _packet_bytes,
    _packet_directory,
    _packet_example,
)
from toolchain.first_slice import EXAMPLE


def _walkthrough_outputs() -> None:
    root = TOOLS.parent
    guide = (root / "docs/tooling/packet-walkthrough.md").read_text(encoding="utf-8")
    steps = re.findall(r'^```console\npython tools/run\.py vela-parser packet-example "([^"]+)"\n```'
                       r'.*?^```text\n(.*?)\n```', guide, re.MULTILINE | re.DOTALL)
    ensure(len(steps) == 3, "expected the framing, checksum and returned-view examples")
    for argument, expected in steps:
        output = _packet_example(root, root / EXAMPLE, _packet_bytes(argument))
        ensure(expected in output, f"packet {argument} disagrees with the walkthrough:\n{output}")


def _walkthrough_edits() -> None:
    root = TOOLS.parent
    validator = (root / EXAMPLE).read_text(encoding="utf-8")
    view = "let payloadView = Span.ReadOnly(Span.Slice(dst, 4, payloadLen));"
    edits = (
        ("if (dst.Length < 8 || pkt.Length < 4 ||", "if (dst.Length < 8 || pkt.Length < 3 ||",
         "Span index is within Span.Length bounds"),
        ("        Span.Fill(ref dst, 0, 8, 0x00);", "        Span.Fill(ref dst, 0, 9, 0x00);",
         "Span.Fill subrange"),
        (view, view.replace("let ", "var ") + "\n    if (payloadLen > 0) { payloadView[0] = 0x00; }",
         "write permission (Span.CanWrite)"),
    )
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "packet.vela"
        for before, after, diagnostic in edits:
            ensure(validator.count(before) == 1, f"walkthrough edit became ambiguous: {before}")
            path.write_text(validator.replace(before, after), encoding="utf-8")
            with raises(VelaError, msg=f"expected walkthrough edit to fail: {after}") as raised:
                _packet_example(root, path, b"")
            error = raised.exception
            ensure(error.kind == "type" and diagnostic in error.message, str(error))


def cases() -> list[Case]:
    return [Case("failed bridge output cleans its files and can be retried", _bridge_retry),
            Case("three packet walkthrough results", _walkthrough_outputs, lane="toolchain"),
            Case("three packet walkthrough source edits", _walkthrough_edits, lane="toolchain")]


def _bridge_retry() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        destination = Path(temporary) / "packet build"
        try:
            with _packet_directory(destination) as output:
                (output / "packet.c").write_bytes(b"failed input")
                _compile_bridge(output, sys.executable, ["-c", "raise SystemExit(7)"],
                                output / "packet.c", output / "packet-example", export=True)
        except RuntimeError as error:
            ensure("C build failed" in str(error), "lost compilation failure")
        ensure(not destination.exists(), "partial destination survived failed build")
        with _packet_directory(destination) as output:
            (output / "packet.c").write_bytes(b"accepted")
        try:
            with _packet_directory(destination):
                raise AssertionError("overwrote an existing build directory")
        except FileExistsError:
            ensure((destination / "packet.c").read_bytes() == b"accepted", "disturbed previous output")
