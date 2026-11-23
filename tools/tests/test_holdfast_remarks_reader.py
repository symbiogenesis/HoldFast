# SPDX-License-Identifier: Apache-2.0
"""Reject changed LLVM observations even when the aggregate decision count agrees."""

import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from toolchain import remarks_reader


def _reader_boundary() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / "llvm-remarkutil"
        path.write_bytes(b"unqualified executable")
        with patch.object(remarks_reader.subprocess, "run", side_effect=AssertionError("reader executed before pin check")), raises(ValueError):
            remarks_reader.qualify(path)
    counts = {"f_Render,2"}
    for returned, message in (([b"binary", b"changed caller", b"oracle", b"expected caller"], "decisions"),
                              ([b"binary", b"same", b"oracle", b"same", b"Function,Count\nf_Bad,2\n"], "per function"),
                              ([b"binary", b"same", b"oracle", b"same", b"Function,Count\nf_Render,2\nf_Render,2\n"], "per function")):
        with patch.object(remarks_reader, "_run", side_effect=returned), raises(ValueError) as caught:
            remarks_reader._observe(Path("reader"), b"actual", b"oracle", counts)
        ensure(message in str(caught.exception), "reader observation mismatch reached the wrong refusal")


def cases() -> list[Case]:
    return [Case("LLVM reader pins, call origins and per-function counts", _reader_boundary)]
