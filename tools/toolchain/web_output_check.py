# SPDX-License-Identifier: Apache-2.0
"""Independent client and corruption controls for the optional Boolean web backend."""

import tempfile
from pathlib import Path

from toolchain import translate, web_output


def qualify(root: Path) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="vela-web-client-") as tmp:
        directory = Path(tmp)
        output = directory / "client.mjs"
        client = web_output.publish(root / "examples/expressions.vela", "Changed", output)
        if client["boolean_results"] != [False, True, True, False]:
            raise ValueError("playground Changed disagrees with its four independently expected rows")
        source = directory / "controls.vela"
        source.write_bytes(b"// UTF-8 \xf0\x9f\x8c\x99\r\nmodule Controls;\r\n"
                           b"public bool Always() => true;\r\n"
                           b"public bool Select(bool x, bool y) { return !x && (y == true || false); }\r\n"
                           b"public bool End(bool a, bool b, bool c, bool d, bool e, bool f, bool g, bool h) => a && h;")
        for entry, expected in (("Always", [True]), ("End", [i >= 128 and i % 2 == 1 for i in range(256)]),
                                ("Select", [False, True, False, False])):
            observed = web_output.publish(source, entry, output)
            if observed["boolean_results"] != expected:
                raise ValueError(f"web client {entry} disagrees with its independently expected table")
        code = output.read_bytes()
        gallina = translate(source.read_bytes()).gallina
        for original, replacement in ((b"(!p0)", b"(!p1)"), (b" && ", b" || ")):
            if code.count(original) != 1:
                raise ValueError("web corruption control did not locate its selected operand or operator")
            try:
                web_output._qualify(code.replace(original, replacement), gallina, "Vela_Controls.f_Select", 2)
            except ValueError as error:
                if "rocq refused web correspondence" not in str(error) or "eq_refl" not in str(error):
                    raise
            else:
                raise ValueError("kernel accepted a changed Boolean output")
    return {"playground": client, "independent_input_rows": 265, "refused_kernel_mutations": 2}
