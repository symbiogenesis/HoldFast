# SPDX-License-Identifier: Apache-2.0
"""Independent generated-position and freshness controls for the Gallina map."""

import json
import tempfile
from pathlib import Path

from toolchain import gallina_source_map as maps
from toolchain import parser


def qualify(root: Path, node: Path) -> dict[str, object]:
    # Repeated concrete word literals exercise the Gallina emitter's sharing
    # pass, which prepends local declarations and moves every authored site.
    module = ("module Map;\r\n"
              "/* 🗺 */ public definition u32 Sum() => /* 🧭 */ 1u32 + 2u32;\r\n"
              "public definition u32 Diff() => 7u32 - 4u32;\r\n"
              + "".join(f"definition u32 More{i}() => 1u32 + 2u32;\r\n" for i in range(160)))
    with tempfile.TemporaryDirectory() as temporary, parser.cached_build(root) as compiled:
        directory = Path(temporary)
        path = directory / "arithmetic map.hf"
        source = module.encode()
        path.write_bytes(source)
        files = maps._compile(compiled, path)
        for name, data in files.items():
            (directory / name).write_bytes(data)
        lines = files[maps.GALLINA].decode().split("\n")

        def find(prefix: str) -> int:
            return next(i for i, line in enumerate(lines) if line.startswith(prefix))

        first = find("Definition holdfast_d0_Sum ")
        # The prelude contains its own lemmas. Identify the synthesized theorem
        # from the independently counted source bytes and the spelling in Gallina.
        operation = b"1u32 + 2u32"
        start = source.index(operation)
        proof = find(f"Lemma holdfast_word_{start}_{start + len(operation)}_0 ")
        second_start = source.index(b"7u32 - 4u32")
        second = find(f"Lemma holdfast_word_{second_start}_{second_start + len(operation)}_1 ")
        helper = find("Local Definition holdfast_word_literal_")
        positions = [(0, 0), (helper, 3), (first, 11), (proof, 0), (proof + 1, 5),
                     (proof + 1, len(lines[proof + 1])), (proof + 2, 0), (second, 8), (len(lines) - 2, 2)]
        uri = ("holdfast-source://sha256/89063eadeb30b5ddeccc2824965e4148e6ccce98a9a80afab5fe01a26fcf2fed/"
               "arithmetic%20map.hf")
        expected = [None, None, [uri, 1, 9], [uri, 1, 49], [uri, 1, 49],
                    None, None, [uri, 2, 32], None]
        observed = maps.read_positions(compiled, path, files, directory, node, positions)
        if observed != expected:
            raise ValueError(f"source map reader disagrees at generated controls: {observed}")
        manifest = json.loads(files[maps.MANIFEST])
        origin = next(row for row in manifest["origins"] if row["first_line"] == proof)
        owner = source.index(b"public definition u32 Sum")
        if (origin["stage"] != "word-equation" or origin["source"] != [start, start + len(operation)]
                or origin["declaration"] != [owner, source.index(b";", owner) + 1]):
            raise ValueError("generated word proof lost its operation or owning declaration")

        refused = []
        for name in (maps.MAP, maps.GALLINA, maps.MANIFEST):
            (directory / name).write_bytes(files[name] + b" ")
            try:
                maps.read_positions(compiled, path, files, directory, directory / "absent-reader", positions)
            except ValueError as error:
                if f"stale or changed source map input: {name}" != str(error):
                    raise
                refused.append(name)
            else:
                raise ValueError(f"changed {name} reached the reader")
            (directory / name).write_bytes(files[name])
        path.write_bytes(source.replace(b"7u32 - 4u32", b"7u32 - 3u32"))
        changed = maps._compile(compiled, path)
        try:
            maps.read_positions(compiled, path, changed, directory, directory / "absent-reader", positions)
        except ValueError as error:
            if "stale or changed source map input" not in str(error):
                raise
            refused.append("source")
        else:
            raise ValueError("changed HoldFast source reached the reader")
    return {"status": "qualified", "reader": maps.NODE_VERSION, "reader_sha256": maps.NODE_SHA256,
            "source_sha256": manifest["source_sha256"], "map_sha256": manifest["map_sha256"],
            "gallina_sha256": manifest["gallina_sha256"], "producer": manifest["producer"],
            "generated_positions": positions, "original_positions": observed, "refusals": refused}
