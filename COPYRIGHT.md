# Copyright and Licensing

Copyright 2026 Edward Miller.

[REUSE.toml](REUSE.toml) assigns the licenses for this repository. The
[license texts](LICENSES/) govern their terms. [THIRD-PARTY.md](THIRD-PARTY.md)
records upstream terms and the scope of Vela's use.

## Repository licenses

| Path | License |
| --- | --- |
| Original Markdown and `docs/evidence/*.json` | [CC-BY-4.0](LICENSES/CC-BY-4.0.txt) |
| Original code, examples, site assets, configuration, and dependency lock metadata | [Apache-2.0](LICENSES/Apache-2.0.txt) |
| Verbatim texts under [LICENSES/](LICENSES/) | Terms stated by each license steward |

## File markings

Open each original file that supports an in-file marker with the SPDX
identifier in that format's comment syntax.

```text
# SPDX-License-Identifier: Apache-2.0
```

[REUSE.toml](REUSE.toml) covers Markdown, JSON and generated lockfiles by path.
`python tools/run.py check` verifies file markings and runs the pinned REUSE
checker. [Validation commands](tools/README.md#commands)

## Terms this tree does not carry

No tracked file is subject to a reciprocal or non-commercial license.
Verify the selected revision's own license and dependency notices before
incorporating an upstream. Record the scope of use and distribution in
[THIRD-PARTY.md](THIRD-PARTY.md).
