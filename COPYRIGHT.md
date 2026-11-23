# Repository licensing

Copyright 2026 Edward Miller.

[REUSE.toml](REUSE.toml) assigns the licenses for this repository. The
[license texts](LICENSES/) govern their terms. [THIRD-PARTY.md](THIRD-PARTY.md)
records upstream terms and the scope of HoldFast's use.

## Repository licenses

| Path | License |
| --- | --- |
| Original Markdown and `docs/evidence/*.json` | [CC-BY-4.0](LICENSES/CC-BY-4.0.txt) |
| Original code, examples, site assets, configuration, and dependency lock metadata | [Apache-2.0](LICENSES/Apache-2.0.txt) |
| Embedded Octicons GitHub mark in the [playground](docs/index.html) | [MIT](LICENSES/MIT.txt) |
| Verbatim texts under [LICENSES/](LICENSES/) | Terms stated by each license steward |

## File markings

Open each original file that supports an in-file marker with the SPDX
identifier in that format's comment syntax.

<!-- REUSE-IgnoreStart -->

```text
# SPDX-License-Identifier: Apache-2.0
```

<!-- REUSE-IgnoreEnd -->

[REUSE.toml](REUSE.toml) supplies copyright and license assignments by path.
`python tools/run.py check` verifies assignments and opening marks for tracked
files, checks additional SPDX license declarations against those assignments,
and verifies the embedded MIT notice and the tracked license texts. The manifest uses
root-level `closest` annotations with literal paths, `*` within a path component,
and `**` as a recursive component. The last matching annotation supplies the
assignment when patterns overlap. [Validation commands](tools/README.md#commands)

Run the [FSFE tool](https://reuse.software/dev/) from the repository root with
the `reuse lint` command for a full REUSE specification audit.

## Terms this tree does not carry

No tracked file is subject to a reciprocal or non-commercial license.
Verify the selected revision's own license and dependency notices before
incorporating an upstream. Record the scope of use and distribution in
[THIRD-PARTY.md](THIRD-PARTY.md).
