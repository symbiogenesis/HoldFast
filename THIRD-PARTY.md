# Third-Party Software and References

This file records third-party dependencies, development tools, and reference readings for the HoldFast repository, following [COPYRIGHT.md](COPYRIGHT.md).

## Independent SCIP reader

The locked-package index targets the [SCIP schema at revision `1c2b6db`](https://github.com/scip-code/scip/blob/1c2b6db7e560d5233c944f36e4ac1377cc6963fc/scip.proto),
SHA-256 `b38021b65ef90cbbf6af9c829ff75192859ad9b5da05439ef154bea4ceb2bf03`.
The [offline qualification](tools/toolchain/scip_reader.py) invokes the external
Linux ARM64 `scip print --json` reader and queries its decoded occurrences and
relationships for the current and renamed package. Supply the `scip` executable
from the [v0.10.0 release](https://github.com/scip-code/scip/releases/tag/v0.10.0).
The archive has SHA-256 `6ab677dc2c4bf2955975d0530766152e45daaa988f9404068d8adecacd0bb24c`
and the executable has SHA-256 `2e808bcfc73711f1ab598412ac6ec6f7c68c2c3c07e02f63b05221a2250a357e`.
The selected revision's [license](https://github.com/scip-code/scip/blob/1c2b6db7e560d5233c944f36e4ac1377cc6963fc/LICENSE)
is Apache-2.0. The schema and reader are external development inputs. HoldFast
distributes its own encoder and qualification harness.

The qualification resolves decoded relationship targets after collecting symbols
from all documents. In v0.10.0 the separate `scip lint` command checks each
document's relationships while traversing an unordered document map. It can
report a missing target when it visits a generated definition before its
authored source. [Upstream linter](https://github.com/scip-code/scip/blob/1c2b6db7e560d5233c944f36e4ac1377cc6963fc/cmd/scip/lint.go)

<a id="independent-sarif-importer"></a>

## Independent SARIF importer

The optional [pure batch SARIF qualification](docs/tooling/tooling-protocols.md#qualified-pure-batch-sarif)
uses the external `sarif-tools` 3.0.5 importer with the exact wheels below.
The [release license](https://github.com/microsoft/sarif-tools/blob/v3.0.5/LICENSE)
and wheel license specify MIT, copyright Microsoft Corporation. Qualification imports only the reader API, with `jsonpath-ng` 1.7.0
([release](https://pypi.org/project/jsonpath-ng/1.7.0/)), `ply` 3.11
([release](https://pypi.org/project/ply/3.11/)) and PyYAML 6.0.3
([release](https://pypi.org/project/PyYAML/6.0.3/)). The wheel license files specify the following terms. `jsonpath_ng-1.7.0.dist-info/LICENSE` is Apache-2.0;
PLY's `ply/lex.py` and `ply/yacc.py` carry the three-clause BSD license, copyright
2001–2018 David M. Beazley (Dabeaz LLC); and
`pyyaml-6.0.3.dist-info/licenses/LICENSE` is MIT, copyright 2017–2021 Ingy döt Net
and 2006–2016 Kirill Simonov. The isolated process loads pure Python directly
from the verified wheel ZIPs; PyYAML's native extension and sarif-tools' chart,
HTML and document-export dependencies are not imported. The named PyYAML wheel
is an input archive for pure imports, with no claim to execute its native payload
on other platforms.

| External wheel | SHA-256 |
| --- | --- |
| `sarif_tools-3.0.5-py3-none-any.whl` | `682d22559095ca4a210a401e21f0585fdb8015e826c0d160ab3cbadee326952f` |
| `jsonpath_ng-1.7.0-py3-none-any.whl` | `f3d7f9e848cba1b6da28c55b1c26ff915dc9e0b1ba7e752a53d6da8d5cbd00b6` |
| `ply-3.11-py2.py3-none-any.whl` | `096f9b8350b65ebd2fd1346b12452efe5b9607f7482813ffca50c22722a807ce` |
| `pyyaml-6.0.3-cp314-cp314-manylinux2014_aarch64.manylinux_2_17_aarch64.manylinux_2_28_aarch64.whl` | `501a031947e3a9025ed4405a168e6ef5ae3126c59f90ce0cd6f2bfc477be31b7` |

The schema input is the official
[OASIS SARIF 2.1.0 schema](https://docs.oasis-open.org/sarif/sarif/v2.1.0/os/schemas/sarif-schema-2.1.0.json),
SHA-256 `ad6db49878699b091f3eeb765b6e29e92a34bad4da88664d000c923b549c3a25`.
The [standard's notices](https://docs.oasis-open.org/sarif/sarif/v2.1.0/os/sarif-v2.1.0-os.html)
and [repository license](https://github.com/oasis-tcs/sarif-spec/blob/main/LICENSE.md)
give copyright 2020 OASIS Open, with its stated document,
computer-language-definition and IPR policies. The schema remains an external
development input checked by the existing locked `jsonschema` library; its
contents are not relicensed or vendored into this tree. No upstream schema,
reader, dependency source, wheel or native binary is copied into the tracked
tree, compiler runtime, or a HoldFast/VerifiedOS image. Retained reports contain
HoldFast-authored fixtures, observed records and tool identities. These records
authorize local development use and do not assert a redistribution closure.

## Independent compilation database reader

The native [C bridge qualification](docs/tooling/tooling-protocols.md#locked-mathematical-package-builds)
runs Ubuntu ARM64 `clang-scan-deps` from LLVM 21.1.8,
SHA-256 `268678d396d51830acbe20f958005cecc9ac155de5822807e3390c0ed3cde995`.
The selected [Clang license](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/LICENSE.TXT)
and the installed Ubuntu package's copyright record specify Apache-2.0 with LLVM
exceptions. The reader consumes local compilation databases as an external
development tool. Its executable and upstream source remain outside the repository
and release artifacts.

## LLVM optimization remark reader

The [remarks qualifier](docs/tooling/tooling-protocols.md#compiler-decisions-and-performance-traces)
runs Ubuntu ARM64 `llvm-remarkutil` and `libLLVM.so.21.1` as external development
tools. Both come from LLVM 21.1.8, Ubuntu package revision `1:21.1.8-6ubuntu1`.
The executable SHA-256 is `18bdbf0d5d387911b585cd97786ffcb3dcdcc8a539784a2963e293afdec208a3`
and the shared library SHA-256 is `a8d595321c634d717fe5d8a03396837c5631b389698125b93061b7638d5a6e7c`.
The revision's [LLVM license](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/llvm/LICENSE.TXT)
specifies Apache-2.0 with LLVM Exceptions and identifies separately licensed
third-party components. Ubuntu's `libllvm21` copyright record has SHA-256
`b2ed2fd344e8ddbf2e0c83113bd40fa1853438be61a0ff20af5acd187c07cbf6`.
The tracked tree distributes HoldFast's harness and authored fixture records. LLVM
executables, shared libraries and upstream source stay with the external tool
installation.

<a id="independent-gallina-source-map-reader"></a>
<a id="boolean-web-execution-engine"></a>

## Independent Node.js runtime

The [Gallina source map lookup](tools/toolchain/gallina_source_map.py) uses
`node:module` SourceMap, and the [Boolean web exporter](tools/toolchain/web_output.py)
executes generated ES modules. Both use the external Linux ARM64 Node.js 22.22.1
executable, SHA-256 `1ea16f5e8d590ca819f1db81e61a6bc4c8e7d8b69776c9236f8ebbf717113225`.
Node.js is MIT with separate notices for bundled dependencies. The exporter
outputs HoldFast-generated JavaScript, and the lookup reads HoldFast-generated maps.
[SourceMap API](https://nodejs.org/download/release/v22.22.1/docs/api/module.html#class-modulesourcemap)
· [Release license and notices](https://github.com/nodejs/node/blob/v22.22.1/LICENSE)

## CI environment setup

The [static workflow](.github/workflows/static.yml) invokes `actions/setup-python`
v7.0.0 at `5fda3b95a4ea91299a34e894583c3862153e4b97` to select the Python minor
owned by [tools/pyproject.toml](tools/pyproject.toml). Its revision's
[LICENSE](https://github.com/actions/setup-python/blob/5fda3b95a4ea91299a34e894583c3862153e4b97/LICENSE)
specifies MIT, copyright 2018 GitHub, Inc. and contributors.
The action runs as a hosted development tool with its upstream notices; no action
source or runtime binary is copied into this tree or a HoldFast/VerifiedOS image.
The workflow installs the existing exact `uv` version from that same manifest
and synchronizes the repository's locked Python dependencies.

<a id="browser-editor-assets"></a>

## Browser playground assets

The [HoldFast playground](docs/tooling/playground.md) loads `monaco-editor` 0.55.1's
browser distribution from its version-pinned jsDelivr package URL. The release's
[LICENSE.txt](https://github.com/microsoft/monaco-editor/blob/v0.55.1/LICENSE.txt),
[package manifest](https://github.com/microsoft/monaco-editor/blob/v0.55.1/package.json),
and [third-party notices](https://github.com/microsoft/monaco-editor/blob/v0.55.1/ThirdPartyNotices.txt)
specify MIT for Monaco, copyright Microsoft Corporation. The notices cover
bundled TypeScript, Unicode, DOM, WebGL, HTML, beautifier, and documentation
material under their stated terms. The license permits use,
modification, and distribution with its copyright and permission notice. Browser
assets and upstream notices are served directly from the package CDN rather than
vendored into this repository or shipped in a VerifiedOS image.

The [playground header](docs/index.html) embeds Primer Octicons v19.21.2's
[16-pixel GitHub mark](https://github.com/primer/octicons/blob/v19.21.2/icons/mark-github-16.svg)
as a link to the HoldFast repository. Its [release license](https://github.com/primer/octicons/blob/v19.21.2/LICENSE)
is MIT, copyright 2026 GitHub Inc. Both the hosted and local playgrounds serve
the SVG and license notice inline. Use of the mark follows
[GitHub's logo guidelines](https://brand.github.com/foundations/logo).

<a id="independent-trace-importer"></a>

## Independent trace importer

The optional [pure trace qualification](docs/tooling/pure-prototype.md#bounded-compiler-traces)
uses an externally provisioned Perfetto `v58.2` `trace_processor_shell`, revision
`add693d8b338ba9599dbcbc3e300b1ab8c000897`. Its revision's
[LICENSE](https://github.com/google/perfetto/blob/v58.2/LICENSE)
has SHA-256
`9a682a56cffc9524dfa9b0b1c0dca9cb81a19e96d5bd0793aaf02c08a95ee7ca` and specifies
Apache-2.0 for the principal work, copyright 2017 The Android Open Source
Project, with the file-specific Chromium BSD notice, syntaqlite Apache-2.0
notice, public-domain parser-grammar declaration and Niels Provos BSD notice
stated in that same file. The reader runs only as an independent local
development tool; no upstream source, executable, library or wrapper is copied
into the tracked tree, compiler runtime or a HoldFast/VerifiedOS image. This record
does not authorize a distribution closure.

The harness accepts these exact official standalone prebuilts, checking bytes
before and after qualification and checking their reported source revision:

| Target | Official executable | SHA-256 |
| --- | --- | --- |
| Windows AMD64 | [trace_processor_shell.exe](https://commondatastorage.googleapis.com/perfetto-luci-artifacts/v58.2/windows-amd64/trace_processor_shell.exe) | `adfa6bad3d72be3ba9b83fa2b17b69fa13b3ab1cad0f42e52b86188bd5f0f997` |
| Linux AMD64 | [trace_processor_shell](https://commondatastorage.googleapis.com/perfetto-luci-artifacts/v58.2/linux-amd64/trace_processor_shell) | `58042408e6cc861fb1a731c26bb082dc222285561eaa4e12a48a8b2b90dca7b9` |
| Linux ARM64 | [trace_processor_shell](https://commondatastorage.googleapis.com/perfetto-luci-artifacts/v58.2/linux-arm64/trace_processor_shell) | `0e6e0c5452c505c8d46fe472fd196a0d17d963460727e2ce2013b02aa1309555` |

The command requires the reader path explicitly and performs no downloads or
dependency installation. The executable remains in an ignored external-tool
directory alongside the upstream license; retained reports contain HoldFast-authored
fixture data, SQL observations and tool identities. Qualification of one target
does not claim execution on every target in the pin table or browser UI coverage.

<a id="independent-syntax-consumers"></a>

## Independent syntax consumers

The optional [editor-asset qualification](docs/tooling/highlighting.md) runs
Tree-sitter CLI `0.25.10`, revision
`da6fe9beb4f7f67beb75914ca8e0d48ae48d6406`, as an independent parser/query
consumer and generator. Its revision's
[LICENSE](https://github.com/tree-sitter/tree-sitter/blob/v0.25.10/LICENSE)
specifies MIT, copyright 2018–2024 Max Brunsfeld, and has SHA-256
`5f9cf9fb6acb1972b35ae29119ce563bb60ec097656bc4b69b9bac2d04c7a147`.
The official
[Linux ARM64 release archive](https://github.com/tree-sitter/tree-sitter/releases/download/v0.25.10/tree-sitter-linux-arm64.gz)
has SHA-256 `07fbff8ae0eeb0d3e496e14fc1a30dcc730cc2c97d70e601e5357f2e51958af5`;
its executable has SHA-256
`6329ea4be486c26ef87fdc45ead60c1b1fb9ffab62fe9bd295932ec8e0645751`.
Generated parser C, Tree-sitter runtime headers, compiled language libraries and
the CLI remain in isolated/ignored development directories with upstream
notices; none is copied into tracked source or a HoldFast/VerifiedOS image. The
tracked grammar, queries and external scanner are original Apache-2.0 work.

The lexical consumer is Microsoft's VS Code tokenization engine
[`vscode-textmate` `9.2.0`](https://registry.npmjs.org/vscode-textmate/-/vscode-textmate-9.2.0.tgz)
(archive SHA-256 `1f4aed19818315f5b2822bf485eb1a9efc02b0a8b88f5d4e9409d6d289ff61cf`)
with [`vscode-oniguruma` `2.0.1`](https://registry.npmjs.org/vscode-oniguruma/-/vscode-oniguruma-2.0.1.tgz)
(archive SHA-256 `3b42911fd9609f2cc3b9c6dd52236b3da73780e633aa7dc381267006b7e7da21`),
running on the [Node.js host runtime](#independent-nodejs-runtime). Both packages
specify MIT, copyright Microsoft Corporation.
`vscode-textmate/LICENSE.md` SHA-256
`b5cb7ff7859e7d282d98fc43ab081b0dda5dc659dc3385cf65740c759a7e6a6c`
and `vscode-oniguruma/LICENSE.txt` SHA-256
`ddde8aba8fe72b4830e27901fc78733eb6db7b6c653161075de213a6adeda3fd`.
Oniguruma's package `NOTICES.txt` has SHA-256
`615d94d89eacc046241518c247f6650a5df80d1adf4b284a756f500867620b35`.
The bundled Oniguruma `6.9.5_rev1` is BSD-2-Clause, copyright 2002-2020 K. Kosako.
Their pinned JavaScript/Wasm implementation bytes and release metadata are
checked by the [qualifier](tools/toolchain/highlight_qualification.py).
Packages and notices remain externally provisioned local development tools;
no upstream JavaScript, Wasm, package or Node runtime is vendored, added to the
Python environment or distributed in the syntax extension or a HoldFast/VerifiedOS
image. The harness records the exact selected Node executable and refuses
changed runtime bytes before report publication. This use grants no additional
runtime or generated-parser distribution closure.

<a id="development-tools-contained-by-use"></a>

## Development parser generator

HoldFast runs Menhir 20260209's code backend in isolated native build directories.
It links no Menhir runtime into the development parser. The
[release archive](https://opam.ocaml.org/packages/menhir/menhir.20260209/)
contains a root `LICENSE` with SHA-256
`9c97527b92b577647880abd2a5eaf5bf0f3b3df1bd09d9f93fc4e103eb1d30d5`.
The generator is GPL-2.0-only. `MenhirLib`, `MenhirSdk`, `MenhirCST`, and
`MenhirGLR` are LGPL-2.0-only WITH OCaml-LGPL-linking-exception. The separate
Rocq support library is LGPL-3.0-or-later. GPL v2 section 0 makes coverage of
generator output depend on whether the output is based on the generator.
Distributing generated source, binaries or the compiler bootstrap requires
qualification of their terms. [Parser qualification](docs/tooling/parser.md#promotion-and-retirement)

### HoldFast parser support library

The [checked-parser qualification](docs/tooling/parser.md#rocq-support-prerequisite)
builds `coq-menhirlib` from the authenticated Menhir 20260209 archive above.
The `coq-menhirlib/LICENSE` specifies LGPL-3.0-or-later and has SHA-256
`218c42550a9b4ff6e48bf38218908755fe156b2e5c586531c2eb8893248a102d`. The bounded `Interpreter.v`
proof-command relocation and `Validator_complete.v` abstract `IsItemsMap` proof
adaptation, the generated `HoldFastPureGrammar.v`, the compiled Rocq library, and the
extracted `holdfast-checked-parser` executable remain in isolated native build
directories with `LICENSE.generator` and `LICENSE.support` staged alongside them.
Only JSON receipts are exported; this use conveys no upstream source, library,
generator, or runtime binary into the tracked tree.

### Generated development tests

The [generated-test runner](tools/toolchain/generated_tests.py) pins Hypothesis
6.170.14 (MPL-2.0) and its dependency `sortedcontainers` 2.4.0 (Apache-2.0,
copyright 2014–2019 Grant Jenks). The Hypothesis source archive includes
`vendor/pretty.py` with Armin Ronacher's BSD notice, a public-domain leap-second
table, and the IANA root-zone table. The wheels contain a native extension
built from MPL-2.0 Rust source. The wheels lack separate notices for the
extension's Cargo dependencies. The runner installs the pinned versions in
an isolated environment and verifies installed versions, license digests and
the Hypothesis native extension digest. The repository retains HoldFast-authored
regression data. [Generated-test contract](docs/tooling/tooling-protocols.md#generated-development-tests)

The [syntax campaigns](docs/tooling/parser.md#generated-syntax-campaigns) use
the [Menhir generator above](#development-tools-contained-by-use) to generate
terminal names from HoldFast's grammar and interpret them as concrete syntax
trees. Retained fixtures contain HoldFast terminal sequences, HoldFast source and
expected observations. The runner uses the code backend and keeps Menhir
runtime libraries and generated error catalogs outside the fixtures.

## Independent editor clients

The [LSP client qualifier](tools/toolchain/lsp_clients.py) pins Neovim 0.11.0
(Apache-2.0 AND Vim) and Vim with `yegappan/lsp`. It checks exact archive,
executable, runtime and license identities for the selected platform. The
Neovim notice covers the bundled `netrw` runtime. Windows uses Vim 9.1.2141
(Vim AND ISC), and Ubuntu ARM64 uses the distribution's
`2:9.1.0016-1ubuntu7.10` packages and notices. The plugin revision is
`58eac06e81bad174cfa897614ae01adf0d31d10a` (MIT, copyright 2021
Yegappan Lakshmanan). The qualifier stages only the required files in temporary
directories. The repository distributes HoldFast's harness and fixtures.
[Neovim license](https://github.com/neovim/neovim/blob/v0.11.0/LICENSE.txt) ·
[Vim license](https://github.com/vim/vim/blob/v9.1.2141/LICENSE) ·
[Plugin license](https://github.com/yegappan/lsp/blob/58eac06e81bad174cfa897614ae01adf0d31d10a/LICENSE)

The pure local rename application qualifier also runs GNU Emacs 30.2 with its
built-in Eglot client, version 1.17.30, as an external batch editor. The
selected Ubuntu 26.04 ARM64 `emacs-nox`, `emacs-bin-common` and `emacs-common`
packages have version `1:30.2+1-2ubuntu1`. The installed package notice
identifies the upstream `emacs-30.2` tag and records GPL-3.0-or-later for
the editor. Eglot's source header names the Free Software Foundation and
GPL-3.0-or-later. The [rename qualifier](tools/toolchain/lsp_rename_clients.py)
checks exact SHA-256 identities for the editor executable, the explicitly
loaded Eglot bytecode, the shipped GNU GPL version 3 text and the distribution's
copyright file. Only the test harness and HoldFast source fixture are distributed
here. [Emacs 30.2 Eglot source and license](https://github.com/emacs-mirror/emacs/blob/emacs-30.2/lisp/progmodes/eglot.el)

The [BSP interoperability qualifier](tools/toolchain/bsp_client.py) runs the
same pinned Neovim editor with bsp.nvim revision
`42f77554d1242b71174da0216e1d29705da7b9d0` as an external build client.
Its root license is Apache-2.0 (SHA-256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`).
The qualifier verifies the archive, stages the license and Lua modules in a
temporary directory and exercises the client's project loader and build requests.
The repository distributes the HoldFast harness. [Pinned client and license](https://github.com/616b2f/bsp.nvim/blob/42f77554d1242b71174da0216e1d29705da7b9d0/LICENSE)

[CoqEAL and Trocq](docs/assurance/verification-strategy.md#existing-tooling-and-implementation-owners)
and QCheck are unselected candidates. A concrete consumer must qualify the
selected release and dependency licenses before incorporation. The [Plinth/Plutus paper](docs/assurance/verification-strategy.md#compilation-and-executable-models)
is a compiler-architecture reference only. No software source is taken from its
artifact, and the paper's publication licence supplies no software grant.
