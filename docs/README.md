# HoldFast documentation

## Language

| Document | Subject |
| --- | --- |
| [language/reference.md](language/reference.md) | Language syntax, semantics, and tool support |
| [language/first-release.md](language/first-release.md) | First-release boundary, primitive semantics, module/package rules, ownership libraries, and first-slice qualification |
| [language/core-design.md](language/core-design.md) | Core design, explicit loan and mutation rules, refinement/domain tier, and proof obligations |
| [language/surface-grammar.md](language/surface-grammar.md) | Concrete grammar, precedence, and layout |
| [language/loan-analysis.md](language/loan-analysis.md) | Path-sensitive loan-end inference over explicit flow facts |
| [language/language-landscape.md](language/language-landscape.md) | Language landscape behind HoldFast's handler, async, and surface decisions |

## Toolchain and IDE

| Document | Subject |
| --- | --- |
| [tooling/pure-prototype.md](tooling/pure-prototype.md) | Pure checking and Gallina emission |
| [tooling/parser.md](tooling/parser.md) | Menhir parsing, checked parser, and syntax campaigns |
| [tooling/elaboration-prototype.md](tooling/elaboration-prototype.md) | Generic dependent mathematics, first-class proofs, and native Rocq kernel replay |
| [tooling/packet-walkthrough.md](tooling/packet-walkthrough.md) | Run short, corrupt and valid packets through the validator and inspect its writes and returned view |
| [tooling/authoring-tools.md](tooling/authoring-tools.md) | Formatting, lints, documentation, and checked edit previews |
| [tooling/lsp-prototype.md](tooling/lsp-prototype.md) | Language Server Protocol lifecycle, diagnostics, navigation, inlay hints, formatting, and semantic tokens |
| [tooling/highlighting.md](tooling/highlighting.md) | Syntax-only editor assets and independent consumers |
| [tooling/playground.md](tooling/playground.md) | Browser playground architecture, local loopback transport, and GitHub Pages in-browser runtime |
| [index.html](index.html) | Interactive language tour and browser playground |
| [tooling/tooling-protocols.md](tooling/tooling-protocols.md) | Compiler inspection API, LSP, Tree-sitter/TextMate, SARIF, SCIP, BSP, remarks/traces, DWARF, and DAP |

## Assurance

| Document | Subject |
| --- | --- |
| [assurance/verification-strategy.md](assurance/verification-strategy.md) | Proof boundaries, language design constraints, and research |
| [assurance/compiler-route-contract.md](assurance/compiler-route-contract.md) | Retained compiler route and source-to-artifact correspondence contract |
| [assurance/workflow-contract.md](assurance/workflow-contract.md) | Release adoption and workflow comparison criteria |
| [assurance/completion-log.md](assurance/completion-log.md) | Landing evidence for completed `Q25` items |

## Extensions

The [extension index](extensions/README.md) links the designs for work outside
the first-release boundary.
