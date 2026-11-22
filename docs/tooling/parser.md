# Vela development parser qualification

The Rocq-extracted checked parser serves the [pure compiler](pure-prototype.md).
The Menhir code-backend parser also accepts the
[development surface grammar](../language/surface-grammar.md) and serves the
[mathematical elaborator](elaboration-prototype.md). Both emit located JSON
syntax. Separate consumers resolve names, check types and elaborate terms.

## Bounded increment

The syntax entries consume the complete source before semantic checking.
Duplicate declarations and `true + 1` parse before semantic diagnostics.
Unsupported keywords, invalid UTF-8, incomplete input and resource exhaustion
produce located refusals. Both entries share a bounded token-only probe for
generic calls.

The authored OCaml grammar and AST types own syntax; actions construct located
syntax only. Nodes carry half-open original-source byte spans. Diagnostics use
one-based lines/columns, treating CRLF and bare CR as line endings. Keep decimal
spellings, including leading zeros, as strings without machine-integer bounds.
Comments may be UTF-8; identifiers are ASCII. Provenance hashes unnormalized bytes.

The [Sail snapshot](../../tools/opam/sail.lock) pins the Menhir generator and
OCaml compiler. Build receipts bind authored inputs, tools, arguments and
generated files. Generated parser source and binaries stay in native build
directories. [Generator terms](../../THIRD-PARTY.md#development-parser-generator)

Input is bounded by the prototype's source-byte and literal-digit limits. The
native driver also bounds delimiter nesting and raw syntax-tree depth at 256 before exposing
an AST, and reports stack exhaustion as a limit refusal. Raw syntax counts groups
and file/function/block/return wrappers; the separate AST consumer retains the
prototype's expression and block/binding limits of 64. The command wrapper
bounds process duration and reads source files with a bounded read. Refused input
publishes no AST. Success emits deterministic JSON containing the complete located
syntax tree and the exact source digest. A successful build alone is no parser
qualification verdict.

## Acceptance and commands

`python tools/run.py vela-parser build` generates and compiles the parser in the
native guest lane. `vela-parser parse SOURCE` emits its JSON syntax tree.
`vela-parser qualify` builds it and runs independent expected-tree fixtures,
whole-file positive/refusal cases, source spans, LF/CRLF/bare-CR positions,
UTF-8 comments and invalid encoding, decimal spelling, precedence and
associativity, incomplete editor input, excessive nesting and oversized input.
Qualification checks that name and type errors parse as syntax and compares
two fresh generations. Its receipts cover development syntax. Checked parsing,
lexical correctness, source correspondence and frontend acceptance have their
own obligations.

### Ordinary build cache

`vela-parser parse`, `vela-parser elaborate`, and `vela-playground` reuse a
development parser in the native worktree lane's `vela-parser/ordinary-cache`
directory. Each lookup checks the exact authored-input hashes, selected
toolchain versions and executable hashes, generation/compilation arguments,
receipt scope and directory, and all generated-output hashes. A missing,
outdated, or damaged entry is rebuilt. The receipt records only `built` syntax
tooling; a cache hit supplies no qualification or kernel verdict.

Builders serialize under a cache lock, waiting at most 120 seconds for another
builder. Construction completes before an atomic current-generation pointer
publishes it; a failed build or publication preserves the previous pointer.
Readers lease immutable generation directories through independent OS file
locks, so concurrent CLI users share a generation and a running playground
keeps its parser even when edited grammar requires a newer generation.

The cache retains its current generation and any older generation still in use.
Obsolete unused entries and interrupted candidates are removed at the next
lookup or lease release. A crashed reader releases its OS lock, allowing its
stale lease to be collected. Cleanup is confined to cache entries; explicit
`vela-parser build` and all qualification paths continue making fresh builds
outside the cache and retain their existing evidence artifacts.

## Generated syntax campaigns

`python tools/run.py vela-parser syntax-campaigns` includes parser qualification
and the [pure parser comparison](#pure-parser-comparison). It uses the locked
Menhir generator and deterministic seeds to exercise interactions among multiple
declarations, precedence, trailing commas and trivia. A bounded renderer turns
terminal sentences into source with canonical, UTF-8 comment and newline variants.
The requested sentence length guides generation. Independent caps bound tokens,
bytes, elapsed time, memory and interpreter output.

Menhir's interpreter and CST exercise the grammar. An independent oracle checks
native syntax trees and source spans, including cases the automaton accepts
and an action refuses. Seeded action and span faults exercise the oracle.
Reports bind the exact tools, grammar, seeds and rendered inputs. Reduced
failures replay without random generation. [Campaign implementation](../../tools/toolchain/syntax_campaigns.py) · [Fixture checks](../../tools/tests/test_vela_syntax_campaigns.py)

<a id="promotion-and-retirement"></a>

## Checked parser boundary

Both backends generate their pure grammar from the same Menhir source. The
checked route uses conflict-free grammar generation, replays the concrete
correctness and completeness theorems, and checks the extracted runtime's
identity before use. The theorems concern parsing a token stream. Source spans,
diagnostics, lexical correctness and checked source correspondence have separate
obligations. [Verification strategy](../assurance/verification-strategy.md)

<a id="executable-migration-preparation"></a>

### Pure parser comparison

The [checked runtime](../../tools/toolchain/parser_checked.py) serves pure
compilation, evaluation, inspection, formatting and linting through its framed
batch protocol on Linux and through WSL on Windows. The
[shared AST decoder](../../tools/toolchain/ast.py) validates each envelope's
schema, exact source digest, token spelling, child spans and resource bounds
before semantic checking.

`python tools/run.py vela-parser migration` compares the checked route with the
Menhir code-backend route. They must agree on independently categorized fixtures,
source edits, diagnostic categories and positions, resource boundaries and full
emitted Gallina bytes. Differences are recorded in `migration.json` and fail the
command. The receipt binds source, tools and generated parser bytes.

### Rocq support prerequisite

`python tools/run.py vela-parser support` authenticates the pinned Menhir
archive, builds its Rocq support library under the
[locked proof switch](../../tools/opam/rocq.lock), and generates the concrete
pure grammar with `menhir --coq --strict`. Supply `--archive FILE` to reuse an
authenticated archive. The support build applies exact-digest-guarded source
adaptations to relocate three `Proof` commands and keep an item-map parameter
abstract during kernel checking. It checks public types, universes, executable
bodies and assumptions against the reference and exercises the generator-version
guard with passing and failing clients. [Support build](../../tools/toolchain/parser_checked.py) · [Support library terms](../../THIRD-PARTY.md#vela-parser-support-library)

The build checks deterministic grammar generation and replays
`vela_file_safe`, `vela_file_complete_validator`, `vela_file_correct`,
`vela_file_complete`, `vela_file_unambiguity` and the concrete precedence,
bare-local, empty-module and zero-fuel controls. The assumption audit requires
a closed global context and recursive `rocqchk` validates the support closure.

Extraction links the checked OCaml parser with the authored AST, lexer and
driver. Runtime builds are keyed by the digest of their checked inputs, so
worktrees with identical inputs can share a receipt-verified executable.
The lexer, framing and JSON decoder remain outside the token-parser theorem.
