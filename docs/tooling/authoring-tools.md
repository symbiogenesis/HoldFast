# HoldFast formatting, documentation and lints

The [pure compiler](pure-prototype.md) and [mathematical compiler](elaboration-prototype.md)
format source and report advisory lints after checking the whole file. The
[surface grammar](../language/surface-grammar.md) defines valid syntax.

## Common style

- Use four spaces per indentation level, LF newlines and one terminal newline.
  Opening and closing block braces occupy their own lines; `else` starts a new
  line. Separate top-level declarations with one blank line and keep attached
  documentation directly above its declaration.
- Use one statement per line, one space around binary operators and after commas,
  no space before a call's opening parenthesis, and a space after control keywords.
  Grouping parentheses have no internal padding. Preserve the authored choice
  between a return block and an expression body.
- Public functions, constants and user-defined types use PascalCase; parameters
  and local bindings use camelCase. The formatter never renames symbols.
  Primitive spellings, lifetime identities, grade names and foreign names retain
  their defining contracts; naming is a suppressible lint, not parsing authority.
- Declaration contracts occupy separate indented lines before the body. Long
  signatures and calls may wrap at argument boundaries with one extra indentation
  level; width is guidance, not a source acceptance limit. Keep ownership, loan,
  effect and proof annotations visible and in their authored order.
- Preserve token spellings, literal representations, comments and documentation
  contents. Do not sort imports, declarations or arguments, insert conversions,
  change parentheses or synthesize proof, resource or disposal operations.

Formatting preserves the authored spelling defined by the
[surface grammar](../language/surface-grammar.md). Editor suggestions and lints
follow the selected compiler's supported subset.

```text
module Example;

/// Computes the configured capacity.
public const Nat Capacity = 1_024;

/// Scales a count by the configured capacity.
public Nat Scale(Nat count)
{
    return count * Capacity;
}
```

## Numeric separators

The [lexical rules](../language/surface-grammar.md) define valid digit separators,
bases and suffixes. Formatters preserve literal spelling and compiler syntax
carries original byte spans. The compiler removes separators when interpreting
the value and counts digits against the literal limit.

## Documentation comments

### Checked examples in Markdown

Use a `holdfast-check` fence for a complete pure module intended to check.
Use `holdfast-reject syntax`, `holdfast-reject name` or `holdfast-reject type`
for a complete refusal example. The repository gate checks the marked source
through the [pure compiler](pure-prototype.md#source-fragment) and reports the
document location when it produces a different verdict. Reserve ordinary
fences for fragments and illustrative syntax. Keep any minimized generated
failure as a replayable regression in the owning tool's tests.

Consecutive `///` lines directly preceding a declaration form its documentation.
Strip the three slashes and at most one following space for presentation; retain
original UTF-8 text and source positions. A blank line, ordinary comment or
intervening source token breaks attachment. Orphan documentation remains a
comment. Formatting must preserve attachment and every comment's content.

The pure compiler attaches documentation to resolved public function and
constant declarations. Hover presents it as bounded plain text at the
declaration and its references. XML-looking text stays literal. Documentation
comments carry no semantic or proof authority.
[LSP projection](lsp-prototype.md#pure-navigation-increment)

## Compiler commands and publication

The [new-package authoring policy](../../PLAN.md#q25el) calls for a single
canonical formatter in the default release checks, with a repair command
alongside a layout finding. Builds check without writing authored source.
Editors may use the same formatter on save according to their edit policy.

| Command or mode | Source policy |
| --- | --- |
| `holdfast check SOURCE` and `holdfast emit SOURCE` | Read an immutable snapshot, run required checks and advisory lints, and preserve source bytes. Emission may publish its explicitly requested output only after successful checking. |
| `holdfast fmt SOURCE` | Explicitly request canonical source formatting. |
| `holdfast fmt SOURCE --check`, `--format check` on check/emission | Report formatting differences without writing source; differences fail the formatting check. |
| `--format off` on check/emission | Explicitly select the ordinary source-preserving default. |
| `--format write` on check/emission | Explicitly opt into formatting this invocation; this mode is never inherited as a hidden build or dependency setting. |
| `holdfast lint SOURCE` | Report the supported lint set without rewriting. |
| Editor formatting | Offer layout for a complete supported syntax tree, including buffers with semantic errors. The editor applies the proposed edit. |

`--no-lint` disables optional lints, never parser, type, constant-evaluation or
proof obligations. A style difference alone does not reject ordinary check or
emission; CI can select the explicit formatting-check mode. Read-only source
files remain usable by source-preserving commands when their requested output
locations are writable. Unsaved editor snapshots are checked at their own identity
and never published into the source file by the compiler.

For a checked formatting write, validate the complete source, reparse and
recheck the formatted candidate, establish token/comment preservation and
idempotence, and publish atomically only to the same unchanged regular source
file. Refuse symbolic links and changed inputs rather than overwriting another
file or another editor's work. Failed syntax/type checks, denied lints or invalid
output destinations leave source and generated output intact. Diagnostics and
emitted source hashes bind the exact snapshot used for compilation. Only an
explicit write mode recomputes semantic facts and emission from formatted bytes.
An I/O failure after that source publication may leave a formatted source but
must not claim successful output publication. The library checker and language
server never rewrite files.

## Lint policy

Lints have stable HoldFast IDs, locations and explicit messages. Default advisory
warnings cover member/binding naming, missing public documentation and redundant
Boolean-literal comparisons. Only compiler-supported syntax or resolved facts
justify a finding; no heuristic borrow, effect, termination or proof verdict is
invented. Emit no semantic/style finding for a source that failed complete checking.
Lints never rewrite code automatically.

The compiler reports these advisory lint IDs.

| ID | Advisory finding |
| --- | --- |
| `HOLDFAST100` | A public member name does not use a capital initial and ASCII alphanumeric words |
| `HOLDFAST101` | A parameter or local name does not use a lower-case initial and ASCII alphanumeric words; `_` is exempt |
| `HOLDFAST102` | A public function or constant has no attached documentation |
| `HOLDFAST103` | An equality comparison has a Boolean literal operand |
| `HOLDFAST105` | A generic type parameter name does not use a capital initial and ASCII alphanumeric words |
| `HOLDFAST107` | An unparenthesized bitwise expression is an operand of a comparison in checked mathematical source |
| `HOLDFAST108` | An otherwise legal binding pattern differs only in its initial capitalization from a constructor of the scrutinee type. A confusable whole match pattern is a [type error](../language/reference.md#lexical-structure). |

The mathematical CLI and native playground report `HOLDFAST107` for accepted
expressions such as `flags & mask == 0u8`. Write `(flags & mask) == 0u8` to
show the existing grouping explicitly. The warning locates the bitwise
operator and leaves the source unchanged.

Use `python tools/run.py holdfast-parser lint-preview SOURCE --line LINE --column COLUMN`
with the one-based warning coordinates to preview a pair of parentheses around
that operand. The JSON gives the half-open UTF-8 byte span, replacement text
and original and candidate digests. Every original byte stays in order,
including comments within a multiline operand. An already grouped operand
produces no warning or edit.

The mathematical parser and elaborator check both snapshots. The full syntax
trees must agree after adding the selected group and dropping locations.
The generated Gallina must agree byte for byte apart from the source digest.
The [preview validator](../../tools/toolchain/mathematical_preview.py) rechecks the
retained edit against the current source, compiler dependencies, parser bytecode
and the OCaml interpreter selected by its executable header.
The command reads the source again before printing the preview.

<a id="compiler-verified-assist-dont-coerce-tooling"></a>

### Authoring diagnostics and suggestions

Syntax errors can identify an invalid nullary constructor call or explain
how `?` propagates an error. The formatting checker can suggest an explicit
`ref` at the target of `Format.Write`. The generic authoring helpers also
construct suggestions from supplied loan modes, effect sets and numeric types.
Check a suggestion in the source context before relying on it.
[Authoring helpers](../../tools/toolchain/authoring.py)

The mathematical compiler reports both the conflicting read and where the
exclusive loan starts. For a first formatting hole that reads the built-in
`Written(builder)` count directly with a fixed-width hexadecimal format,
it can show an expression-local snapshot.
For example, write `(let count = Written(builder) in Format.Write(ref builder, $"{count:x4}"))`
to evaluate the count before `Format.Write` borrows the builder.

Repeatable `--allow ID` suppresses optional findings; `--deny ID` makes them
errors. The same ID cannot be both allowed and denied. Unknown IDs are command
errors. Defaults and rule identities are compiler-versioned; disabling an optional
lint cannot waive a language error. Findings go to stderr, keeping emitted Gallina
on stdout usable. A denied finding prevents any requested formatting and output writes.
If bounded compiler inspection cannot supply complete lint facts, normal advisory
compilation reports lints unavailable and continues. Explicit `holdfast lint` and a
command with denied lints require complete findings and refuse without writes.

## Formatting and linting mathematical source

Run `python tools/run.py holdfast-parser fmt FILE --check` to check a standalone
mathematical module's layout. A style difference yields a failing exit code.
`holdfast-parser fmt FILE` writes the checked layout. Ordinary `holdfast-parser elaborate FILE`
reads the authored bytes. Its explicit `--format check` and `--format write` modes
check the requested layout before emitting Gallina. A denied elaboration lint or
invalid program preserves both source and existing output. Emission after a
formatting write identifies the formatted source. `holdfast-parser fmt FILE
--syntax-only` applies layout to a complete mathematical syntax tree, including
one with an unresolved name, type error or broken proof. Add `--check` for a
read-only style verdict. This mode gives no elaboration or proof verdict.

The formatter works from Menhir's complete original token ranges. It preserves
literal spellings, nested block comments, line comments and the groups of
`///` comments attached to declarations. Raw and interpolated string tokens
retain their contents. It compares the complete location-independent syntax and
ordered spellings, and checks that a second
formatting pass yields identical bytes. Both compilers use the same source
identity checks and atomic file replacement. [Formatter](../../tools/toolchain/mathematical_authoring.py)

`holdfast-parser lint FILE` reports the mathematical expression and pattern rules
alongside public member naming, local and parameter naming, and missing
documentation on public functions, definitions and constants. Use `--allow ID`
to suppress a rule or `--deny ID` to fail on its findings. The locations identify
the original source. The [bitwise grouping preview](#lint-policy) consumes the
reported operator coordinates.

## Checked Boolean comparison previews

`python tools/run.py holdfast lint-preview SOURCE --line LINE --column COLUMN`
prints one explicit `HOLDFAST103` edit as JSON. Coordinates are the one-based
compiler location of the first `=` in `==`, as reported by the lint. The command
preserves the source file and its modification time. It emits no preview if the
source changes during checking.

The bounded pure compiler's complete syntax and concrete-source snapshot select
the comparison and its original byte spans. Comparing `value == true` or
`true == value` proposes `(value)`; comparing with `false` proposes `!(value)`.
Grouping around a literal is supported. Parentheses retain precedence and the
operand occurs exactly once. One request changes one comparison; it preserves
every byte outside that span. Comparisons containing comments refuse the edit.
Naming, documentation and other lint findings remain independent.

Both original and candidate must pass the existing parser and pure checker.
The checker compares their complete syntax modulo grouping and the two Boolean
equality identities, retaining calls, arguments, bindings and control flow.
The schema-2 preview binds the original inspection snapshot, exact source,
producer/configuration/target, replacement span and candidate SHA-256. The
`authoring_preview.validate` library operation rechecks all fields against the
current source and producer before returning candidate bytes. Unknown fields,
changed candidates, stale bindings and malformed coordinates refuse. This is a
development preview; it supplies no checked source or artifact correspondence.

Independent expected edits and exhaustive two-variable truth tables cover both
literal sides, negation, nested comparisons, precedence, Unicode and CRLF.
Refusal controls cover comments, invalid source, nonliteral comparisons, changed
source/producer and tampered fields; CLI controls verify source preservation and
concurrent-edit refusal.

In the pure language server, place the caret on either character of `==`, or
select a range intersecting exactly one equality operator, and request the
**Simplify Boolean comparison (HOLDFAST103)** refactoring. The editor must support
literal `refactor.rewrite` actions and versioned `documentChanges`. The server
checks the current unsaved text in a bounded worker and returns a single edit
for that document version. The editor chooses whether to apply it. Comments,
ambiguous selections and excluded action kinds yield no edit. An invalidated
generation or a failed worker prevents publication.

## Generic type parameter naming

The [mathematical playground](playground.md#dependent-mathematics-increment)
and CLI expose `HOLDFAST105` as an advisory naming lint. Generic types
use PascalCase: `T`, `TValue` and `Element` qualify. Prefer descriptive names when
they clarify the role; a `T` prefix is useful but is not mandatory. This follows
the capitalization in [C# type-parameter guidance](https://learn.microsoft.com/en-us/dotnet/standard/design-guidelines/names-of-classes-structs-and-interfaces#names-of-generic-type-parameters),
while retaining [Rust's warning and deny distinction](https://doc.rust-lang.org/rustc/lints/levels.html).
In `Copy<T, ghost Nat n>`, `T` is a type parameter and `n` is a natural-number
value index. Keep that value camelCase; angle brackets do not make it a type.

Inspect compiler-validated schema-2 generic binders by their declared role,
including nested callable telescopes, after complete semantic checking succeeds.
Use exact original identifier coordinates, preserve source and Gallina, and emit
no naming findings for invalid or incomplete source. The naming rule is advisory by default.

`holdfast-parser elaborate SOURCE` reports `HOLDFAST105` warnings by default;
`--allow HOLDFAST105` suppresses the rule and `--deny HOLDFAST105` makes it an error
before stdout emission or atomic output publication. Conflicting options refuse
before compilation.
The mathematical playground displays successful compilation's bounded findings
as warning markers and Problems entries; pure responses and mathematical
evaluation responses retain their existing shapes. Invalid, stale, oversized or
mislocated worker findings refuse the response rather than claiming clean output.

<a id="pure-formatting-and-lint-disposition"></a>

## Qualification

The formatter checks a fingerprint of ordered tokens and comments, documentation
attachment, location-independent syntax and idempotence. The
[formatting fixtures](../../tools/tests/test_holdfast_format.py) independently specify
canonical bytes. The [lint fixtures](../../tools/tests/test_holdfast_lint.py) check
findings, original positions and refusal when inspection is unavailable.

The [documentation fixtures](../../tools/tests/test_holdfast_documentation.py) check
direct attachment, orphan and broken attachment cases, Unicode and mixed
newlines, bounded plain text, declaration/use hover agreement, forged facts and
invalidation after unsaved edits over stdio. They compare translation and
attachment before and after formatting. An oversized orphan is ordinary trivia.

The [CLI fixtures](../../tools/tests/test_holdfast_authoring_cli.py) check immutable
defaults, read-only source, exact snapshot provenance, explicit formatting, lint
policy and publication failures. The
[editor fixtures](../../tools/tests/test_holdfast_lsp_editor.py) check edit ranges,
worker refusal and recovery and stdio. Independent client qualification follows
the [LSP contract](lsp-prototype.md#acceptance-and-remaining-qualification).

The [mathematical authoring fixtures](../../tools/tests/test_holdfast_mathematical_authoring.py)
compare independently specified canonical bytes, preserve attached and orphan
Unicode documentation, reject detached token ranges and stale writes, and
replay the original and formatted bitmask lemma in Rocq.
