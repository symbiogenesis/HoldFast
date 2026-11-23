# Pure HoldFast translation prototype

The pure compiler translates explicit `Nat` and `bool` functions and
constants to Gallina. The [checked parser](parser.md#checked-parser-boundary)
produces syntax for separate resolution, typing, evaluation and emission.
Accepted expressions are interpreted by their generated Gallina terms.
`Nat` and `bool` denote mathematical values. Kernel replay, source
correspondence and machine-level evidence have separate acceptance checks.
The [mathematical elaborator](elaboration-prototype.md) covers a wider subset.

## Source fragment

This subset follows the [proposed surface](../assurance/verification-strategy.md#an-ideal-surface):
return types precede operation names, parameter types precede bindings, immutable
locals use `let` with an optional type, required-static values use typed `const`, and exits use `return`
or an expression body. Contracts, grades,
effects, loans and machine representations are unsupported and diagnosed,
never ignored.

The prototype accepts UTF-8 source with ASCII identifiers and `//` line comments.
Identifiers match `[A-Za-z_][A-Za-z0-9_]*`, excluding grammar and reserved extension
keywords; the latter produce unsupported-feature diagnostics. Decimal
literals match `[0-9](?:_?[0-9])*`; underscores separate digits, while leading
zeros are permitted. Separators and leading zeros normalize on emission; their
authored spelling and source locations remain intact in syntax. The [surface grammar](../language/surface-grammar.md) defines the wider numeric syntax.
Every file contains one named module and at least one function or constant.
Declarations are resolved in source order. Every parameter and return type is
explicit. A function can call only earlier functions; recursion and forward calls
are refused. Local bindings are immutable.

```text
module Example;
public const Nat Twice(Nat x) => x + x;
public const Nat Limit = Twice(x: 8);
public Nat Scale(const Nat factor, Nat value) {
  const Nat multiplier = Twice(factor);
  return multiplier * value;
}
public Nat Runtime(Nat value) => Scale(factor: Limit, value: value);
public Nat Select(bool flag, Nat x) {
  const Nat fallback = Twice(x: 0);
  let result = Twice(x: x);
  if (flag) { return result; } else { return fallback; }
}
```

The accepted grammar is:

```text
file      := 'module' name ';' declaration+
declaration:= function | 'public' constant
function  := 'public' 'const'? type name '(' parameters? ')' body
body      := block | '=>' expression ';'
parameters:= parameter (',' parameter)* ','?
parameter := 'const'? type name
type      := 'Nat' | 'bool'
block     := '{' binding* exit '}'
binding   := 'let' type? name '=' expression ';' | constant
constant  := 'const' type name '=' expression ';'
exit      := 'return' expression ';'
           | 'if' '(' expression ')' block 'else' block
expression:= disjunction
disjunction:= conjunction ('||' conjunction)*
conjunction:= comparison ('&&' comparison)*
comparison:= sum (('==' | '!=' | '<' | '<=' | '>' | '>=') sum)?
sum       := product (('+' | '-') product)*
product   := unary (('*' | '/' | '%') unary)*
unary     := '!' unary | atom
atom      := decimal | 'true' | 'false' | name
           | name '(' arguments? ')' | '(' expression ')'
arguments := argument (',' argument)* ','?
argument  := (name ':')? expression
```

Arithmetic and ordering take naturals; equality and inequality take two operands
of the same type. Negation, conjunction and disjunction take booleans.
A condition is Boolean and every reachable branch returns the declared
function result type. An expression body checks exactly like a single return;
its expression is evaluated once. Optional trailing commas apply to nonempty
parameter and argument lists, never to grouping. Statements after a terminal
return or conditional are refused, and a block without a terminal result is a syntax error. Calls have the
declared arity and argument types. A positional prefix may be followed by a
labeled suffix; each label must name the next declared parameter. Reordered,
duplicate or unknown labels, omitted arguments and positional arguments after a
label are refused. Labels preserve once-only left-to-right evaluation and do
not change the emitted application. Local annotations must match the initializer's
`Nat` or `bool` type exactly; unannotated locals infer it. Bare `type name = expression;`
locals are refused as syntax, directing authors to explicit `let`.
Duplicate functions, parameters, local bindings in an active
scope (including active parameters) and unbound values are errors. Function and
value namespaces are separate. Equality returns `bool`. Natural arithmetic,
equality and comparison map to `Corelib.Init.Nat.add`, `.sub`, `.mul`, `.div`, `.modulo`, `.eqb`,
`.ltb` and `.leb`.
Boolean equality maps to pure nested conditionals returning the Boolean
constructors. Types and constructors come from `Corelib.Init.Datatypes`.
Constants follow the [required-static contract](../language/surface-grammar.md#required-static-constants):
their typed initializers evaluate from earlier constants and pure calls with
static arguments, under finite work and numeric bounds. The supported constant
types are `Nat` and `bool`. Unmarked runtime parameters and
ordinary outer locals are refused before evaluation, including ignored or dead
dependencies. Constants denote evaluated values and cannot be reassigned or
called. Compiler-recorded constant symbols support the existing editor services.
An ordinary local inside a pure function evaluated with static arguments belongs
to that evaluation; it is not an outer runtime dependency. Constants with machine
types such as `usize` require the wider selected-target interpretation and are
outside this pure prototype.

The function modifier records constant-evaluation support without restricting
runtime calls. A static parameter is checked symbolically in its definition and
requires a static argument at every call. Instantiation substitutes that argument
and computes the required local constants, leaving ordinary data arguments in
their original order. Forwarding a static parameter preserves its availability;
neither a ghost binder nor a runtime local acquires that availability implicitly.
Logical template definitions may retain symbolic static expressions; this host
prototype establishes no target erasure or source-correspondence theorem.

Every user name is mapped to a generated identifier so Gallina keywords and
library names cannot capture source references. There is no raw Gallina escape.

Whole-source size, block/binding nesting, expression nesting and decimal-literal length have explicit
implementation limits, reported as limit diagnostics rather than acceptance.
These are host parser limits, not target resource bounds or integer widths.

## Extended pure expressions

The [pure grammar](#source-fragment) defines precedence. Comparisons require
parentheses to nest. The pure types support binary natural subtraction and
Boolean negation.

`!`, `&&`, `||`, `!=`, `<`, `>`, `>=` and binary
`-`, using the existing wider surface's spellings and precedence. From weakest
to strongest, precedence is `||`, `&&`, a single comparison (`==`, `!=`, `<`,
`<=`, `>`, `>=`), left-associative `+`/`-`, left-associative `*`, prefix `!`,
then atoms/calls/grouping. Comparisons do not chain; parentheses are required.
Repeated negation is permitted within the existing expression bounds. Unary
minus and machine integer types remain outside this increment. Division and
remainder have their own increment below.

`!`, `&&` and `||` require Boolean operands. Equality and inequality require
two operands of the same supported type; ordering and subtraction require
naturals. Subtraction saturates at zero: `2 - 5` is `0`. Emission uses existing
`Corelib.Init.Nat.sub`, `.ltb` and `.leb`, Boolean equality's once-only bindings,
and Boolean conditionals for negation and short-circuit logic. Reversed ordering
must preserve left-to-right once-only operand evaluation through fresh bindings.
All generated binders remain disjoint from mapped source names.

Both logical operands undergo name/type and required-static dependency checks,
including dead operands. Evaluation and emitted conditionals evaluate the left
operand once and evaluate the right only when needed. Thus
`false && (huge * huge == 0)` can avoid a static arithmetic limit, while
`false && runtimeFlag` still cannot initialize a required-static constant.
The evaluator applies its work, depth, output and numeric limits.

The [expression fixtures](../../tools/tests/test_holdfast_expressions.py) check
expected values, emitted terms, refusal cases and original-source spans.
`holdfast-parser elaborate-qualify` replays independently expected constant
and runtime equalities with the kernel and assumption auditor.
[Playground examples](playground.md#extended-expression-examples)

## Boolean web output

Export one function from a checked pure module as a default ECMAScript module
function. For example, build the playground's `Changed` comparison, then
import the resulting file in an ES module. [Example source](../../examples/expressions.hf)

```console
python tools/run.py holdfast-parser emit-web examples/expressions.hf Changed --output changed.mjs
```

```js
import changed from "./changed.mjs";
changed(false, true); // true
```

The selected public function takes zero to eight ordinary `bool` parameters and
returns `bool` in a single expression or return statement. The expression may use
its parameters, Boolean literals, grouping, `!`, `&&`, `||`, `==` and `!=`.
Every declaration in the file must pass the pure checker. Only the selected
function is exported. Calls with the wrong arity or a nonprimitive Boolean
argument return `undefined`. Parameters receive positional JavaScript names.
Equality uses strict Boolean comparison. [ECMA-262, 16th edition](https://262.ecma-international.org/16.0/)

For each export the [backend](../../tools/toolchain/web_output.py) runs the
exact generated bytes in the pinned Node.js executable on Ubuntu ARM64 or WSL.
Each Boolean tuple, in order from all-false to all-true, produces one primitive
result. For every tuple, `rocq c` checks an equality between the existing pure
Gallina interpretation and that observed result by conversion. `rocqchk`
independently checks the compiled library. The command then rereads the source
and atomically publishes the executed bytes. Its JSON result identifies the
source, exported function, JavaScript, Gallina, engine and Rocq switch and
includes the truth table. The correspondence covers this file and function under
the pure parser and Gallina interpretation.

The input limit is 65,536 bytes. The entry expression permits at most 128
syntax nodes within the pure compiler's depth limits. Its execution visits
at most those 128 nodes, with at most eight parameter type tests and one arity
check per call. The emitted module is at most 16,384 bytes. Qualification runs
at most 256 in-domain tuples, tests invalid callers, and allows ten seconds
for Node with a 32 MiB old-space limit and thirty seconds for each kernel tool.
The bounds describe this generated expression and qualification process.
Browser engine memory allocation and execution time depend on the host.

Run `python tools/run.py holdfast-parser qualify-web` to exercise four independent
truth tables and require the kernel to reject two changed JavaScript expressions.
[Runtime pin](../../THIRD-PARTY.md#boolean-web-execution-engine) ·
[Qualified client](../../tools/toolchain/web_output_check.py)

## Natural division and remainder

Division `/` and remainder `%` take two `Nat` operands and return `Nat`.
They share multiplication's precedence and associate left to right.
For example, `20 / 3 * 2` is `12`, `20 % 6 * 2` is `4` and
`20 / (3 * 2)` is `3`.

These operations denote `Corelib.Init.Nat.div` and `.modulo`. For a positive
divisor, division is the natural quotient and remainder is the nonnegative
remainder. The operations are total: `n / 0` is `0`, and `n % 0` is `n`.
The static evaluator uses the same mathematical operations. Both operands
are checked and evaluated once in source order, including for a zero divisor.
[Represented arithmetic](../language/first-release.md#primitive-semantics) has
its own nonzero-divisor and representability requirements.

The [division fixtures](../../tools/tests/test_holdfast_division.py) exercise
values, rendering, operand types and static dependency checks. Native kernel
replay also checks emitted terms. [Playground examples](playground.md#division-and-remainder-examples)

## Command and publication

Run `python tools/run.py holdfast check SOURCE` to check a file, or
`python tools/run.py holdfast emit SOURCE` to print its Gallina. Use `--output FILE`
to publish Gallina atomically after successful checking. The output must
have an existing parent and must not alias the source. Diagnostics identify
the source position and the kind of failure. Formatting and lint behavior
follow the [authoring command policy](authoring-tools.md#compiler-commands-and-publication).

Deterministic output uses fully qualified CIC operations and SHA-256 provenance
for the exact authored bytes, or post-format bytes after an explicit formatting write,
without a correspondence theorem. Emit definitions only:
no axioms, admissions, proof scripts or machine-code escape.

## Acceptance

Behavioral fixtures check expected translations, types, lexical scope, syntax
and resource refusals, exact source provenance and output publication.
The [parser comparison](parser.md#pure-parser-comparison) exercises both syntax
routes. [Kernel replay](elaboration-prototype.md#commands-and-acceptance) checks
generated terms and their assumptions. [Unified-source acceptance](../extensions/unified-source-contract.md)
governs production correspondence.

## Try the prototype

From the repository root on Windows (use `python3` on Linux):

```console
python tools/run.py holdfast check examples/pure.hf
python tools/run.py holdfast emit examples/pure.hf --output out/Pure.v
```

Create the output directory first, or omit `--output` to print definitions.
The [example](../../examples/pure.hf) defines a cube and Boolean
selection: intended `Choose(true, 1)` is true, `Choose(true, 2)` false. Output is
module `HoldFast_Oracle` with `f_Cube`/`f_Choose`. The
[expression example](../../examples/expressions.hf) adds Boolean
logic, comparisons and saturating natural subtraction. The playground console
evaluates closed expressions through the bounded static evaluator; kernel
acceptance requires the separate replay.

## Bounded compiler traces

The compiler records bounded development traces under the
[performance trace contract](tooling-protocols.md#compiler-decisions-and-performance-traces).

For the packet validator, `python tools/run.py holdfast-parser first-slice --trace`
runs the [native qualification](../language/first-release.md#first-slice-qualification)
and records the path of a Chrome Trace Event file in the receipt's
`compiler_trace` field. The host track covers surface parsing, joint resolution
and elaboration, Gallina generation, proof compilation, assumption auditing,
kernel checking and lowering to C. Three child tracks measure the time the
parent spends waiting on the launched proof commands. Their event arguments
record the actual process IDs. The packet interval ends at C lowering. The
remaining qualification controls and simulator runs execute afterwards.
Both parent and child proof spans must fit the independent command-step
duration, allowing for rounding to recording-relative microseconds.

The twelve-event inventory has a fixed size. A clock fault, cancellation,
truncation or missing phase prevents complete-trace validation. Rechecking the
first-slice receipt verifies the source, compiler outputs, parser and proof
environment, then checks the trace digest, order, nesting and child identities.
The packet runtime binding covers the Linux Python compiler, bytecode parser
and its actual interpreter, opam, the selected Rocq dispatch and proof workers,
native plugins and their transitive ELF libraries. The selected system loader
resolves dependencies in the host and proof-switch environments. The recording
and recheck require regular, readable inputs and refuse unresolved libraries and
loader injection. Configured Rocq load roots and proof inputs have separate
file-by-file bindings in the same receipt.
These measurements describe compiler execution.

Run `python tools/run.py holdfast trace-qualify-packet-viewer --trace-processor PATH --output out/packet-viewer.json`
with a provisioned, pinned Perfetto v58.2 reader. It imports a deterministic
packet trace and checks eleven independently specified spans in nanoseconds,
their depths, logical threads and processes, the source byte counter and the
three proof-command process IDs. Each child has its own process track and
falls inside the wall-time interval of its host proof phase.
`python tools/run.py holdfast trace-packet-viewer-validate out/packet-viewer.json --trace-processor PATH`
rechecks the exact fixture, reader, harness, SQL and retained CSV observations.

Create the destination directory, then run:

```console
python tools/run.py holdfast trace examples/pure.hf --output out/pure-trace.json
python tools/run.py holdfast trace-validate out/pure-trace.json --source examples/pure.hf
python tools/run.py holdfast trace-render out/pure-trace.json --source examples/pure.hf --output out/pure-timeline.html
python tools/run.py holdfast trace-benchmark examples/pure.hf --output out/pure-trace-comparison.json
python tools/run.py holdfast trace-benchmark-validate out/pure-trace-comparison.json --source examples/pure.hf
python tools/run.py holdfast trace-qualify-viewer --trace-processor /path/to/trace_processor_shell --output out/trace-viewer.json
python tools/run.py holdfast trace-viewer-validate out/trace-viewer.json --trace-processor /path/to/trace_processor_shell
```

The read-only trace command records `compile`, nested `parse` and
`elaborate-and-emit` phases from the existing pure producer. Resolution and Gallina
emission share one elaborator and remain one measured phase. The synchronous host
worker includes time waiting for the checked parser process; it does not report
that process's internal phases. Inside `parse`, the `checked-parse` span measures
the checked parser invocation and its existing build/runtime checks; the
`syntax-decode` span measures Python validation and construction of the returned
pure AST. Their ordered, nonoverlapping nesting within `parse` is mandatory.
Source and Gallina byte counters use Chrome
Trace Event `C` records, and completed phases use `X` records with recording-relative
integer microseconds derived from `perf_counter_ns`. The fixed worker identities
are `pid: 1`, `tid: 1`; they describe this recording, not operating-system IDs.
[Perfetto documents these event formats](https://perfetto.dev/docs/getting-started/other-formats)
as an input to its viewer. The optional qualification command checks a pinned
independent importer as described below.

Each top-level constant or function also has a nested `declaration` span within
`elaborate-and-emit`, in source order. Its standard event `args` retain the declared
name, declaration kind and one-based normalized Unicode code-point line/column.
This attributes the existing combined elaboration/emission work to declarations;
constant specialization remains inside its calling declaration. The manifest
counts attempted declaration spans, including dropped records. Validation checks
retained name sites against exact source bytes, ordered nonoverlapping declaration
work within its parent phase, and the retained/dropped inventory. These source
sites identify name spellings; declaration kinds are recorded producer metadata.
The inventory counts recorder calls and supplies no independent source-coverage
or source-to-timing correspondence theorem.

The `holdfast` schema-3 manifest binds events and completeness metadata, exact source
bytes, local Python/compiler/parser input files and Python/platform versions.
The producer identity binds the Python and opam locks, command bootstrap,
Python executables, active import search paths, interpreter flags and kernel
versions. Its Python file inventories cover the standard library, installation
archives and extensions, versioned Python shared libraries, active installed
package trees including their data and startup hooks, loaded module files and
their bytecode caches, and mapped user-space images including system libraries.
Cache creation changes the identity. Each inventory is limited to 20,000 file
labels and 512 MiB of file content.

An ordinary checked parse starts the persistent worker before timing. A control
request on that worker's own batch pipe returns its Linux PID. The observer
checks its live command line against the build receipt's parser file, hashes
the bytecode executable and follows its actual file-backed mappings through the
OCaml interpreter, system loader and transitive libraries. Deleted images,
changed device/inode identities and anonymous executable mappings refuse
observation, apart from kernel-supplied clock/system-call pages. On Windows
the binding also includes the libraries of the live WSL transport process and
the guest Python environment that validates the parser build. Hashes describe
compiler processes in the observed operating systems. The kernels, WSL service,
firmware and hardware provide the measurement environment.

Identity observation lies outside the timed intervals. The validation
command refuses changed source or producer identities, malformed events, crossing
spans, invalid clocks, missing phases or counters, and incomplete recordings.
The validator requires schema 3, including the parser-stage record.
A successful complete recording measures a successful pure check only.

Recording retains at most 4,096 events; `--max-events` selects a smaller positive
limit. Phase names, counters, nesting and exported/decoded bytes have fixed bounds.
Dropped events, open spans, clock faults and refused or cancelled work prevent a
complete measurement claim. A refused source writes a diagnostic trace and returns
failure. Publication is atomic, refuses source aliases and rechecks source and
producer freshness; failed preparation preserves an existing output. Validation
also rechecks producer freshness after reading the recording. The manifest
reports measured recorder bookkeeping in nanoseconds, excluding identity hashing,
serialization and file publication. No hard elapsed-time overhead bound is claimed.

The comparative benchmark runs both plain and traced translation in alternating
pairs in the same host process, including checked-parser wait time. It defaults to
one warmup pair followed by seven measured pairs; `--warmups` accepts 0–5 and
`--samples` accepts 1–31. Every translation must emit the same module and Gallina,
and every traced run must pass complete-recording validation. Only translation
lies inside the measured intervals: recorder construction, trace export and
validation, identity hashing and report publication are excluded. Warmup intervals
are discarded, while compiler caches and operating-system scheduling remain part
of the observed conditions. The command bounds compilation count and report size;
it establishes no hard elapsed-time bound or stable overhead threshold.

The separate schema-1 comparison report retains each pair's execution order,
elapsed nanoseconds and traced bookkeeping, output identity, source and producer
bindings, and exact summaries. Totals, minima, maxima and medians summarize each
path; an even-sample median rounds down to whole nanoseconds. `elapsed_delta_ns`
is traced total minus plain total. `overhead_ppm` is that difference divided by
plain total in parts per million, rounded down; a zero plain total reports `null`.
Negative observations are retained without claiming that instrumentation improves
performance. Validation recomputes summaries and refuses stale identities,
changed samples, invalid durations, incorrect pair order and malformed reports.
Refused, cancelled or stale measurements preserve an existing report. A hash-bound
report detects changed data and supplies no authentication of the measurement or
its environment.

Both benchmark commands accept `--max-overhead-ppm N`. Supply the workload and
budget before measuring. Qualification requires at least one warmup and seven
measured pairs with a positive total plain time. It compares the exact totals,
so an overrun smaller than one part per million still fails. A failed comparison
preserves the previous output. Pass the same budget to the independent validation
invocation. The qualification workloads are [pure functions](../../examples/pure.hf)
and [expressions](../../examples/expressions.hf), each with one warmup,
seven measured pairs and a 250,000 ppm (25%) aggregate elapsed overhead budget.
The verdict applies to those recorded runs.

[Independent timeline fixtures](../../tools/tests/test_holdfast_compiler_trace.py)
recover expected order, durations, nesting and counters with a separate JSON reader
and exercise corruption, overflow, clock and refusal controls.
[Paired-measurement fixtures](../../tools/tests/test_holdfast_trace_benchmark.py) check
independently chosen timing totals, warmup exclusion, output equivalence, binding
and publication refusals.

`trace-qualify-viewer` accepts an already provisioned Perfetto `v58.2`
`trace_processor_shell`; it performs no downloads and changes no dependencies.
The selected executable must match one of the reviewed Windows AMD64, Linux
AMD64 or Linux ARM64 SHA-256 pins in the
[qualification harness](../../tools/toolchain/trace_viewer.py), then report
revision `add693d8b338ba9599dbcbc3e300b1ab8c000897`. The
[license and use record](../../THIRD-PARTY.md#independent-trace-importer) owns
provisioning links and terms. Other binaries refuse before execution.

The harness validates a deterministic Chrome trace and verifies seven negative
controls before handoff: stale source/producer, missing phases, crossing spans,
negative timestamps, dropped events and cancellation. Perfetto imports the valid
fixture and executes two fixed SQL queries. Independently chosen expected rows
require six spans with exact nanosecond timestamps/durations, parent/child
depth through both parser stages and a nested function declaration, worker
identities, plus both byte counters. The report retains the
fixture, queries, imported CSV and parsed rows, version/diagnostic transcripts,
negative-control results, executable/revision and harness identities, and a
binding over the complete report. Each reader invocation has a 30-second timeout
and bounded accepted output. Hashes detect changes and authenticate no measurement.
Reader/harness changes withdraw qualification; atomic publication preserves
existing evidence after failures or cancellation and refuses output aliases.
[Reader qualification tests](../../tools/tests/test_holdfast_trace_viewer.py) cover
wrong independent observations, disabled negative checks, unknown binaries,
timeouts, output bounds, aliases and late identity changes.

`trace-viewer-validate` rechecks a retained qualification receipt without executing
the external reader. It bounds receipt bytes and nesting, rejects duplicate
fields, and checks the exact fixture, source, producer, negative-control inventory,
queries, CSV observations and retained result rows against independently chosen
expectations. Non-successful reader outcomes, a changed release, malformed or
oversized transcripts, changed reader bytes and stale harness identities refuse.
Current identities are checked again after receipt inspection. Rehashing an
altered duration, counter, declaration kind or omitted control cannot restore
acceptance. This checks retained data consistency and freshness; it supplies no
transcript authentication or fresh reader observation.

The selected Perfetto importer and the offline browser viewer below consume
the same pure recording contract. Compiler timings describe tooling performance. Emitted-program WCET and constant-time evidence have their own
qualification requirements.

### Offline browser timelines

`trace-render` validates an exact-source, current-producer, complete schema-3
recording before publishing a self-contained HTML timeline. Open the resulting
file in a browser. Nested phase and declaration spans have keyboard-focusable
source/time tooltips, with a searchable table retaining exact microsecond values
and both byte counters. The graphic uses a fixed 1,000-pixel time axis inside a
horizontal scroll container; depth determines the row. Zero and subpixel
durations retain a minimum half-pixel hit target, while the table preserves the
actual zero or short duration. The view identifies the source, producer,
recording and viewer bytes. It includes no source text or external assets; a
content-security policy allows only its exact inline style/script hashes and
refuses network access. Default commands preserve source bytes.

HTML export accepts at most the recording's 2 MiB input bound and emits at most
4 MiB. Stale, refused, cancelled, dropped or malformed recordings refuse before
rendering. Source and recording bytes and identities, plus producer inputs, are
rechecked before atomic publication. Source/recording aliases refuse and failed
or cancelled preparation preserves an existing timeline.

Qualify actual browser rendering using an already provisioned Chromium browser
and an explicitly selected executable SHA-256:

```console
python tools/run.py holdfast trace-qualify-browser --browser /path/to/browser --browser-sha256 <sha256> --output out/trace-browser.json
```

The command installs nothing and opens only a temporary local file in a fresh
headless profile. Its 30-second invocation and accepted DOM/diagnostic output are
bounded. The browser renders the deterministic fixture with a qualification-only
probe that reads actual layout rectangles, computed colors, keyboard focusability,
tooltips, counters and a dispatched filter edit. Independently fixed expectations
require six spans at their exact time-derived positions, three nesting depths,
source details and a single matching declaration row after filtering. The receipt
binds observed geometry and behavior, exact browser bytes, viewer/harness inputs
and fixture HTML; late changes withdraw publication. The
[viewer controls](../../tools/tests/test_holdfast_trace_html.py) exercise incorrect
layout, styles, filtering and source observations, binary changes, timeouts,
oversized output, stale/incomplete recordings and atomic publication failures.

This qualifies the HoldFast offline viewer in the exact selected Chromium executable.
It supplies no Perfetto browser-UI qualification, browser installation/runtime
closure, measurement authentication or emitted-program timing verdict. The pinned
Perfetto importer retains its independent receipt and separate acceptance scope.
