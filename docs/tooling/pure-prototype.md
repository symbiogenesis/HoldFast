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

```holdfast-check
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
           | 'Nat' '.' name '(' arguments? ')'
arguments := argument (',' argument)* ','?
argument  := (name ':')? expression
```

Arithmetic and ordering take naturals; equality and inequality take two operands
of the same type. Negation, conjunction and disjunction take booleans.
A condition is Boolean and every reachable branch returns the declared
function result type. An expression body checks exactly like a single return;
its expression is evaluated once. Nonempty parameter and argument lists allow
a trailing comma. A block ends with a return or returning conditional. Calls
must match the declared arity and argument types. A positional prefix may be
followed by a labeled suffix. Each label must name the next declared parameter. Reordered,
duplicate or unknown labels, omitted arguments and positional arguments after a
label are refused. Labels preserve once-only left-to-right evaluation and do
not change the emitted application. The supported qualified call,
`Nat.SaturatingSub(a, b)`, takes two positional `Nat` arguments.
Local annotations must match the initializer's
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
and computes the required local constants. The definition checks both branches
before instantiation, which computes local constants only in the reachable branch
when the condition is known. Ordinary data arguments retain their original order.
Forwarding a static parameter preserves its availability;
neither a ghost binder nor a runtime local acquires that availability implicitly.
Logical template definitions may retain symbolic static expressions; this host
prototype establishes no target erasure or source-correspondence theorem.

The return type is checked before Gallina emission. This complete example
reaches a type error at the Boolean result.

```holdfast-reject type
module ReturnType;
public Nat Count() => true;
```

Every user name is mapped to a generated identifier so Gallina keywords and
library names cannot capture source references. There is no raw Gallina escape.

Whole-source size, block/binding nesting, expression nesting and decimal-literal length have explicit
implementation limits, reported as limit diagnostics rather than acceptance.
These are host parser limits, not target resource bounds or integer widths.

## Extended pure expressions

The [pure grammar](#source-fragment) defines precedence. Comparisons require
parentheses to nest. Repeated negation is permitted within the existing
expression bounds.

`!`, `&&` and `||` require Boolean operands. Equality and inequality require
two operands of the same supported type. Ordering and subtraction require
naturals. For `a - b` the checker establishes `b <= a` using a known
operand bound or a matching fact from a branch or short-circuit condition.
The true branch of `if (used <= total)` can return `total - used`. For intentional truncation,
`Nat.SaturatingSub(2, 5)` evaluates to zero. Both forms emit
`Corelib.Init.Nat.sub`. Ordering emits `.ltb` and `.leb`, while Boolean
negation and short-circuit logic emit conditionals. Reversed ordering
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

The checker must establish a nonzero divisor. A nonzero literal suffices,
and the true branch of `if (size != 0)` can use `count / size` or
`count % size`. Accepted expressions emit `Corelib.Init.Nat.div` and
`.modulo` for the natural quotient and nonnegative remainder. The static
evaluator uses the same mathematical operations. Both operands are checked
and evaluated once in source order.

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
The [example](../../examples/pure.hf) defines a cube and a Boolean selection.
`Choose(true, 1)` evaluates to `true` and `Choose(true, 2)` to `false`. The
emitted `HoldFast_Oracle` module contains `f_Cube`, `c_Base` and `f_Choose`. The
[expression example](../../examples/expressions.hf) adds Boolean
logic, comparisons and checked natural arithmetic. The playground console
evaluates closed expressions through the bounded static evaluator; kernel
acceptance requires the separate replay.

## Bounded compiler traces

Records bounded development traces under [the performance trace contract](tooling-protocols.md#compiler-decisions-and-performance-traces).

For the packet validator, `python tools/run.py holdfast-parser first-slice --trace` runs [native qualification](../language/first-release.md#first-slice-qualification) and records a Chrome Trace Event path in `compiler_trace`: host track covers surface parse, resolution+elaboration, Gallina emission, proof compile, assumption audit, kernel check, and C lowering (three child tracks record parent wait times + PIDs on launched proof commands; interval ends at C lowering before controls/Sail; parent/child spans fit command durations within microsecond rounding). The 12-event inventory is fixed-size (clock faults, cancellations, truncations, or missing phases fail validation). Receipt rechecks verify source, outputs, parser/proof env, trace digest/order/nesting/child IDs, and transitive regular-file ELF bindings (Linux Python, bytecode parser + interpreter, opam, Rocq dispatch/workers, plugins, loader deps, Rocq load roots/proof inputs—refusing missing/unreadable files and loader injection).

`python tools/run.py holdfast trace-qualify-packet-viewer --trace-processor PATH --output out/packet-viewer.json` runs a pinned Perfetto v58.2 reader importing a deterministic packet trace and checking 11 nanosecond spans, depths, logical threads/processes, source byte counter, and 3 proof PIDs (rechecked via `holdfast trace-packet-viewer-validate out/packet-viewer.json --trace-processor PATH` against fixture, reader, harness, SQL, and CSVs).

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

`trace` records `compile`, nested `parse` (containing nonoverlapping `checked-parse` and `syntax-decode`), and `elaborate-and-emit` (containing source-ordered `declaration` spans with name, kind, and 1-based code-point line/col; constant specialization stays inside its calling declaration; dropped records counted; provides no coverage or timing-correspondence theorem). Uses Chrome Trace Event `C` byte counters and `X` microsecond records (`perf_counter_ns`), fixed `pid: 1` / `tid: 1` ([Perfetto formats](https://perfetto.dev/docs/getting-started/other-formats)). Schema-3 manifest binds source bytes, local Python/compiler/parser files, locks, interpreter/paths/flags/kernel, and loaded Python/system ELF inventories (<= 20,000 labels, <= 512 MiB; persistent worker batch-pipe PID checked live through OCaml/loader/ELF mappings—refusing deleted/changed/anonymous executable pages, plus WSL transport/guest Python on Windows). Identity hashing stays outside timed intervals; max 4,096 events (`--max-events`), atomic publication (refusing aliases; refused source writes diagnostic trace and fails; validation checks schema 3 and freshness). Bookkeeping nanoseconds exclude hashing/serialization/publication (no hard overhead claim).

`trace-benchmark` alternates plain and traced runs in one host process (default 1 warmup + 7 samples; `--warmups 0..5`, `--samples 1..31`), verifying identical Gallina and valid complete traces (measuring translation only; schema-1 report records order, elapsed ns, bookkeeping, totals/min/max/median rounded down, `elapsed_delta_ns`, `overhead_ppm` rounded down or `null`, retaining negatives; `--max-overhead-ppm N` fails on exact total overrun >= 1 ppm; qualification workloads [pure functions](../../examples/pure.hf) and [expressions](../../examples/expressions.hf) run 1 warmup + 7 samples at 250,000 ppm / 25%). [Timeline fixtures](../../tools/tests/test_holdfast_compiler_trace.py) · [Benchmark fixtures](../../tools/tests/test_holdfast_trace_benchmark.py)

`trace-qualify-viewer` verifies provisioned Perfetto `v58.2` `trace_processor_shell` against [trace_viewer.py](../../tools/toolchain/trace_viewer.py) SHA-256 pins (Windows AMD64, Linux AMD64/ARM64) and revision `add693d8b338ba9599dbcbc3e300b1ab8c000897` ([terms](../../THIRD-PARTY.md#independent-trace-importer)), validates 7 negative controls (stale source/producer, missing phases, crossing spans, negative timestamps, dropped events, cancellation), executes 2 SQL queries expecting 6 nanosecond spans, depths, worker IDs, and byte counters (30 s timeout, atomic report; [tests](../../tools/tests/test_holdfast_trace_viewer.py)). `trace-viewer-validate` rechecks retained receipt consistency/freshness without running the reader.

### Offline browser timelines

`trace-render` validates schema-3 recordings (<= 2 MiB input -> <= 4 MiB atomic HTML; refusing stale/refused/cancelled/dropped/malformed inputs and aliases) into a self-contained timeline with focusable tooltips on a 1,000 px scrolled axis (0.5 px min hit target), searchable exact-microsecond table, SHA-256 bindings, zero external assets, and strict inline-hash CSP. Qualify with a provisioned Chromium executable:

```console
python tools/run.py holdfast trace-qualify-browser --browser /path/to/browser --browser-sha256 <sha256> --output out/trace-browser.json
```

Runs headless on a temporary file (30 s timeout), checking layout rects, computed colors, keyboard focus, tooltips, counters, and filtering (6 spans, 3 depths, source details, 1 filtered row) while binding browser/viewer/harness/HTML bytes ([viewer controls](../../tools/tests/test_holdfast_trace_html.py); no Perfetto UI, browser closure, or target timing claim).
