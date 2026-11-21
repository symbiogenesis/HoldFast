# Vela browser playground

## Dependent mathematics increment

Q25ae in [the plan](../../PLAN.md#q-assessment-actions) commissions one unified
playground using the [mathematical elaborator](elaboration-prototype.md).
`python tools/run.py vela-playground` runs in the native guest lane and builds
the locked Menhir parser once before serving. Every local buffer uses the
schema-2 surface parser and mathematical elaborator. The static playground
loads its browser parser and elaborator with the page.

Compile elaborates the entire source and displays its actual Gallina. The console
checks the complete source plus exactly one closed expression, reduces it with the
existing bounded mathematical reducer, and returns only `Nat` or `bool`. Generic
inference, dependent functions, length-indexed `Vec`, finite `Fin` indices and
explicit equality proofs keep their existing semantics. Reject mismatched lengths,
out-of-range indices, false proofs, ambiguous inference and declaration injection.
No browser request may select an executable or filesystem path.

Compile and evaluate use the full playground language from the first request.
For example, a module defining only `public Nat Square(Nat x) => x * x;`
can evaluate `At(VCons(Square(7), VNil<Nat>()), FZero<0>())` to `49`.
Compile results include an `editorServices` Boolean for formatting, navigation
and other pure editor tools. Successful compilation includes `findings`.
The local service runs parsing and elaboration in a timed isolated worker.
It checks the identity of the prepared parser and validates each response's
source identity, shape, types, coordinates and budget. Compiler requests reject
client-supplied `mode` fields. Source, expression and result type all invalidate
stale output.

Runnable examples demonstrate generic instantiation, safe vector lookup, dependent
length preservation, multi-quote raw string literals with allocation-free checked
`Format.Write(ref builder, $"...")` formatting, nominal records with total
read-only expression properties, `with { ... }` updates, declaration-order labeled
constructor patterns, `if (...) ... else ...` expressions, `let ... else` /
`if (x is ...)` guards, and explicit proofs, with independently expected console
answers.
All examples share one selector and one source buffer. Debounced source checks
automatically update diagnostics and editor-service availability. Compilation
reports diagnostics for the current buffer, including the
[generic type parameter naming lint](authoring-tools.md#generic-type-parameter-naming).
Formatting, pure lints and LSP inspection are available where their producers
support the source. Edits clear old diagnostics and results, including in
plain-text fallback. Late analysis must never restore services or output for
an obsolete source or connection.
Label elaboration and compile-time reduction accurately: neither is a kernel verdict.

Acceptance requires independent evaluator and injection/refusal controls, actual
HTTP isolation, dependent expressions in ordinary buffers, browser asset checks, focused retained playground
and pure tests, Python validation and corpus checks. Exercise the native parser
with accepted and semantically rejected examples locally when available. Hosted
Host CI on both platforms and every Guest CI lane, including kernel replay of the
new evaluated examples, remain user-managed acceptance. Record pending verdicts
without claiming production qualification.

## Scope and launch

The local playground connects the mathematical elaborator,
[authoring tools](authoring-tools.md) and [language server](lsp-prototype.md).
Launch it with
`python tools/run.py vela-playground` (`python3` on Linux), then open the printed
loopback URL. The command accepts a port, including zero for an available port,
and stops with Ctrl+C. The server never publishes, writes source files or installs
an editor extension. Explicit browser downloads save the current buffer or output
only when requested. Hosting and wider-language qualification retain their owners.

The editor uses pinned Monaco 0.55.1 browser assets from jsDelivr. Internet access
is needed for those editor assets; authored source is sent only to the local
compiler service when launched with a `#token=...` loopback URL, or evaluated
locally in the browser when served statically from [docs/index.html](../index.html)
([docs/app.mjs](../app.mjs), [docs/style.css](../style.css)) on GitHub Pages via
[.github/workflows/pages.yml](../../.github/workflows/pages.yml).
The canonical `docs/` directory owns `index.html`, `style.css`, and `app.mjs`
with relative `./style.css` and `./app.mjs` paths so both static hosting and
`PlaygroundServer` serve the same single-source language overview, tour, compact
reference, and embedded playground without a duplicate asset tree. The browser must clearly report an editor-load failure and
offer plain-text editing with the same compile/evaluate controls. This fallback
does not claim Monaco highlighting or inline editor providers; the inspector
panels still use the local language services. The
[third-party record](../../THIRD-PARTY.md#browser-editor-assets) owns the
selected upstream terms and intended distribution.

<a id="single-source-unification-and-worker-efficiency"></a>

## Single-source unification and worker efficiency

Q25aj in [the plan](../../PLAN.md#q-assessment-actions) eliminates duplicated
playground assets, drifted in-browser grammar/emission logic, and redundant
evaluation passes across [docs/app.mjs](../app.mjs),
[tools/toolchain/playground.py](../../tools/toolchain/playground.py), and
[tools/toolchain/playground_worker.py](../../tools/toolchain/playground_worker.py):

1. **Single canonical asset root (`docs/`):** `PlaygroundServer` serves
   `docs/index.html`, `docs/app.mjs`, and `docs/style.css` directly; the
   duplicate `tools/toolchain/playground/` mirror is retired.
2. **Exact grammar, `Q25ah` syntax, and `Corelib` Gallina parity:**
   `VELA_GRAMMAR` matches the active and retired keywords of
   [lexer.mll](../../tools/toolchain/parser/lexer.mll) exactly, static and
   in-browser parsing enforce mandatory `let`/`var` local bindings, pure
   in-browser translation emits the canonical `Corelib.Init.Datatypes` /
   `Corelib.Init.Nat` Gallina of [tools/toolchain/__init__.py](../../tools/toolchain/__init__.py),
   and the example catalog exercises compilation, findings and console evaluation
   across the Python/OCaml worker and `browserApi`.
3. **Unified client utilities and highlighting:** Static code cards and Monarch
   share a single grammar-driven lexical table, Web Crypto (`crypto.subtle`)
   replaces custom bitwise SHA-256 boilerplate, and a unified cancellation/ticket
   helper replaces per-panel ticket counters.
4. **Console evaluation and parser identity.** The local worker passes the source
   and expression directly to the mathematical evaluator. The browser can reuse
   the elaborated module for an unchanged source. The local server verifies its
   parser's identity before accepting worker results.

## Browser behavior

Provide an editable source pane, examples, a diagnostics view, a read-only
Gallina output pane and a console for closed expressions. Include accessible
labels, keyboard actions, a responsive layout and connection/error status.
A successful check means only that
the unqualified prototype reported no error. It supplies no kernel, source
correspondence, native execution or production-admission verdict.

Lexical highlighting is a syntax-only Monarch projection. Hover, definition,
references, document symbols, inferred-type hints, full semantic tokens and
explicit formatting consume the existing server's advertised capabilities.
The browser initializes a separate LSP session, synchronizes full unsaved
snapshots with monotonically increasing versions and serializes transport.
Discard diagnostics, editor replies and compiled/evaluated output after the
source or relevant input changes. Formatting applies only to its requested
unchanged snapshot. Render source-derived strings as text, including console
output and hover documentation. Completion, imports and wider semantics are
not advertised by this demo.

For pure source, Compile shows the actual Gallina returned by `translate` for the exact UTF-8
source. The expression console selects `Nat` or `bool` and uses the mathematical
evaluator for every buffer. The local API validates the complete original
source and exactly one synthetic constant initializer before returning its
typed value.
Reject declaration injection, unsupported constructs and resource exhaustion.
The authored source stays unchanged; the console describes the value as a
compile-time result. There is no runtime standard-output or native-code claim.

## Local transport

Bind only IPv4 loopback, use a random startup bearer token in the printed URL
fragment and require it for every API call. Remove the fragment from the visible
URL after reading it. Check the exact Host and any supplied Origin against the
bound loopback authority; never enable wildcard CORS. Serve only a fixed static
asset allowlist. No client-selected disk path, shell command, proxy, workspace
read or generated-file publication is exposed. Apply no-store and
no-referrer response policy and prevent framing.

The JSON API is same-origin POST with `Authorization: Bearer TOKEN`:

| Path | Request | Response |
| --- | --- | --- |
| `/api/session` | `{}` | `{ "session": "opaque-id" }` |
| `/api/close` | `{ "session": "opaque-id" }` | `{ "closed": true }` (idempotent session release) |
| `/api/lsp` | `{ "session": "opaque-id", "message": LSP_OBJECT }` | `{ "messages": [LSP_OBJECT] }` |
| `/api/compile` | `{ "source": "UTF-8 text" }` | `{ "ok": true, "sourceHash": "sha256", "module": "name", "gallina": "text", "editorServices": true or false, "findings": [] }` |
| `/api/evaluate` | `{ "source": "UTF-8 text", "expression": "text", "valueType": "Nat or bool" }` | `{ "ok": true, "sourceHash": "sha256", "valueType": "Nat or bool", "value": "decimal or true/false" }` |
| `/api/authoring` | `{ "source": "UTF-8 text" }` | `{ "ok": true, "sourceHash": "sha256", "findings": [{ "code": "VELA101", "message": "text", "line": 1, "column": 1 }] }` |

Compiler refusals return `ok: false`, the original `sourceHash`, and an `error`
object containing `kind`, `message`, `line` and `column`. Coordinates are
one-based compiler coordinates; expression errors identify their expression
context. Transport refusals use an unsuccessful HTTP status and an `error`
string. The browser handles both explicitly. No refusal can retain a successful
result for changed input.

Compile refusals also include `editorServices`; evaluation and authoring retain
their existing refusal shapes. The single launch prepares the native parser;
authoring requests remain limited to supported pure source. Mathematical refusals
also include the elaborator's `protocol` and `inference` categories.

Successful compilation returns `findings`, a list of
`{ "code": "VELA105", "message": "text", "line": 1, "column": 1 }`
naming warnings and `VELA107` precedence warnings from the native mathematical
compiler in source order. Require at most 8,192 findings, exact keys, known code,
nonempty text and original source positions. Duplicate, unordered, malformed
or oversized findings refuse the result. Warnings do not prevent Gallina output;
failed compilation returns no findings. A source without lint warnings returns
an empty list.

Use the existing strict protocol JSON reader and its nesting/byte limits, and
validate endpoint shapes. Bound HTTP reads, concurrent requests, session count
and idle lifetime. A single keepalive close request releases a tab's session on
reload or exit; reconnect also closes its previous session. Serialize each
session's `Server.handle` calls, retain the
server's document and isolated-worker limits, and bound complete HTTP replies.
Compile and evaluation use isolated same-interpreter workers with a finite
timeout and bounded input/output; no source becomes Python code. Sessions expire
and shutdown releases server resources. Log no source text or bearer tokens
except the initial local launch URL.

## Authoring and inspection increment

Q25ab in [the plan](../../PLAN.md#q-assessment-actions) extends the local
playground using the existing [authoring tools](authoring-tools.md) and
[pure navigation facts](lsp-prototype.md#pure-navigation-increment). These editor
services cover pure Nat/bool source and follow the same transport and
stale-result constraints as compilation.

An explicit authoring check calls `lint_source` in the
same bounded isolated worker used by compilation. Return advisory VELA100 through
VELA103 findings at original one-based compiler positions. Validate the complete response, known
codes, original-source positions and at most 8,192 findings. Refuse malformed, incomplete, oversized or
failed producer results; an unavailable inspection is never a clean lint result.
The static formatter lays out the original pure tokens and line comments. It rechecks the candidate and compares token spellings, inline comments, documentation attachment and idempotence before offering an edit.

The static page runs its authoring check in the browser. A check changes no
source. Invalidate findings on edits and reconnection.

A visible symbol outline queries the existing document-symbol service. Selecting
a symbol shows its existing plain-text hover, including documentation, and its
resolved references, with navigation to exact UTF-16 ranges. Keep each request
bound to the current source version and session generation, including selection
changes while replies are pending. Clear old inspection on edits or service
failure. These controls also work with plain-text editing. Do not advertise new
LSP capabilities. Display toggles may change inferred-type hints and semantic
coloring without changing compiler judgments.

Offer explicit browser downloads of the current source and current successful
Gallina output; revoke temporary object URLs and disable output export after an
edit. Add examples exercising already supported named arguments, immutable
bindings, documentation and numeric separators. Neither examples nor inspector
controls imply wider-language implementation.

Acceptance adds independent HTTP/worker controls for exact lint findings,
invalid source,
Unicode/newline coordinates, malformed worker results, size/time limits and
recovery. Exercise the browser's authoring check,
outline/documentation/reference navigation, display toggles and
downloads using available local browser infrastructure. If that infrastructure
is unavailable, record the missing browser verification explicitly and retain
focused API/LSP checks and code review as their narrower evidence. Run the
focused playground controls and the [local validation handoff](../../AGENTS.md#tool-execution-and-validation);
record the settled revision and recommended user-managed hosted checks.

## Extended expression examples

Q25ac in [the plan](../../PLAN.md#q-assessment-actions) connects the
[pure expression increment](pure-prototype.md#extended-pure-expressions) to the
existing compile and expression-console APIs. Add examples for Boolean logic,
ordering, inequality and saturating natural subtraction, with expressions users
can evaluate in the console. Highlight the added spellings and retain compiler
formatting, hover, diagnostics and source-bound stale-result behavior. The
browser uses the same compile and evaluate APIs in Monaco and plain-text mode.

## Division and remainder examples

Q25ad in [the plan](../../PLAN.md#q-assessment-actions) exposes the
[natural division and remainder increment](pure-prototype.md#natural-division-and-remainder)
through runnable examples and console suggestions. Show quotient/remainder
grouping, mixed multiplication precedence and the mathematical zero-divisor
results explicitly. Highlight `/` and `%` while preserving `//` comments.
Reuse compiler evaluation, Gallina emission, formatting, diagnostics and editor
facts in both Monaco and plain-text mode. Cover actual HTTP values, emitted
operations, invalid operand types and successful recovery; preserve source and
the existing stale-result checks.

## Acceptance

Land this contract and Q25aa's estimate before implementation. Independently
review the compiler reuse, bridge and stale-response behavior. Focused host
controls cover actual natural/Boolean evaluation and Gallina, malformed and
injected expressions, semantic refusals and limits, immutable source, real LSP
initialization/diagnostics/navigation/formatting, Unicode and version isolation,
cross-session isolation, HTTP authority/authentication/JSON/path/size refusals
and session expiry. Check browser behavior with the available local browser
infrastructure, including an edit, diagnosis, hover, format, compile, evaluate
and rejected-source recovery; record unavailable browser verification explicitly.
Editor asset failure must leave usable compile/evaluate controls.

Run focused behavioral tests and the [local validation handoff](../../AGENTS.md#tool-execution-and-validation).
Record the settled revision and recommended hosted checks.
The user owns publication and Host/Guest CI; pending hosted verdicts do not
block the local demo handoff or qualify Q25n/Q25o/Q25u's independent-client gates.
