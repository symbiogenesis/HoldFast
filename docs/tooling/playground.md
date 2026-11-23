# Vela browser playground

## Scope and launch

Open the [hosted playground](https://symbiogenesis.github.io/VelaLang/) for a
browser-only preview. Launch `python tools/run.py vela-playground` to use the
native compiler, then open the printed loopback URL. The command runs in WSL on
Windows. On Linux use `python3`. Use `--port 0` for an available port and
Ctrl+C to stop the server.

<a id="single-source-unification-and-worker-efficiency"></a>

The hosted and local pages share [index.html](../index.html),
[app.mjs](../app.mjs) and [style.css](../style.css). They load pinned Monaco
assets from jsDelivr and fall back to a plain-text editor if those assets fail.
Authored source is evaluated in the browser or sent to the authenticated
loopback service. [Browser editor asset terms](../../THIRD-PARTY.md#browser-editor-assets)

## Dependent mathematics increment

The native service uses the cached Menhir surface parser and the
[mathematical elaborator](elaboration-prototype.md). It checks the complete
buffer and displays pure compiler Gallina when the source also passes the
pure checker. Other accepted sources show Gallina from the mathematical
elaborator. The hosted page shows pure Gallina for the pure profile and
an evaluation preview with located unchecked claims for wider source.
The hosted evaluator accepts self-contained modules. Imported modules
require the native resolver.

The console checks a closed expression in the source context and returns a
`Nat` or `bool` compile-time value. For example, with
`public Nat Square(Nat x) => x * x;`, evaluate
`At(VCons(Square(7), VNil<Nat>()), FZero<0>())` to get `49`. The native
worker checks that the expression forms exactly one synthetic typed constant
initializer. It refuses declaration injection, runtime dependencies and
exhausted evaluation budgets. Kernel acceptance requires separate replay.
[Replay command](elaboration-prototype.md#commands-and-acceptance)

## Browser behavior

The page offers examples, live diagnostics, source editing, Gallina output and
a compile-time console. It also offers explicit downloads of the buffer and
successful Gallina output. Editing invalidates output and downloads along with
old diagnostics and inspection. Asynchronous replies bind the source and
connection, and console replies also bind the expression and result type.

The local Problems panel highlights each [named goal](elaboration-prototype.md#named-goals)
and shows its status, expected type and available context. The native service
checks its prepared parser, bytecode interpreter, Python executable and
mathematical frontend inputs around each compile or evaluation. The connected
page checks that generation every three seconds. A dependency change clears
the diagnostics and output and expires pending replies. Restart the local
service to prepare a changed compiler.

Lexical highlighting uses a syntax-only Monarch projection. For sources with
pure editor support, the page synchronizes versioned overlays with a separate
LSP session. Formatting returns an edit for the requested buffer version.
Hover, definition, references, symbols, inlay hints and semantic tokens use
the [pure language server's capabilities](lsp-prototype.md). Source-derived
text is rendered as text. Monaco failure leaves compile and evaluate available.

## Local transport

The server binds IPv4 loopback and checks the exact Host and any supplied
Origin. It serves a fixed asset allowlist and applies no-store, no-referrer and
framing protections. The startup URL carries a random bearer token in its
fragment. The page removes the fragment and sends the token on every
same-origin API request. The service accepts source text, with no client
selection of executables or disk paths.

Send API requests as JSON POSTs with `Authorization: Bearer TOKEN`.

| Path | Request | Successful response |
| --- | --- | --- |
| `/api/session` | `{}` | `{ "session": "opaque-id" }` |
| `/api/compiler-generation` | `{}` | Prepared compiler input digest `generation` and Boolean `current` |
| `/api/close` | `{ "session": "opaque-id" }` | `{ "closed": true }` (idempotent) |
| `/api/lsp` | `{ "session": "opaque-id", "message": LSP_OBJECT }` | `{ "messages": [LSP_OBJECT] }` |
| `/api/compile` | `{ "source": "UTF-8 text" }` | `ok`, `sourceHash`, `module`, `gallina`, `editorServices`, `findings` |
| `/api/evaluate` | `{ "source": "UTF-8 text", "expression": "text", "valueType": "Nat or bool" }` | `ok`, `sourceHash`, `valueType`, `value` (decimal or Boolean text) |
| `/api/authoring` | `{ "source": "UTF-8 text" }` | `ok`, `sourceHash`, `findings`, `bindingPreview` |

Compiler refusals return `ok: false`, the source hash, and an `error` object
with `kind`, `message`, `line` and `column`. Compile refusals also return
`editorServices`. Position fields use one-based compiler coordinates.
Named-goal refusals carry an ordered `goals` array. Its entries have
`name`, `line`, `column`, `status`, nullable `expected` and `context`.
Compile and evaluation replies carry the prepared input digest in the
`X-Vela-Compiler-Generation` header.
Expression diagnostics identify expression context. Transport refusals use
an unsuccessful HTTP status and an `error` string.

A finding has `code`, `message`, `line` and `column`. Compilation returns
[mathematical lint findings](authoring-tools.md#lint-policy) in source order,
with at most 8,192 entries. Malformed, unordered, duplicate or oversized
findings fail result validation. Advisory findings do not prevent Gallina
output.

The transport bounds HTTP reads, concurrent requests, response sizes, open
sessions and idle lifetime. Session requests serialize, and closing or
reconnecting releases the preceding session. Isolated compiler workers have
bounded input, output and time. The server validates request shapes and checks
the prepared parser and response bindings before publishing results.
[Server](../../tools/toolchain/playground.py) · [Worker](../../tools/toolchain/playground_worker.py)

## Authoring and inspection increment

The authoring check reports the pure naming, documentation and Boolean
comparison lints. It can return a candidate with explicit `let` bindings for
bare typed declarations. Checking preserves the buffer, and applying the preview
is an explicit editor action. Static formatting checks
token and comment preservation, documentation attachment and idempotence
before returning an edit. The outline and symbol inspector show plain-text
hover and resolved references for the current overlay, with exact UTF-16
navigation ranges. [Authoring contract](authoring-tools.md)

## Extended expression examples

The examples and console exercise Boolean logic, comparisons and saturating
natural subtraction. [Pure expressions](pure-prototype.md#extended-pure-expressions)

## Division and remainder examples

The arithmetic example exercises grouping, precedence and total natural
division and remainder, including zero divisors.
[Operation semantics](pure-prototype.md#natural-division-and-remainder)

## Acceptance

The [HTTP controls](../../tools/tests/test_vela_playground.py) exercise
authentication, session isolation, real editor requests, bounded failures
and stale-result handling. The
[mathematical controls](../../tools/tests/test_vela_playground_math.py)
exercise compile/evaluate, injection refusal, response validation and the
browser assets. Browser interaction and independent editor interoperability
use their own checks. [Local validation](../../AGENTS.md#tool-execution-and-validation) · [Editor qualification](lsp-prototype.md#acceptance-and-remaining-qualification)
