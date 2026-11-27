# HoldFast host language server prototype

## Connect an editor

`python tools/run.py holdfast-lsp` starts a stdio server for the
[pure Nat/bool compiler](pure-prototype.md). It uses LSP 3.17-compatible
messages. Its diagnostics and editing services use the compiler's checked
source and resolution facts.

To connect a host editor, configure its stdio language-server command as `python`
with arguments consisting of the absolute path to `tools/run.py` followed by
`holdfast-lsp`; use `python3` on Linux. Associate HoldFast buffers with language ID `holdfast`
and the `.hf` extension. No editor extension or automatic registration is
installed by this command. The server uses open-buffer text and does not read the
URI's file. Diagnostics and navigation cover only the pure subset linked above.

For Neovim 0.11's built-in LSP client, adapt these absolute paths in `init.lua`
and reopen a `.hf` file. This configuration uses the
[documented client configuration API](https://github.com/neovim/neovim/blob/v0.11.0/runtime/doc/lsp.txt).
The [client qualifier](#acceptance-and-remaining-qualification) checks
interoperability with the pinned editors.

```lua
vim.filetype.add({ extension = { hf = 'holdfast' } })
vim.lsp.config['holdfast'] = {
  cmd = { 'python', 'C:/src/HoldFast/tools/run.py', 'holdfast-lsp' },
  filetypes = { 'holdfast' },
  root_markers = { '.git' },
}
vim.lsp.enable('holdfast')
```

Use the manifest's Python minor version and `python3` on Linux. Prepare the locked
environment once with `python tools/run.py holdfast-lsp --help` before the editor's
first connection. In Neovim, `K` shows hover, `grr` finds references, `gO` lists
document symbols and `:lua vim.lsp.buf.definition()` jumps to a declaration.
Only complete sources accepted by the pure checker provide navigation; incomplete
or unsupported code continues to receive the producer's diagnostic.
Editors with standard inlay-hint support can also show inferred local `Nat` and
`bool` types through the [authoring-hint provider](#authoring-hints).
The [pure editor operations](#pure-editor-operations) supply semantic tokens
for resolved identifiers, with delta updates for supporting clients, and offer
the compiler's canonical layout as a formatting edit for the client to apply.
The [discovery providers](#callable-discovery) offer explicit callable and value
completion edits and argument-sensitive signature help in completely checked
pure source. [Single-expression recovery](#single-expression-recovery-completion)
also supplies bounded value proposals for selected unfinished pure expressions.

## Interface and bounds

Support initialize/initialized, shutdown/exit, incremental document synchronization
(open/change/save/close), push diagnostics and cancellation notifications over
stdio. Advertise UTF-16 positions and incremental synchronization. Unknown requests
return method-not-found; pre-initialization requests return server-not-initialized.
Refuse repeated initialization and requests after shutdown. EOF or exit before
shutdown is an unsuccessful session. Logs use stderr. No filesystem, process
launch requested by the client, workspace traversal or network service is exposed.

Immutable snapshots bind URI, document version, source bytes and a monotonically
increasing session generation. URIs are opaque identifiers, never authority to
read disk. Diagnostics use the existing checker's one-based Unicode code-point
coordinates after newline normalization, converted explicitly to zero-based
UTF-16 positions. Shared source utilities also convert half-open UTF-8 byte
offsets, rejecting offsets inside encoded characters or CRLF. Handle LF, CRLF,
bare CR and supplementary characters. Full unsaved text replaces earlier text;
ranged edits use zero-based UTF-16 positions in the preceding edit's result.
Convert positions back to exact UTF-8 boundaries without normalizing stored text.
Clamp character offsets beyond a line's end as LSP requires; refuse negative or
non-integer coordinates, nonexistent lines, reversed ranges and positions inside
a supplementary character. An optional deprecated `rangeLength` must match the
removed UTF-16 units, counting CRLF as two units. Apply each notification's edits
in order and publish only its final snapshot. Versions strictly increase, and an
invalid edit anywhere in a notification leaves the previous snapshot and session
generation unchanged.
Remember a newer received version even when its replacement text is refused;
an older later update cannot restore synchronization.
Close clears diagnostics. Save rechecks the overlay. Configuration and watched-file
changes invalidate and recheck all open snapshots conservatively. There are no
import or interactive-proof providers. The [local rename preview](#local-rename-previews)
and [Boolean comparison action](authoring-tools.md#checked-boolean-comparison-previews)
return edits for a specific document version. Navigation consumes the pure
compiler's resolution facts.

| Resource | Bound and refusal |
| --- | --- |
| Frame headers | 8,192 bytes; ASCII CRLF lines and exactly one decimal Content-Length; malformed/truncated frames close the session |
| Frame bodies and replies | 1,048,576 bytes; strict UTF-8 JSON objects, unique keys and finite numbers; malformed JSON receives a parse error and valid non-message JSON an invalid-request error |
| JSON nesting | 64 containers, counted outside strings before decoding; over-budget input closes the session |
| Documents | 16 open documents, each at most the pure producer's 65,536 UTF-8 bytes; URI at most 4,096 UTF-8 bytes |
| Changes | At most 64 sequential edits per notification; every intermediate text must fit the document bound; an empty batch advances a synchronized document's version without changing its text |
| Diagnostic output | One producer error per document; message at most 4,096 characters; include version and snapshot identity, never an acceptance claim |
| Work and concurrency | One synchronous check at a time, isolated worker timeout 5 seconds; no queued/background work or late publication |

Unsupported language constructs receive the producer's explicit unsupported
diagnostic. An empty diagnostic list can reflect a successful check, a close,
or a refused update that cleared earlier diagnostics.
Every reply, including initialization and errors, must fit the frame bound.
An oversized initialization result returns RequestFailed without initializing the
session. Error replies retain correlation when a bounded refusal can carry the
request ID; if even the shortest correlated refusal cannot fit, return a bounded
RequestFailed with null ID. Either refusal leaves the session usable for later
bounded requests.
Cancellation has no outstanding asynchronous work to cancel; it cannot undo a
published notification. A worker timeout produces a diagnostic for that snapshot.
Invalid document notifications clear diagnostics for the affected open document,
are logged and leave overlays unchanged.
Save and invalidation cannot republish diagnostics for a refused edit's old text;
a valid full replacement or close/reopen restores synchronization. A ranged edit
cannot use a desynchronized overlay; a change batch must begin with a full
replacement before any subsequent ranged edits can restore synchronization.

## Pure navigation increment

Consumes immutable source-bound declaration IDs, types, and occurrences from complete pure checks (refused/unavailable checks yield nothing). Advertises `textDocument/hover`, `definition`, `references`, and `documentSymbol` (plus [inlayHint](#authoring-hints) and [formatting/semanticTokens](#pure-editor-operations)). Hover shows plain-text signatures/types labeled as unqualified prototype; `definition` gives declaration identifier spans; `references` honors `includeDeclaration` within document; flat `SymbolInformation` lists functions, params, and locals in source order (distinct IDs across functions/branches, separate call/value namespaces, earlier-function-only rule, half-open identifier ranges excluding end/comments/punctuation/whitespace).

Requires `initialized` and synchronized open overlays: unknown/closed docs -> `-32602`, desynchronized -> `ContentModified` (`-32801`), refused source -> null hover/def and empty refs/symbols, malformed params -> `-32602`, worker/resource failure -> `RequestFailed` (`-32803`). Synchronous, correlated, per-doc cache (1 successful inspection, max 16 docs) bound to snapshot, inspector, and generation (failed/timed-out/unavailable results never cached; edits/saves/invalidations/close/shutdown/exit discard facts; cache hits never probe disk/WSL; URIs grant no disk access).

Uses 5 s isolated worker (max 1,024 declarations, 4,096 occurrences, 1,048,576 B output/reply; `{"status":"unavailable","reason":KIND}` or `{"status":"ok", symbols, occurrences}` with `kind` in `{function,parameter,variable,constant}`, `detail`, structured `type`, 1-based code-point `line`/`column`, and `source_sha256` verified against input bytes). [Declaration documentation](authoring-tools.md#documentation-comments) optionally attaches directly preceding contiguous `///` blocks (max 8,192 UTF-8 bytes; LF-joined plain text stripping `/// ?`; missing/forged/stale docs refuse inspection) shown on declaration and reference hovers. [Client qualification](#acceptance-and-remaining-qualification)

## Authoring hints

`textDocument/inlayHint` emits `: Nat` / `: bool` (`kind: 1`) at inferred local identifier ends wholly inside valid request ranges (omitting params/explicit types; adapter never reparses or infers; labels insert nothing). Constants show `constant` kind 14 symbols without `const` hints or adapter evaluation (failed static eval invalidates snapshot facts). [Hint fixtures](../../tools/tests/test_holdfast_lsp_hints.py) · [Wider editor contract](tooling-protocols.md#language-server-protocol)

## Pure editor operations

- `textDocument/formatting`: returns empty edits for canonical source else 1 full-document replacement edit in canonical compiler layout (ignoring `tabSize`>`0`/`insertSpaces` prefs; succeeds on valid pure syntax despite semantic errors; malformed/unsupported -> empty; overflow/timeout -> `RequestFailed` without partial edits; 5 s worker; never mutates overlay/disk).
- `textDocument/semanticTokens/full` & `/delta`: legend types `[function, parameter, variable]`, modifiers `[declaration, readonly]` (constants use `variable`+`readonly`; functions omit `readonly`; 5-int UTF-16 relative records; no range tokens; invalid/unsupported -> empty; never truncated). Delta-capable clients get 64-char `resultId` and integer-interval edits (or full stream on unknown/evicted/cross-doc/stale `previousResultId`); 1 immutable base cached per doc (max 4,096 occurrences), updated only after complete reply passes byte limit and cleared on save/refusal/invalidation/close/shutdown/exit. [Editor fixtures](../../tools/tests/test_holdfast_lsp_editor.py)

## Callable discovery

`textDocument/completion` and `textDocument/signatureHelp` reuse validated inspections (unopened/malformed refuse; unavailable -> empty incomplete list unless [single-expression recovery](#single-expression-recovery-completion) repairs uniquely, and null signature help; `RequestFailed` on worker failure; current-source/producer checks precede publication).

- **Callable completion**: matches prefix at resolved callable identifier (incl. end) to itself and compatible earlier declarations (matching callable types, `const` qualifiers, parameter labels; `isIncomplete: true`, kind 3, plain doc, single `textEdit`, no snippets/resolver/additional edits).
- **Value completion**: at resolved value identifier (not declarations/named-arg labels/unsupported sites), offers visible same-type params, earlier locals, and constants (locals shadow constants; excludes other functions, later defs, sibling branches, self-initializer; `required_static` narrows to static params/constants). Kind 6 (var) / 21 (const); opt-in transport capped at 8,192 choices across 4,096 sites (validates sorted unique sites, types, names, selected binding, static flags; optional site inventory—absent yields none, present empty/malformed refuses). Pinned Neovim/Vim sessions verify exact constant/static probes on wire and buffer.
- **Literal completion**: replaces complete `Nat`/`bool` literals (incl. `_` separators, from any cursor pos inside token, no prefix filter) with visible same-type values (`const` init/arg narrows entire expr to constants/static params); shares 4,096-site / 8,192-choice budget; detached immutable cache. [Controls](../../tools/tests/test_holdfast_lsp_literal_completion.py)

### Single-expression recovery completion

When inspection is unavailable, [completion.py](../../tools/toolchain/completion.py) repairs one empty/unfinished value expression at an identifier or insertion boundary (refusing comments/token interiors/bad UTF-8/CRLF) by trying `0` and `false` through checked parser + pure resolver in one 5 s worker: iff exactly one scalar succeeds, projects its visible same-type values (`isIncomplete: true`, single `textEdit`, leaving overlay/diagnostics unchanged and providing no navigation/tokens/formatting/acceptance; enforced explicit paired producer, full byte/choice/generation checks). [Recovery controls](../../tools/tests/test_holdfast_lsp_recovery.py)

### Signature help

Triggers `(`, `,` (retrigger `,`), selecting innermost checked call containing cursor up to `)` start via balanced delimiter pass over `concrete` tokens (16,384-piece cap; preserves param names, `const`, docs; 0-arg omits `activeParameter`; trailing comma selects last param; outside/declarations yield null; no adapter resolution/inference). Checked via stdio, Neovim, and Vim sessions. [Wider requirements](tooling-protocols.md#language-server-protocol)

## Local rename previews

`textDocument/prepareRename` and `textDocument/rename` cover resolved local `let` variables only (functions/params/constants/ends/comments/punctuation/refused source return null; sibling branches stay distinct), advertised (`prepareProvider: true`) only if client sets `workspace.workspaceEdit.documentChanges: true` (else `-32803`). Invalid spellings -> `-32602`. Applies byte-range replacements to a candidate and re-runs isolated 5 s inspection verifying identical symbol kinds/types and occurrence IDs/flags/ranges (catching type-valid variable capture; failing/changed binding refuses preview; ASCII names preserve UTF-8 comments and LF/CRLF/CR). Reuses cache for prepare/source without caching candidate; returns 1 versioned `TextDocumentEdit` leaving overlay/disk untouched (same-name -> empty edits).

`python tools/run.py holdfast-lsp --qualify-rename --output rename.json` qualifies Neovim 0.11.0 and GNU Emacs 30.2 + Eglot on Ubuntu 26.04 ARM64 ([pinned clients](../../THIRD-PARTY.md#independent-editor-clients)) on unsaved Unicode buffers, verifying versioned edit application, post-rename declaration lookup, stale-version edit refusal, and unchanged parameter/disk text (Vim sessions verify refusal without `documentChanges`). Workspace-wide rename remains open.

## Acceptance and remaining qualification

Constant functions/`const` params show `const` in hover without adapter evaluation; changing static requirements invalidates snapshots. `python tools/run.py holdfast-lsp --qualify-clients` ([`lsp_clients.py`](../../tools/toolchain/lsp_clients.py)) runs Neovim `0.11.0` (`vim.lsp`, incremental) and Vim `9.1.2141` + `yegappan/lsp` (`58eac06e81bad174cfa897614ae01adf0d31d10a`, full+incremental) against `holdfast-lsp --transcript`, checking wire transcripts and client state against [`test_holdfast_lsp_clients.py`](../../tools/tests/test_holdfast_lsp_clients.py) (`--output FILE` saves schema-2 report). [Wider requirements](tooling-protocols.md#qualification-and-delivery)
