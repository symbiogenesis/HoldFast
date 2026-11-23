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
The [pure editor operations](#pure-editor-operations) supply full semantic tokens
for resolved identifiers and standard document formatting. A formatting request
offers the compiler's canonical layout as an edit for the client to apply.
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
diagnostic. Empty diagnostics mean only that the prototype reported no error.
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

Navigation consumes immutable source-bound declaration identities, types and
occurrences from a complete pure check. Unavailable or refused checks supply
no resolved facts.

Support `textDocument/hover`, `textDocument/definition`,
`textDocument/references` and `textDocument/documentSymbol`; advertise only those
four navigation providers; [authoring hints](#authoring-hints) add the separate
inlay-hint provider; the [pure editor operations](#pure-editor-operations) add
formatting and full/delta semantic tokens. Hover uses plain text with the resolved function
signature or local/parameter type and an explicit unqualified-prototype label.
Definition returns the exact declaration identifier location. References use
resolved identity within the requested document and honor `includeDeclaration`.
Flat `SymbolInformation` lists functions, parameters and local bindings in source
order with exact identifier locations; it makes no function-body span claim.
Use distinct identities for same-spelled declarations in different functions or
sibling branches, and preserve the producer's distinct call/value namespaces and
earlier-function-only rule. Identifier ranges are half-open: positions at their
end, comments, punctuation and whitespace select no symbol.

Require the initialized notification and a synchronized open overlay for every
query. Unknown or closed documents are invalid parameters; desynchronized
documents return ContentModified (`-32801`). Refused source yields null hover
and definition, and empty references and symbols. Malformed query parameters
return invalid parameters (`-32602`). Worker/resource failure returns RequestFailed
(`-32803`), without partial facts, truncation or session termination. Requests
are synchronous and correlated; each result uses the current immutable snapshot.
The server retains at most one successful, fully validated inspection per open
document (at most 16). Immutable facts bind the full snapshot identity, inspector
callable identity and server inspection generation, so hover, navigation, hints
and semantic tokens reuse one compiler inspection and one validation pass for
unchanged text. Each projected reply still receives its own byte-bound check.
Unavailable, malformed, failed and timed-out inspections are never cached;
the next query retries the producer.

Changes (including same-text and empty updates), refused updates, saves,
configuration/dependency invalidation, close, shutdown and exit discard affected
facts. Replacing the inspector callable or explicitly advancing the inspection
generation also requires fresh facts. Compiler or external toolchain replacement
requires restarting the server or sending a configuration/watched-file
invalidation; cache hits do not probe files or launch WSL to discover changes.
A result for an old snapshot or producer generation cannot become a result for
a newer one. URI strings grant no disk access, and query responses cannot publish
accepted artifacts.

Use the same isolated interpreter and five-second worker bound as diagnostics.
An inspection may contain at most 1,024 declarations and 4,096 identifier
occurrences, including declarations; exceeding either refuses inspection without
changing ordinary translation. Its internal JSON result is either
`{"status":"unavailable","reason":KIND}` or an object with `status: "ok"`,
`symbols` and `occurrences`. Each symbol has `name`, `kind` (`function`,
`parameter`, `variable` or `constant`), `detail`, structured `type` and one-based
normalized code-point `line` and `column`. Scalar types record `kind: "scalar"`
and `name` (`Nat` or `bool`). Callable types record `kind: "function"`, `result`,
Boolean `const` and an ordered `parameters` list whose entries contain scalar
`type` and Boolean `required_static`. Validation checks these compiler-produced
types against symbol kinds, declaration facts and presentation signatures; the
adapter supplies no type inference. Each symbol's index is a snapshot-local
identity. Each occurrence has
`symbol` (that index), `line`, `column` and boolean `declaration`. Validate the
worker shape, bounds, identity links and exact source spelling before converting
positions through the shared source API. Worker output and each complete reply
retain the 1,048,576-byte bound; an oversized result is refused as a whole.
The isolated worker adds `source_sha256` to every inspection response, including
unavailable and over-budget results. The transport verifies it against the exact
input bytes before projecting or caching facts; missing or mismatched bindings
refuse the request, and the next query retries the producer. This binds worker
output to its input without adding a source-correspondence proof.

[Declaration documentation](authoring-tools.md#documentation-comments) extends a
public function or constant symbol with an optional `documentation` record:
`text`, an original-byte half-open `span`, and the original-byte `declaration`
start. The parser records that start without extending either native AST schema.
The compiler attaches only a directly preceding contiguous triple-slash block;
blank lines, ordinary comments and intervening source break attachment. Text
removes the slashes and at most one following space per line, and uses LF between
lines while retaining all other UTF-8 content. An attached block may supply at
most 8,192 UTF-8 presentation bytes; overflow refuses inspection without affecting
ordinary translation. XML-looking documentation remains authored plain text.

Hover includes the declaration's documentation for both its declaration and
references. The projection checks comment bytes, rendered text, adjacency and
the declaration/name source link before rendering it; it performs no name
resolution or semantic checking. The documentation field is optional. Incomplete,
forged or stale documentation records refuse the entire inspection. Overlay edits and configuration changes use existing snapshot
invalidation, so changed or removed documentation cannot survive in cached facts.

Navigation tests check exact signatures, types, definition sites,
reference sets, scope, UTF-16 coordinates and unsaved edits over stdio.
[Client qualification](#acceptance-and-remaining-qualification)

## Authoring hints

`textDocument/inlayHint` reports inferred local types in completely checked
pure source. Requests contain a valid
half-open document range; return type hints at the ends of inferred local
identifiers wholly contained in that range, with `kind: 1` and labels such as `: Nat` or
`: bool`. Parameter declarations and explicit signatures need no redundant hint.
The identifier may end exactly at the requested range's end, which also anchors
its hint there. Use the compiler's existing resolved symbol facts; do not reparse source or infer
types in the protocol projection. Labels are diagnostic presentation and never
insert source, conversions, loans, proof steps or accepted artifacts.

Requests require an initialized session and a synchronized overlay. Invalid
coordinates, refused source and worker failures follow the navigation policy.
Invalid or unsupported source supplies no hints. [Hint fixtures](../../tools/tests/test_holdfast_lsp_hints.py)

The pure checker diagnoses mutation and resource syntax outside its subset.
[Binding syntax](../language/surface-grammar.md#bindings-match-arms-and-generic-calls)
defines mutable and immutable locals. Receiver-mode hints and conflict
explanations require the corresponding compiler facts.
[Wider editor contract](tooling-protocols.md#language-server-protocol)

Constants are compiler-resolved `constant` symbols, with details such as
`const Nat Limit = 16` and LSP document-symbol kind 14. Their references and
definitions use the same source identities and bounds as other symbols. Neither
the editor adapter nor the inspection transport evaluates constant expressions.
Explicit constant types receive no inferred-local hint; failed static evaluation
removes the entire snapshot's semantic facts until a valid edit restores them.

## Pure editor operations

The compiler formatter and resolved inspection facts serve pure formatting
and full or delta semantic tokens for synchronized overlays.

`textDocument/formatting` returns no edits for canonical source, otherwise one
edit replacing the complete original document with the checked canonical text.
Use the shared source adapter for the original UTF-16 end position, including
terminal newlines. The formatter retains its token/comment, attachment, syntax
and idempotence checks and uses the layout in the
[authoring contract](authoring-tools.md#common-style). Standard formatting options
must contain a positive integer `tabSize` and Boolean `insertSpaces`; canonical
compiler style determines the resulting layout regardless of those preferences.
The server never applies an edit, writes a file or runs the compiler command's
automatic publication. Invalid or unsupported source returns no edits. A bounded
formatter failure returns RequestFailed, including expansion beyond the source
bound; never return a partial edit. Run formatting in the existing isolated
five-second worker and validate its complete, bounded transport result.

`textDocument/semanticTokens/full` advertises full tokens with delta support and a fixed legend with token types
`function`, `parameter`, `variable`, in that order, and modifiers `declaration`,
`readonly`, in that order. Project every resolved identifier occurrence in source
order. Constants use `variable`; parameters, constants and immutable locals have
`readonly`, while declaration occurrences also have `declaration`. Functions have
no `readonly` modifier. Encode the standard five-integer relative token records,
with UTF-16 lengths and same-line relative starts. Keywords, literals, comments
and unsupported syntax receive no invented semantic facts. Invalid or unsupported
source returns an empty token stream. Do not advertise range tokens.
Retain existing inspection validation, complete-output limits and
worker failures; never truncate a token stream.

Clients that offer `textDocument.semanticTokens.requests.full.delta: true` receive
a 64-character opaque `resultId` alongside each complete token stream. Full-only
clients retain the data-only response. `textDocument/semanticTokens/full/delta`
requires a string `previousResultId`; it returns the current result ID and either
standard integer-array edits or a complete current stream when the base is unknown.
Edits replace one differing integer interval after removing the shared prefix and
suffix; unchanged streams return no edits. The consumer applies edits to its prior
encoded stream before decoding token records. Delta offsets count integers,
including changes inside a five-integer token record.

The server retains at most one immutable delta base per open document, bounded by
the existing 4,096-occurrence inspection limit. A base records only the previously
published token array, producer identity and inspection generation. Valid text
updates retain that array for comparison against freshly checked current facts;
it supplies no facts about the new source. A successful full/delta response
replaces the base only after the complete correlated reply passes its byte bound.
Failed publication leaves the prior base usable. Saves, refused updates,
configuration/dependency invalidation, explicit generation advances, close,
shutdown and exit discard affected bases. Producer replacement, cross-document
IDs, evicted IDs and IDs from earlier document lifetimes receive complete current
tokens. Unavailable source removes the old stream through a complete empty result
or deletion delta; worker failure returns RequestFailed without publishing a base.

The [client qualifier](#acceptance-and-remaining-qualification) reconstructs
semantic token streams from full and delta replies and joins each edit to its
snapshot and base ID. It checks UTF-16 edits, unknown bases and configuration
invalidation, including Vim's full and incremental synchronization modes.

These requests require `initialized` and a synchronized open document. Retain the
navigation errors for malformed parameters, unopened/closed documents, refused
updates and resource failures. Compute each response from the current immutable
snapshot; changes and configuration invalidation cannot reuse old results. An
unknown URI grants no filesystem access. Existing request, reply, source,
inspection and timeout bounds apply to the complete operation.

Formatting and token controls cover exact edits and token streams, source
identity, malformed replies, UTF-16 positions and recovery after unsaved edits.
[Editor fixtures](../../tools/tests/test_holdfast_lsp_editor.py)

## Callable discovery

The server advertises `textDocument/completion` and
`textDocument/signatureHelp` over synchronized, completely checked overlays.
Both reuse the validated compiler inspection and its existing source, dependency,
configuration and producer invalidation. Unopened documents and malformed
positions refuse; unavailable source returns an empty incomplete completion list
unless the [bounded recovery producer](#single-expression-recovery-completion)
supplies a unique scalar repair. Signature help remains null for unavailable
source. Worker failures return RequestFailed. Complete response
byte bounds and the final current-source/current-producer check apply before
publication, including when a request ID leaves little reply space.

Completion selects an existing resolved callable identifier, including its end
position, and matches the prefix before the cursor. It supplies the selected
function and compatible functions declared before it: matching structured
callable types, static qualifiers and parameter labels preserve the existing
call's argument interface. Every candidate is already callable at this source
site. The conservative list has `isIncomplete: true`; it supplies no exhaustive
scope claim. Items carry the compiler signature, plain-text documentation when
present, function kind 3 and a single `textEdit` replacing the complete selected
identifier. The server leaves the overlay untouched. Declarations,
punctuation and unsupported contexts yield no candidates. Wider incomplete-input
and cross-package completion retain their producer prerequisites.
No completion resolver, snippets or additional edits are advertised.

At a resolved value-expression identifier, the pure resolver supplies its visible
same-type values: parameters, preceding locals and constants, with local names
overriding same-spelled module constants. Choices exclude other functions'
parameters, later declarations, sibling-branch locals and the binding currently
being initialized. Callable and value namespaces remain separate. A selected
required-static value offers only required-static parameters and constants;
the adapter performs no evaluation or scope reconstruction. A named-argument
label is a callable parameter reference and supplies no value choices.

The worker's opt-in completion mode records source-ordered value sites and
resolved symbol identities during the same complete check. The transport caps
the aggregate at 8,192 choices across the existing 4,096-occurrence bound; a
producer or consumer budget failure refuses the operation. Validation requires
ordered unique sites, valid same-type value identities, unique visible names,
the selected binding and agreement with static qualifiers. Cached facts contain
immutable tuples and retain the normal producer/snapshot invalidation.
The completion inventory is optional. An unrecorded site supplies no value
suggestions. Neither absence nor an empty site
inventory establishes that no compatible values exist. A present site record
must contain the selected binding; an empty or malformed choice record refuses.

Value items use variable kind 6 or constant kind 21, the compiler's type/value
detail and available plain-text declaration documentation. Prefix matching and
the single complete-identifier `textEdit` follow callable completion. Lists remain
`isIncomplete: true`; they promise compatible choices at an existing checked
identifier, without a whole-scope or successful edited-program verdict.
No proposal applies itself or supplies an acceptance receipt. Independent host
controls cover scope/order/shadowing, Boolean and static compatibility, malformed
and over-budget facts, cache detachment, source/producer invalidation and complete
reply bounds. A real stdio session checks value edits before and after an unsaved
supplementary-comment/CRLF update. The pinned Neovim and Vim full/incremental
sessions additionally qualify an explicit value-completion probe: the exact
constant and required-static parameter choices, edit ranges and details join to
the retained source, cursor, wire response and client observation. Missing probe
traffic, altered choices and mismatched observations refuse qualification.

Completion also accepts checked natural-number and Boolean literal tokens. The
compiler records their same-type visible values while checking each expression;
the server proposes replacing the complete literal, including every numeric
separator, with a selected value name. All cursor positions within the literal,
including its end, use that same edit range. Literal spelling supplies no name
prefix filter. Scope, shadowing and declaration order follow the resolver's
identifier choices; a binding is unavailable inside its own initializer.

When a literal occurs in a constant initializer or a required-static call
argument, the compiler narrows its choices to constants and required-static
parameters throughout the enclosing expression. Ordinary call arguments retain
runtime choices. This records the producer's static-input requirement without
evaluating proposed edits or inferring another type in the adapter.

The optional `literal_completions` inventory binds each site's exact spelling,
scalar type, static requirement and ordered symbol identities. The consumer
checks the complete token against the existing compiler token producer and
validates candidate types, source order, uniqueness and static eligibility.
Identifier and literal sites share the 4,096-site and 8,192-choice budgets;
budget exhaustion refuses the entire operation. Empty literal choices are valid;
omitted inventories provide no literal suggestions. Cached tuples detach from
mutable producer replies and invalidate with source, producer and configuration
changes. Literal lists remain `isIncomplete: true` and are explicit proposals.

The [literal completion controls](../../tools/tests/test_holdfast_lsp_literal_completion.py)
cover full separator-containing edits, Boolean types, sibling scopes,
self-initializers, shadowed constants, nested static arguments, malformed facts,
shared budgets and cache invalidation. A real stdio session verifies exact edits
before and after an unsaved supplementary-comment/CRLF update. Wider-language
completion retains its producer prerequisites; literal completion adds no
advertised semantic acceptance claim.

### Single-expression recovery completion

When ordinary inspection is unavailable, completion can repair one empty or
unfinished value expression in otherwise checkable pure source. The compiler's
[bounded repair producer](../../tools/toolchain/completion.py) selects a complete
identifier under the cursor or an empty insertion boundary using the existing
token producer. Comments, interiors of other tokens and invalid Unicode/CRLF
boundaries refuse. It checks at most two modified sources, inserting `0` and
`false`, through the existing checked parser and pure resolver. Exactly one
successful scalar repair must record that literal's completion context. Zero or
two successful repairs supply no proposals: unconstrained initializer types,
unrelated unresolved names, missing delimiters and wider syntax remain unsupported.

The repair's existing resolver facts determine visible values, lexical scope,
shadowing, source order, scalar types and static-input restrictions. The editor
adapter validates the complete repaired facts against the exact reconstructed
source, then projects only the selected literal's value alternatives onto the
original snapshot. An unfinished identifier uses its prefix before the cursor
and replaces the whole original identifier; an empty expression receives a
zero-width insertion. Every proposal remains an explicit single `textEdit` with
`isIncomplete: true`. The original overlay and diagnostics stay unchanged, and
repaired facts supply no hover, navigation, token, formatting or acceptance result
for the original source.

One isolated worker has five seconds for both repairs. Source, concrete-piece,
inspection, choice and complete-response limits apply to the entire operation;
timeouts and malformed or stale source bindings return RequestFailed. The final
publication check binds the original snapshot, completion producer, inspector
and configuration generation; a concurrent replacement invalidates the reply.
Injected inspection producers require an explicitly paired completion producer,
so a test or alternate producer cannot silently fall back to another compiler.

The [independent recovery controls](../../tools/tests/test_holdfast_lsp_recovery.py)
cover typed numeric and Boolean insertions, full identifier edits, prefix filters,
branch scopes, required-static arguments, ambiguity and unrelated-error refusals,
malformed repair facts and producer invalidation. A real stdio session verifies
the original diagnostics and exact completion edits before and after an unsaved
supplementary-comment/CRLF update. Pinned Neovim and Vim full/incremental sessions
exercise an unfinished identifier in an unsaved Unicode/CRLF source. Independent
wire checks join the source, cursor, expected edit and client observation while
requiring the original name-error diagnostic. Missing traffic, changed edits,
different source/cursor and detached observations refuse qualification. Wider
incomplete-source behavior retains its producer prerequisites.

### Signature help

Signature help selects the innermost checked call whose argument list contains
the cursor, through the closing parenthesis's start. The existing compiler token
producer supplies bounded punctuation and trivia boundaries; resolved function
occurrences supply callable identities. A single balanced-delimiter pass counts
only commas belonging to each call, so nested calls, grouped expressions, named
arguments and comments containing punctuation retain the correct active parameter.
The 16,384-piece concrete-token limit applies; exhaustion refuses the complete
request. Signatures preserve declaration parameter names and `const` modes, with
plain-text documentation. Zero-argument calls omit `activeParameter`; a trailing
comma selects the final actual parameter. No context after the closing delimiter
or inside a declaration supplies a signature. Triggers are `(` and `,`, with `,`
as a retrigger. The adapter adds no name resolution or type inference.

Independent controls cover prefix filtering, exact edits, distinct function/value
namespaces, incompatible and forward candidates, nested and named arguments,
zero/static/trailing parameters, supplementary comments and mixed newlines,
refused source, incremental edits, lifecycle and producer invalidation. A real
stdio session checks both providers before and after an unsaved Unicode/CRLF
edit. Pinned Neovim and Vim sessions request both operations explicitly; their
observations and exact wire responses join to the expected source and cursor.
Missing traffic, changed suggestions/signatures, mismatched observations and
stale source positions refuse qualification. The [rename qualification](#local-rename-previews) covers both
version-capable clients. Wider language services remain open under the
[editor contract](tooling-protocols.md#language-server-protocol).

## Local rename previews

The server supports `textDocument/prepareRename` and
`textDocument/rename` for compiler-resolved local `let` variables. Functions,
parameters and constants return null: their public or callable uses require
package-wide facts that this producer does not supply. A token-end position,
comment, punctuation or refused complete source also returns null. Same-spelled
variables in sibling branches retain distinct identities.

Advertise `renameProvider: {prepareProvider: true}` only when the client offers
`workspace.workspaceEdit.documentChanges: true`. Preparation returns the exact
selected identifier range and its current spelling. Rename returns a single
`TextDocumentEdit` containing the open URI, its exact integer version and all
resolved declaration/reference edits for the selected variable. The server
preserves the overlay and disk; applying the preview belongs to the client,
which must refuse an edit after that document version changes. A same-name
request returns an empty versioned edit list. A client without versioned edit
support receives RequestFailed (`-32803`) for either request.

Validate the requested spelling with the pure compiler's identifier and keyword
vocabulary. Invalid names return invalid parameters (`-32602`). Construct a
candidate by replacing only the resolved identifier byte ranges, then run the
existing isolated compiler inspection over that complete candidate. Compare every
declaration's kind and structured type and every occurrence's resolved identity,
declaration flag and translated range with the original facts. This catches a
capture even when the edited source still typechecks. A failed candidate or any
changed binding refuses the entire preview. ASCII identifiers let position shifts
preserve supplementary comments, original UTF-8 bytes and LF/CRLF/bare-CR layout.
No second resolver or type inference is added.

Use the existing current-snapshot inspection cache for preparation and the source
side of rename. Recheck the candidate separately without caching it as a live
overlay. Before publishing, require the original overlay, synchronization state,
inspector callable and configuration/dependency generation to remain current.
Saves, source changes, refused edits and configuration/dependency invalidation
retain the normal navigation cache rules. Source, inspection and complete-reply
bounds apply; each compiler worker retains its five-second limit.

Independent controls cover exact previews, declaration/reference selection,
same-name edits, sibling identities, separate call/value namespaces, invalid
names, duplicates, type-correct capture, CRLF and supplementary comments,
unsupported clients, desynchronization and source/producer changes during
candidate checking. The pinned Neovim qualifier explicitly offers versioned
document edits and checks successful preparation and preview traffic. The pinned
Vim plugin omits that capability and supplies no override API, so both its full
and incremental sessions check the explicit refusal. Retained observations join
the exact responses to wire requests, open source and document version; changed
versions, incomplete edits and mismatched observations fail replay.

`python tools/run.py holdfast-lsp --qualify-rename --output rename.json` qualifies
application in Neovim 0.11.0 and GNU Emacs 30.2 with Eglot on Ubuntu 26.04
ARM64. Windows runs the clients in WSL and writes the report to the requested
host path. Install the [pinned client packages](../../THIRD-PARTY.md#independent-editor-clients)
before running the command. Both clients prepare a local rename against their
unsaved Unicode document, apply the returned versioned edit with their own
workspace-edit implementation, and look up the declaration from the renamed use.
Replaying the original edit against the newer buffer preserves its bytes and
binding. An unrelated parameter of the same name and the on-disk file retain
their original spellings.

The report retains both editor observations and both bidirectional transcripts.
The qualifier reconstructs the document version at each request and checks the
exact preparation, two edits, declaration locations, and client buffer contents.
The existing Vim sessions continue to exercise refusal for a client that omits
versioned document edits. Workspace-wide rename still requires resolved package
identities and reference coverage.

## Acceptance and remaining qualification

Constant-compatible functions and required-static parameters retain their `const`
qualifier in compiler-produced hover signatures. A symbolic local constant has a
typed constant identity before its static inputs are instantiated; the editor
must not invent an evaluated value. Changes to a parameter's static requirement
invalidate the complete source snapshot, including navigation and diagnostics.

Wire tests check UTF-8 framing, strict JSON, lifecycle, overlay edits and
bounded refusals. Coordinate tests use independent UTF-8 and UTF-16
expectations for mixed line endings and supplementary characters. An invalid
update preserves the previous snapshot and desynchronizes the document.
The server accepts source text through overlays.

`python tools/run.py holdfast-lsp --qualify-clients`
([`lsp_clients.py`](../../tools/toolchain/lsp_clients.py)) executes the two
pinned independent editor clients recorded in
[THIRD-PARTY.md](../../THIRD-PARTY.md#independent-editor-clients)
— Neovim `0.11.0` (`vim.lsp`, incremental sync) and Vim `9.1.2141` +
`yegappan/lsp` (`58eac06e81bad174cfa897614ae01adf0d31d10a`, both full and
incremental sync) — against `holdfast-lsp --transcript`, verifying bidirectional
wire transcripts and client observations against independent expected oracles in
[`test_holdfast_lsp_clients.py`](../../tools/tests/test_holdfast_lsp_clients.py).
The schema-2 report embeds each session's transcript and editor observations,
their digests and a traffic summary. Use `--output FILE` to save the report.
The exercised subset includes diagnostics, navigation, hints, formatting,
full and delta semantic tokens, callable discovery and value completion.
The [rename qualifier](#local-rename-previews) exercises versioned edit
application separately. [Wider requirements](tooling-protocols.md#qualification-and-delivery)
