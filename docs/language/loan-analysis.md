# HoldFast loan-analysis diagnostic

The loan diagnostic proposes loan ends and reports conflicts and unresolved
obligations over explicit flow facts. The
[core promotion contract](core-design.md#borrow-analysis-promotion) specifies the
additional checks needed for source acceptance.

## Input and composition

The Python API consumes an explicit finite control-flow graph with named
owners, declared field projections, named invariant clauses, shared and
exclusive loans, and parent links. `lower_function` and `lower_module` build
graphs from schema-2 surface ASTs. `analyze_function` and `analyze_module`
combine lowering and analysis.
Events describe borrowing, receiver reservations and activations, access,
resource moves, binding capture environments, uses, per-conjunct invariant
opening and closing (`open ... lifts`),
outcome-specific returns and unsupported suspension boundaries. Each
operation's facts are explicit inputs: a library call does not obtain authority
from its name. Boxes, optional values, cells, callbacks and protocol wrappers use
the same capture and loan facts, without dedicated cases for their type names.
Owner identities and field partitions are supplied abstract facts, not inferred
from source spelling or pointer inequality. Unknown overlap produces an unresolved obligation.

For supported implicit `ref` receivers, the diagnostic models
[reservation and activation](core-design.md#two-phase-receiver-borrows). In
`buf.Update(buf.length)`, the receiver is reserved before the read and activated
after it. A shared view retained into the call conflicts at activation if it
overlaps the receiver. Single-field receiver views identify a footprint.
Compound and indexed views conservatively cover the whole receiver.
[Receiver timing fixtures](../../tools/tests/test_holdfast_loans.py#_located_receiver_timing)

Names must be unambiguous within a path. A child loan must stay within its
parent footprint, and a shared parent can grant only a shared child. Graph
validation rejects missing references, duplicate node identities, malformed
edges, self-loops, irreducible cycles, and nodes with no path to a graph exit.
For supported natural loops, the analyzer iterates the abstract states at the
header to a fixpoint. The presence of an exit edge is a graph requirement.
Termination of the source loop requires the separate
[loop resource and termination rules](core-design.md#loans-and-control-flow).

The [analyzer](../../tools/toolchain/loans.py) computes backward
demand over the control-flow graph and performs forward abstract interpretation
with join-point state merging at join nodes and loop headers. Compatible branch
states merge when the available handles, loan routes and footprints, invariant
debts, owner availability, and relevant binder history agree. A sequence of
conditionals whose local loans end before each join therefore needs one state per
join. `Limits` bounds owners, nodes, captures, and work. Its path limit
bounds distinct states at a join and the number of terminal reports.
Exhaustion raises `AnalysisRefusalError` before publishing a result. The
[promotion contract](core-design.md#borrow-analysis-promotion) governs using
the diagnostic's findings in a checked source analysis.

## Inference and obligations

Abstract states along the control-flow graph track their own capture
environments, active/suspended loans and per-conjunct invariant debt sets,
and retain separate states when the same handle denotes different grants on
incoming edges. For equivalent states, the analyzer combines prior issue and
restoration evidence while sharing the remaining flow. Backward demand follows transitive
captures and loan ancestry; forward analysis detects competing access, use before
creation, use after move and invalid reborrows. Loan ends are inferred at last
use, with descendants ended before ancestors. Each inferred end records a
restoration obligation with its path and location. It does not prove restoration,
run cleanup, discard a tracked value or erase a required verdict.

Access through a loan requires its grant and respects overlapping descendant
suspension. Declared disjoint fields remain accessible. Unknown projections or
alias relations produce residual overlap obligations rather than permission.
A shared loan may escape as a view into a declared borrowed parameter under an
explicit return summary. That outcome retains the loan and ancestor restoration
duties, with overlapping parent access suspended. A scoped ancestor also retains
its scope restriction through moved handles, nested reborrows and wrapper
captures; returning an unscoped descendant cannot hide that restriction. Its
error sibling restores locally. Local-owner and exclusive escapes produce
diagnostics. Closure returns must include their transitive captures. Suspension and open-invariant cases
remain unsupported or unresolved; syntactic availability is no proof of safety.

Each report identifies detected conflicts, unresolved obligations, and
path-specific proposed ends and escapes. Source acceptance still requires
checked restoration, capture, effect and interpretation proofs.

## Using the diagnostic

[loans.py](../../tools/toolchain/loans.py) exposes immutable graph/event
records and `analyze(owners, graph, limits)`. Run its focused behavioral checks
with `python tools/run.py test --only test_holdfast_loans --jobs 1` on Windows
or `python3 tools/run.py test --only test_holdfast_loans --jobs 1` on Linux.
The graph below models one path that returns a view and another that writes
to its backing after the view becomes dead.

```python
from toolchain.loans import Access, Borrow, Graph, Loan, Node, Owner, Place, Return, analyze

input_place = Place("input")
report = analyze((Owner("input", borrowed=True),), Graph("lend", (
    Node("lend", Borrow(Loan("view", "input", input_place)), ("ready", "error")),
    Node("ready", Return("Ready", ("view",))),
    Node("error", Access(input_place, "write"), ("rejected",)),
    Node("rejected", Return("Rejected")),
)))
```

The `Ready` path retains the shared view and suspended parent footprint. On
`Rejected`, no later use demands the view: its proposed end precedes the write,
and its restoration remains an unresolved obligation. `PathReport` keeps those
outcomes separate. `Issue` describes a detected conflict or unsupported operation;
`Obligation` and `Restoration` retain unresolved premises. `AnalysisRefusalError`
means malformed input or incomplete exploration and returns no report.

`Use` reads through a handle's retained loans or reads an owner root. `Bind`
retains captures without accessing their contents. `Move` transfers a
descriptor's availability.
`Drop` removes availability without running resource disposal or extending a
dead loan's demand. Moving an owner root is an explicit `Access(..., "move")`;
partial owner moves remain unsupported. Array projections use `"*"` and retain
explicit overlap/containment obligations. Whether a `Graph` is constructed
directly or lowered from a schema-2 surface AST via `lower_function` /
`lower_module`, its owner and projection facts remain explicit inputs rather
than proved source semantics.

<a id="diagnostic-disposition"></a>

## Acceptance

The [loan tests](../../tools/tests/test_holdfast_loans.py) check structural refusals,
path-local demand, move and transitive capture accounting, symbolic overlap,
restoration order and returned outcomes. The
[join fixtures](../../tools/tests/test_holdfast_loans.py#_correlated_loan_origins_at_join)
exercise three alternative exclusive routes and a write that conflicts with
only one incoming footprint. An
[independent branch-demand oracle](../../tools/tests/test_holdfast_loans.py#_generated_branch_demand_oracle)
checks conflict and restoration locations while varying each branch's reads and
writes. Unsupported operations and budget exhaustion have distinct refusal cases.

## Conditional borrowing comparison

The [first-release checker](first-release.md#default-borrow-checking) uses
proof-backed separation and path-sensitive loan analysis by default. The
comparison qualifies the precision and cost claims for the supported workloads.
A comparison under [client qualification](first-release.md#qualification) freezes independently
reviewed client behavior, expected decisions and the compared guarantee
endpoints. Pin the compiler/analyzer revision and configuration, explicitly
distinguishing original Polonius from Polonius Alpha. Pin the selected
[Ante design](../extensions/interior-mutability.md#ante-as-a-candidate-for-static-invalidation)
and identify its implemented subset; a design example supplies no compiler
verdict. Supplied graph diagnostics and source checking have different endpoints.

Run `python tools/run.py holdfast-borrow-compare` with the pinned Rust nightly
installed through rustup and its host linker available. The command checks the
compiler revision, replays the default and the explicit NLL, legacy Polonius
and Polonius Alpha modes, and validates diagnostic codes and source lines. It runs
the observation tests for accepted configurations and records the fixture
digests and compiler flags. The higher-ranked callback replay also runs with the
next-generation trait solver. [Recorded comparison](../assurance/completion-log.md#q25cc-compare-borrow-checking-alternatives-on-held-out-clients)

### Nested row invalidation

The nested-row client starts with three nonempty rows. It borrows row `i`,
clears row `j` and observes the first byte of the borrowed row after the
clear. The indices must be below two and different. The observation includes
all three rows after the operation, with a third row to check the frame.
Equal or out-of-range indices leave every row unchanged and produce no byte.

On the default mathematical frontend, the `Nat` inequality justifies the
shared `in rows[i]` and exclusive `ref rows[j]` arguments to the helper. The
coincident and guard-free controls are refused at the exclusive argument.
Rocq checks the returned byte and restored vector for arbitrary row contents
and indices in the emitted model. The pinned Rust modes and Ante reject the
direct and coincident forms. Rust's `split_at_mut` rewrite and Ante's
separate named row owners pass the 16 observation pairs. The HoldFast result
ends at the mathematical model. [HoldFast fixture](../../tools/tests/fixtures/nested-indexed-invalidation.hf) ·
[Rocq replay](../../tools/tests/test_holdfast_borrow_comparison.py) ·
[Rust fixture](../../tools/tests/fixtures/nested_indexed_invalidation.rs) ·
[Ante direct fixture](../../tools/tests/fixtures/nested_indexed_invalidation.an) ·
[Ante rewrite](../../tools/tests/fixtures/nested_indexed_invalidation_rewrite.an)

On the default mathematical frontend, local element borrows (`let x = in coll[i];`
and `let x = ref coll[i];`) over `Vec<T, n>`, `Seq<T>`, `Span<byte>`, and
`Slots<T, capacity>` are also checked directly without helper-call workarounds.
At each later read or write of a bound element borrow, the elaborator checks that
reachable owner updates preserve the element index and that any conflicting peer
borrows created afterwards on the current or joined control-flow paths have proved
index separation.
[Direct indexed fixture](../../tools/tests/fixtures/direct-indexed-borrows.hf) ·
[Direct indexed replay](../../tools/tests/test_holdfast_borrow_comparison.py)

On a lane with Cargo and a C compiler, add `--ante-checkout CHECKOUT` to the
comparison command. It verifies the pinned checkout and submodule,
builds the compiler from an isolated copy with its lockfile and C backend,
checks both invalidation diagnostics at the live read and executes the
accepted rewrite. Run
`python3 tools/run.py test --only holdfast_borrow_comparison --require-toolchain`
on the guest for the HoldFast verdict and kernel replay.
[Ante prerequisite](../../tools/README.md#ante-borrow-comparison)

### Branch-local view use

A shared one-byte slice of `values[i]` is created before a branch. On one
path the caller reads through the slice, overwrites `values[i]` and returns
the saved byte. On the other path the guard `i != 0` proves that the write to
`values[0]` preserves the slice before the caller reads it. When `i == 0`
on that path the caller skips the write. The default mathematical frontend
checks the reachable owner write history at each read. Using the view after
the first path's overwrite or changing the second write to `values[i]` is
refused at the affected read.
[HoldFast fixture](../../tools/tests/fixtures/branch-view-last-use.hf) ·
[Checked replay](../../tools/tests/test_holdfast_loan_returns.py#_branch_view_last_use)

The four pinned Rust modes reject the direct spelling at the disjoint write
and reject both overlapping controls. The safe rewrite splits at `i` on the
path where the view remains live. It uses `split_at_mut`'s usual bounds
check and passes the shared returned-byte, writeback and frame observations
for all 16 tested inputs.
[Rust fixture](../../tools/tests/fixtures/view_last_use.rs)

### Lending filtering loops with borrowed returns

A returning range loop (`foreach (let i in 0usize..len)`) can break early with
`return Ok(...)` yielding a read-only `Span<byte>` slice borrowed from the
mutated `ref Span<byte>` owner, while marking skipped elements along the
continue path. The mathematical elaborator checks loop entry and inductive
invariants, verifies slice disjointness against any writes within the returning
branch, folds state across `NatFold` with a `Unit + R` return-freeze sum, and
joins early-returned values and writebacks with the fallthrough exit.
[Lending filter source](../../tools/tests/fixtures/lending-filter-return.hf) ·
[Lending filter replay](../../tools/tests/test_holdfast_loan_returns.py#_lending_filter_return)

### Symbolic Span separation

The mathematical frontend checks same-collection indexed call args using scoped arithmetic: exclusive+other indexed args require proved index separation, and distinct slice views require separation in common owner coordinates. Ordered shared/exclusive (`i < j && j < 4`) permits reading `i` while writing `j`; Rocq verifies returned value, writeback, frame, and unchanged failure in `Span<byte>`, while pinned Rust modes reject the direct call and coincident neighbor and pass `split_at_mut`. [HoldFast replay](../../tools/tests/test_holdfast_loans.py#_mixed_indexed_loans) · [Rust fixture](../../tools/tests/fixtures/mixed_indexed_loans.rs)

For `view[i]` (`Span.Slice`) beside `owner[j]`, the checker shifts `i` by slice offsets before separation (`Span.ReadOnly` preserves offset/extent; two offset-1 slices require `j != 2usize + i`). Pre-write/pre-fill slices must survive on every reachable branch; pending mutable arg updates leave separation unresolved. Rocq verifies single/nested slices, read-only wrappers, and pre-call index-0 writes. [Owner-coordinate replay](../../tools/tests/test_holdfast_loans.py#_owner_coordinate_indexed_loans)

Conditional slice selection before owner joins verifies readability, bounds, and owner coordinates on every path before permitting shared+exclusive calls. [Correlated indexed call replay](../../tools/tests/test_holdfast_loans.py#_correlated_indexed_loans)

Conditional-return checks verify returned slices against `ref Span<byte>` on return paths (intervening writes need out-of-slice evidence; error branches restore). [Source and replay](../../tools/tests/test_holdfast_loan_returns.py#_conditional_view_return)

Joined owner updates check every branch write history (`values[i]` survives index-1 write when `i == 0` and index-0 write when `i != 0`; index-`i` writes fail). Rocq checks value, writeback, and frame; pinned Rust rejects direct source and passes runtime `get_disjoint_mut`. [HoldFast replay](../../tools/tests/test_holdfast_loan_returns.py#_joined_view_return) · [Rust fixture](../../tools/tests/fixtures/joined_view_return.rs)

Conditional slice selection (`0` surviving write at `1` on true, `1` surviving write at `0` on false) checks each descriptor under branch facts (overlapping writes or independent conditions fail); pinned Rust rejects direct source and passes branch-local view creation. [Correlated return replay](../../tools/tests/test_holdfast_loan_returns.py#_correlated_view_return) · [Rust fixture](../../tools/tests/fixtures/correlated_view_return.rs)

Symbolic range loops keep a shared view at index 3 while writing 9 across `[0, n)`: `n <= 3` proves disjointness, whereas `n <= 4` fails at return (`Span.Fill` uses the same half-open rule, incl. empty and view-adjacent fills); Rocq checks original/updated bytes and unchanged error state. [HoldFast source](../../tools/tests/fixtures/loop-view-return.hf) · [Kernel replay](../../tools/tests/test_holdfast_loan_returns.py#_loop_view_return)

`foreach (ref byte element in values)` over symbolic-length `Span<byte>` lends elements in order and restores on writeback; terminal/unconditional `break` writes back the breaking element, freezes later iterations, checks both invariants, and restores (competing accesses, non-terminal `break`, and retained views fail). [Lending source and replay](../../tools/tests/test_holdfast_loan_returns.py#_lending_span_iteration) · [Early break replay](../../tools/tests/test_holdfast_loan_returns.py#_lending_span_break)

The mathematical elaborator (`tools/toolchain/elaborate_*.py`, incl. `elaborate_borrows.py`), region solver ([`regions.py`](../../tools/toolchain/regions.py)), and CFG analyzer ([`loans.py`](../../tools/toolchain/loans.py)) also handle:

- Polonius-style location-sensitive origin, subset, variance (`in` covariant, `ref`/`shared ref` invariant), `Outlives<'a, 'b>`, multi-region disambiguation (`'a` vs `'b`), `FnMut`/`FnOnce` HRTBs, and generalized outer-capture blocking;
- exclusive `ref<'a>` conditional/loop returns with prophecy/lens restoration across multi-branch and `while`/`foreach`/`match`, GAT `LendingIterator` interfaces/`impl`s, arbitrary-depth nested field reborrows, partial field moves with re-init, and loop-carried mutable cursor reborrowing;
- safe `shared ref` aliased mutation over shape-stable scalars, fields, and fixed-extent elements (plus `LocalCell`/`BorrowCell` store-threaded models) purging overlapping `active_facts` while keeping disjoint refinements, proof-backed tag-preserving union mutation (`tag(new) == tag(old)`), and `Slots.Push` (`LiveCount < capacity`);
- container stability (`unstable` `Seq`/`Slots` mutations vs stable element writes), symbolic `requires`/`assert` index-disjointness (`AssumeIndexNe`), path-sensitive `if`/`else` disequalities, `PathSensitiveRowClear`, and `ProvedFacts` / `path.obligations` / `check_loan_certificate` across elaborator, CFG analyzer, and [zero-axiom Rocq loan soundness proofs](../../tools/rocq/loan_soundness.v);
- disjoint sub-slice writebacks (`holdfast_bs_shift_onto`), field and 2D-grid borrows under `r1 != r2 || c1 != c2`, two-phase receiver reservations, and 3-span conflict diagnostics (`origin`, `conflict`, `live_use`/`proposed_end`);
- paired Rust (`rustc +nightly-2026-11-20`) and Ante (`ante_borrow_compare.py`, `.rs`/`.an` fixtures, `holdfast-borrow-compare`) trials across 22 `comparison_matrix` cases (HoldFast accepting all 22 vs 3 Rust NLL, 7 Rust Polonius Legacy, 6 Rust Polonius Alpha, 3 expected Ante).

[Subslice writeback replay](../../tools/tests/test_holdfast_loan_returns.py#_subslice_disjoint_writeback) · [Field and 2D borrows](../../tools/tests/test_holdfast_loan_returns.py#_field_and_multidim_borrows) · [Loop cursor reborrow](../../tools/tests/test_holdfast_loan_returns.py#_loop_cursor_reborrow) · [Higher-ranked view callback](../../tools/tests/test_holdfast_loan_returns.py#_higher_ranked_view_callback) · [Two-phase receiver replay](../../tools/tests/test_holdfast_loan_returns.py#_two_phase_receiver_replay) · [Exclusive ref returns](../../tools/tests/test_holdfast_loan_returns.py#_exclusive_conditional_return_and_prophecy) · [GAT LendingIterator and FnMut](../../tools/tests/test_holdfast_loan_returns.py#_lending_iterator_gat_and_hrtb) · [Shared ref and proof-backed updates](../../tools/tests/test_holdfast_loan_returns.py#_shared_mut_and_ante_beat_proofs) · [Partial moves and loop cursors](../../tools/tests/test_holdfast_loan_returns.py#_partial_field_move_and_loop_cursor) · [Loan certificate replay](../../tools/tests/test_holdfast_loan_returns.py#_loan_certificate_rocq_soundness_replay) · [Rocq soundness audit](../../tools/tests/test_holdfast_loan_soundness.py) · [Borrow comparison suite](../../tools/tests/test_holdfast_borrow_comparison.py#_comparison_fixture_contracts)

For loop restructuring comparisons, keep the original loop and move one use past the write for the conflicting case (freezing place, last use, and expected restoration per path). Two 2026 analyses are candidate comparators:

- MoveLight regex path summaries ([OOPSLA 2026](https://2026.splashcon.org/details/oopsla-2026/147/Tracking-Borrows-with-Regular-Expressions) · [Lean artifact](https://zenodo.org/records/21850968)): test whether structured-path summaries separate the two live ranges.
- Wu, Wang, and Chen forward Polonius abstract interpretation ([Nov 2026 preprint](https://arxiv.org/abs/2611.06319v1)): compare write-site alias decisions on the common fragment and record preserved places/CFG edges.

Record unexpressible features (e.g., HoldFast-specific resource exits), replay exit restorations, and benchmark against the same budgets. Separate loan reasoning from generic resolution across:

| Client | Required distinction |
| --- | --- |
| Returned view on one branch, owner updated on its sibling | Update after view's last use succeeds; update before view use conflicts. |
| Iterator lending a mutable element from its receiver | Next iteration proceeds after prior loan ends; overlapping element loans conflict. |
| Generic callback valid for each fresh input lifetime | Noncapturing identity view returns input loan; storing view in longer-lived state violates callback contract. |
| Generic iterator with an associated item | Resolve item equality via independently imported instance, report genuine ambiguity, and preserve both outcomes under import reordering. |

Pin Rust edition, revision, flags, and crate closure (keeping ordinary receiver rules, Polonius modes for loans, and next-gen trait solver for generics), recording extra proofs, annotations, `unsafe`, runtime checks, and rewrites ([Rust two-phase](https://rustc-dev-guide.rust-lang.org/borrow-check/two-phase-borrows.html), [Rust trait solving](https://rustc-dev-guide.rust-lang.org/solve/trait-solving.html)). Report accepted, semantically rejected, unsupported, and incomplete cases separately (conflict-free diagnostics with open obligations give no acceptance; parse/type failures give no borrowing rejection); count a precision gain only when HoldFast accepts a matched positive that the baseline rejects on borrowing grounds while replaying guarantees and rejecting conflicts. Use [measurement/sampling](../assurance/workflow-contract.md#measurement-record-and-sampling) alongside graph size, branching, captures, budgets, and budget refusals, scoping claims to tested workloads and endpoints.

<a id="two-phase-receiver-trial"></a>

### Two-phase receiver qualification

[Release qualification](../../PLAN.md#q25cd) checks the
[two-phase receiver rule](core-design.md#two-phase-receiver-borrows) with
`buf.Update(buf.ReadCount())` on a whole-object receiver and a by-value count.
Compare traces with a count snapshot where the earlier read observes the same
state. Include a computed receiver, an effectful argument before the read, and
a failure before activation after an earlier ownership transfer. Check that the
receiver and each reached argument are evaluated once in source order, and
replay the resource predicate on each exit.

Use neighboring calls with an overlapping mutation or move during argument
evaluation, a shared argument or capture live at activation, and an explicit
`ref` argument followed by an overlapping read. Each fails at its responsible
permission check. The corresponding disjoint named-view case succeeds even
when the shared loan is retained. Promotion requires source correspondence and
the [core borrow obligations](core-design.md#borrow-analysis-promotion).
