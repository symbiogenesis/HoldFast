# HoldFast loan-analysis diagnostic

The loan diagnostic proposes loan ends and reports conflicts and unresolved
obligations over explicit flow facts. The
[core promotion contract](core-design.md#borrow-analysis-promotion) specifies the
additional checks needed for source acceptance.

## Input and composition

The Python API consumes an explicit finite control-flow graph with named
owners, declared field projections, named invariant clauses, shared/exclusive
loans and parent links, and also provides a schema-2 surface AST lowering pass
(`lower_function`, `lower_module`, `analyze_function`, `analyze_module`).
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

Names must be unambiguous within a path. A child loan must stay within its parent
footprint; a shared parent cannot produce an exclusive child. Missing references,
duplicate graph identities, malformed edges, irreducible or non-terminating
cycles and exhausted node/path/work budgets refuse analysis. No partial
exploration may produce a complete result. Reducible natural loops with an exit
edge are analyzed by Kleene fixpoint iteration over the loop header.

The [analyzer](../../tools/toolchain/loans.py) computes backward
demand over the control-flow graph and performs forward abstract interpretation
with join-point state merging at join nodes and loop headers. Compatible branch
states merge when the available handles, loan routes and footprints, invariant
debts, owner availability, and relevant binder history agree. A sequence of
conditionals whose local loans end before each join therefore needs one state per
join. `Limits` bounds nodes, distinct states per join, terminal reports, captures,
and work. Exhaustion refuses the complete analysis without
returning partial success. This diagnostic establishes neither production
scalability nor a choice of production algorithm; the
[promotion contract](core-design.md#borrow-analysis-promotion) retains that decision.

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

The result distinguishes structural refusal, detected conflicts, unresolved
obligations and path-specific proposed ends/escapes. A graph with no detected
conflict still needs every restoration, capture, effect and interpretation proof.
The API must not expose an admitted-program or memory-safe verdict.

## Using the diagnostic

[loans.py](../../tools/toolchain/loans.py) exposes immutable graph/event
records and `analyze(owners, graph, limits)`. Run its focused behavioral checks
with `python tools/run.py test --only test_holdfast_loans --jobs 1` on Windows.
An explicit result split can be modeled as follows:

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

`Use` means reading through a handle's retained loans. `Bind` retains captures
without accessing their contents; `Move` transfers a descriptor's availability.
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
the observation tests for accepted configurations and emits the results with
their fixture digests. [Recorded comparison](../assurance/completion-log.md#q25cc-compare-borrow-checking-alternatives-on-held-out-clients)

The mathematical frontend checks same-collection indexed call arguments using
scoped arithmetic facts. When an exclusive argument and another indexed
argument share a collection, the frontend must establish that their indices
differ. This covers exclusive pairs and shared/exclusive pairs. Distinct
slice views of the same owner require separation in a common coordinate system
before their relative indices can justify distinctness. In the ordered
shared/exclusive trial, `i < j && j < 4` permits reading element `i` while
writing back element `j`. The Rocq replay checks the returned value, the
writeback, the frame and the unchanged failure state in the emitted
`Span<byte>` model. The direct Rust call and coincident neighbor fail in the
pinned modes, while the `split_at_mut` spelling passes the observations.
[HoldFast replay](../../tools/tests/test_holdfast_loans.py#_mixed_indexed_loans) ·
[Rust fixture](../../tools/tests/fixtures/mixed_indexed_loans.rs)

The frontend also checks a shared element loan from a named `Span.Slice`
and an exclusive element loan directly from its owner. The slice must derive
from the current owner term, and argument evaluation must complete without
pending mutable updates. The checker adds the slice offset to the shared
index before applying the scoped separation facts. At offset one,
`j != 1usize + i` separates the loans and `j != i` leaves their separation
unproved. A nested slice retains its backing identity and leaves a same-owner
cross-view overlap unresolved. The Rocq replay checks the returned byte,
owner writeback, framed elements and untouched failure state.
[Owner-coordinate replay](../../tools/tests/test_holdfast_loans.py#_owner_coordinate_indexed_loans)

If a client must restructure a loop whose last use of a view precedes a write
to its owner, keep the original loop. Move one use past that write to produce
the conflicting case. Freeze the accessed place, last use and expected
restoration point on each path.
Two 2026 results supply candidate analyses for the parts their models cover.

- MoveLight uses regular expressions to summarize paths rooted in local
  variables across calls and loops. For a structured path, check whether its
  summary preserves the distinction between the two live ranges.
  [OOPSLA paper](https://2026.splashcon.org/details/oopsla-2026/147/Tracking-Borrows-with-Regular-Expressions) · [Lean artifact](https://zenodo.org/records/21850968)
- Wu, Wang and Chen verify a forward abstract interpretation of Polonius for a
  Rust core. On the common fragment, compare its alias decision at the write
  with HoldFast's. Record which source places and control-flow edges the translation
  preserves. [November 2026 preprint](https://arxiv.org/abs/2611.06319v1)

Record any feature a model cannot express, such as an exit that returns a
HoldFast-specific resource. To qualify an analysis for HoldFast, replay its restoration
obligations on each exit and measure its work against the same budgets.

In the comparison, distinguish reasoning about loans from resolving generic
interfaces. Exercise the following source clients with their corresponding
invalid edits and record the first obligation each compiler can judge.

| Client | Required distinction |
| --- | --- |
| Returned view on one branch, owner updated on its sibling | The update after the view's last use is safe. An update followed by use of the same view conflicts. |
| Iterator lending a mutable element from its receiver | The next iteration can proceed after the first loan ends. Holding the first element through a second overlapping loan conflicts. |
| Generic callback valid for each fresh input lifetime | A noncapturing identity view returns the loan tied to its input. Storing that view in longer-lived state violates the callback contract. |
| Generic iterator with an associated item | Resolve the required item equality through an independently imported instance, report a genuinely ambiguous selection and check that reordering imports preserves both outcomes. |

Pin the Rust edition, compiler revision, flags and crate closure separately for
each run. Keep ordinary Rust receiver behavior in the baseline. Compare
Polonius configurations for the loan cases and the next-generation trait solver
for the generic obligations it judges. Record extra proof terms, annotations,
unsafe abstractions, runtime checks and source rewrites for each tool.
[Rust two-phase borrows](https://rustc-dev-guide.rust-lang.org/borrow-check/two-phase-borrows.html)
and [Rust trait solving](https://rustc-dev-guide.rust-lang.org/solve/trait-solving.html)
describe the respective subjects.

Record accepted, semantically rejected, unsupported and incomplete cases
separately. A diagnostic with no detected conflict still carries its unresolved
proof obligations and supplies no source acceptance. Compare matching behavior
without weakening ownership, dependent facts, effects or required guarantees.
Retain manual rewrites, annotations and the first intended diagnostic; an
unrelated parse/type failure supplies no borrowing rejection evidence.

Reuse the applicable [measurement record and sampling](../assurance/workflow-contract.md#measurement-record-and-sampling)
for diagnostic latency, elapsed/CPU time, peak memory and environment identity.
Record graph size, branching, captures, configured budgets and budget refusals
alongside successful cases. State each claimed improvement's objective and
supported workload, including regressions and endpoint differences. Report conclusions for the tested workloads and evidence endpoints.

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
