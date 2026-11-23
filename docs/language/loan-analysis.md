# Vela loan-analysis diagnostic

The loan diagnostic proposes loan ends and reports conflicts and unresolved
obligations over explicit flow facts. The
[core promotion contract](core-design.md#borrow-analysis-promotion) specifies the
additional checks needed for source acceptance.

## Input and composition

The Python API consumes an explicit finite control-flow graph with named
owners, declared field projections, named invariant clauses, shared/exclusive
loans and parent links, and also provides a schema-2 surface AST lowering pass
(`lower_function`, `lower_module`, `analyze_function`, `analyze_module`).
Events describe borrowing, access, resource moves, binding capture environments,
uses, per-conjunct invariant opening and closing (`open ... lifts`),
outcome-specific returns and unsupported suspension boundaries. Each
operation's facts are explicit inputs: a library call does not obtain authority
from its name. Boxes, optional values, cells, callbacks and protocol wrappers use
the same capture and loan facts, without dedicated cases for their type names.
Owner identities and field partitions are supplied abstract facts, not inferred
from source spelling or pointer inequality. Unknown overlap produces an unresolved obligation.

A receiver loan starts before argument evaluation under the
[first-release call rule](first-release.md#ownership-libraries). In `buf.Update(buf.length)`,
a whole-buffer exclusive receiver conflicts with the `length` read. Saving
`let n = buf.length;` before the call removes the overlap. A receiver restricted
to the `payload` field permits the `length` read. Single-field receiver views
identify a footprint. Compound and indexed views conservatively cover the whole
receiver. [Receiver timing fixtures](../../tools/tests/test_vela_loans.py#_located_receiver_timing)

Names must be unambiguous within a path. A child loan must stay within its parent
footprint; a shared parent cannot produce an exclusive child. Missing references,
duplicate graph identities, malformed edges, irreducible or non-terminating
cycles and exhausted node/path/work budgets refuse analysis. No partial
exploration may produce a complete result. Reducible natural loops with an exit
edge are analyzed by Kleene fixpoint iteration over the loop header.

The [analyzer](../../tools/toolchain/loans.py) computes backward
demand over the control-flow graph and performs forward abstract interpretation
with join-point state merging at join nodes and loop headers. Compatible branch
states merge at join points rather than enumerating $2^k$ paths across sequential
conditionals. `Limits` owns the bounded node,
path, capture and work budgets. Exhaustion refuses the complete analysis without
returning partial success. This diagnostic establishes neither production
scalability nor a choice of production algorithm; the
[promotion contract](core-design.md#borrow-analysis-promotion) retains that decision.

## Inference and obligations

Abstract states along the control-flow graph track their own capture
environments, active/suspended loans and per-conjunct invariant debt sets,
merging compatible states at join points and loop headers without unioning
mutually exclusive branch loans into a single unconditional grant. Backward demand follows transitive
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
with `python tools/run.py test --only test_vela_loans --jobs 1` on Windows.
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

The [loan tests](../../tools/tests/test_vela_loans.py) check structural refusals,
path-local demand, move and transitive capture accounting, symbolic overlap,
restoration order and returned outcomes. An
[independent branch-demand oracle](../../tools/tests/test_vela_loans.py#_generated_branch_demand_oracle)
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
  with Vela's. Record which source places and control-flow edges the translation
  preserves. [November 2026 preprint](https://arxiv.org/abs/2611.06319v1)

Record any feature a model cannot express, such as an exit that returns a
Vela-specific resource. To qualify an analysis for Vela, replay its restoration
obligations on each exit and measure its work against the same budgets.

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
