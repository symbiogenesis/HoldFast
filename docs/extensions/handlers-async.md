# Handlers and structured async lifecycle rules

> Design for effect handlers and structured async beyond the
> [first-release subset](../language/first-release.md#release-boundary).

## Boundary and shared resource interface

First release is synchronous. Structured async is a later extension commissioned for a named service after synchronous-component and independent-client gates; its first qualification uses sequential helpers and one structured child (no handler or shared mutable cell required). Handlers begin with deep one-shot continuations (including explicit zero-resumption disposal); runtime multi-shot and shallow rehandling remain deferred research directions whose rules apply only when separately commissioned after showing material benefit over bounded control flow.

Async computations own dormant state, compose sequentially, or spawn structured children, realized in VerifiedOS as a finite reaction graph with explicit cleanup and syntactic poll sites. Lowering must prove R-05-100 (no exceptions, unwinding, `longjmp`), R-07-037a (no blocking, internal threads, or inner scheduler), and R-11-006 (schedule obligation); effects confer no ambient authority or dynamic graph changes.

### Interpretation commitment

`Interpret(e)` is the selected anchor computation with checked source correspondence; ownership/frame predicates live in the chosen resource logic, quantifying capture, substitution, return, erasure, and progress laws. [Frontend admission](full-language-review.md#frontend-admission)

The [graded foundation](graded-foundation.md#resource-and-computation-interface) owns stable telescope `Gamma`, use vectors `u`/`v`, dependency rows, and resource context `Delta`. `Capture`, `Dup`, `Dispose`, `Suspend`, `Transfer`, and `Share` require resource-logic laws (grade constraints alone give no memory predicate or ownership token):

```text
Gamma ; u ; v ; Delta_in |- e : Exit(A, Delta_out)
  [captures C, loans L, effects E, source trace bound B, representation rho]

Capture(e, Delta_k, C, L, rho_k)
  records every transitively retained resource and its exit duties
Dup(Delta_k, rho_k)
  permits a represented clone and a separating resource interpretation
Dispose(Delta_k, reason, Delta_disposed)
  accounts for cleanup, erasure, terminal protocols and examined verdicts
Suspend(Delta_k, frame, lifetime, Delta_resumed)
  preserves stable storage, closed invariants and restoration at activation
```

`Delta_in = Delta_run * Delta_k * Delta_frame` is a proved separating split (including suspended parent permissions and restoration debts); a loan name in `Gamma` grants no access without its `Delta` permission. `Dup` checks nested closures, handlers, and stored continuations transitively; repeated invocations require fresh separated `Delta_i`, and idempotent grades never duplicate owners. Operation contracts supply source event counts separately from use grades and target WCET.

Effectful arguments sequence explicitly by value (`bind x <- c; call f(x)` evaluates `c` once with its trace and resource transition; zero use does not erase effects, repeated use does not reevaluate, governed by pure scaling + open CBV bridge; multi-resumption repeats only the captured continuation under its contract).

The [synchronous core](../language/core-design.md#loans-and-control-flow) embeds without capture or suspended frames, retaining ordinary returns, resource-indexed errors, and loan restoration (fallible cleanup and suspended loans need extra laws):

| Source | Result and transfer limit |
| --- | --- |
| [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383v2), POPL 2024 | Relates continuation use to linear resources and exposes the soundness bug; pen-and-paper proofs, GPL-3.0-or-later Links fork, unmechanized. |
| [Affect](https://iris-project.org/pdfs/2025-popl-affect.pdf), POPL 2025 | Iris/Rocq semantic soundness over Hazel separating one-shot/multi-shot continuations (including mutable-ref storage); no verified checker/inference. |

The [strategy](../assurance/verification-strategy.md#effect-handlers-sharing-and-protocol-logics) surveys relational, stack-switching, sharing, and disposal logics; none proves this graded dependent CHERI combination or models preassigned immovable frames.

## Handler lookup, capture and return

Effect signatures declare represented argument/reply types, effect permission, input/output resources, and resumption allowance. One-shot handlers supply a finite deep operation table, environment representation, operation/return/disposal clauses, and result/resource transform (shallow mode and multi-shot belong to the deferred research extension). Binding introduces an instance capability; effect contracts list usable capabilities and effect polymorphism quantifies over them; specialization fixes tables, layouts, and bounds. Residual operations require caller-supplied capabilities or injected primitives (unhandled composed-entry operations fail as unresolved obligations, never default services or runtime traps).

Capabilities resolve to preassigned frame slots/incarnations ([frame representation](#frames-child-ownership-and-reaction-execution)); deferred cloning/rehandling stores body-internal references frame-relatively. Operations name a capability explicitly or pick the nearest lexical binding ([Zhang and Myers](https://doi.org/10.1145/3290318), POPL 2019; effect-contract params count as lexical), never searching dynamically. `E` spans the hole and all intervening frames/handlers up to the target handler without running their clauses/cleanup on capture (restored on resume); the chosen clause runs outside `E` and its handler using its lexical environment.

A handler capability is a shared duplicable loan authorizing `perform` only (capture authority comes from the running context), lexically scoped like Effekt and [System C](https://doi.org/10.1145/3527320) (OOPSLA 2022):

- Type operation, return, and disposal clauses without the handler's own or body-bound capabilities.
- Type `spawn` dormant computations with no handler capability in scope (children install own handlers; no continuation segment crosses to an outer handler).
- Track retained capabilities transitively: use requires every capture in scope (including closures read through cells), and operation argument/reply types cannot carry body-bound capabilities (matching Effekt's [capture discipline](https://effekt-lang.org/tour/captures)).
- Operation arguments may lend the clause part of the body's frames (resolved against `k`'s invocation frame), ending before `resume`, clone, rehandle, or `dispose` (neither `Dup`, rehandle, nor reply retains it).

Effect-polymorphic handlers cannot intercept operations performed through capability parameters—blocking accidental handling, preserving parametricity, enforcing [object-capability R-04-003](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-04-003), and permitting $O(1)$ slot lookup independent of nesting. Simulation is still required against Affect/Hazel's first-matching-handler semantics; named/lexical precedents cover different theorems:

| Source | Checked result |
| --- | --- |
| Zhang and Myers | Coq parametricity and logical-relation soundness for contextual refinement (closed label types/effects). |
| [Biernacki, Piróg, Polesiuk and Sieczkowski](https://doi.org/10.1145/3371116), POPL 2020 | Coq lexically scoped instances, open/generative semantics, and logical relations. |
| System C | Coq progress and preservation for second-class capabilities and boxes. |
| [De Vilhena and Pottier](https://doi.org/10.1007/978-3-031-30044-8_9), ESOP 2023 | Coq type soundness encoded into Iris separation logic (supports lexical handlers without requiring them). |
| [Handling Higher-Order Effectful Operations](https://doi.org/10.1145/3776678), POPL 2026 | Judgmental monadic laws for scoped and higher-order effectful operations (Yang & Wu). |
| [HMCFA](https://doi.org/10.1145/3828703), ICFP 2026 | Big-step control-flow analysis for bounding handler dispatch and specialization tables (Whiting & Germane). |

None supplies Affect's one-shot/multi-shot resource separation for capability-directed lookup (open law), while HoldFast keeps its lexical capability discipline and specialization proofs unchanged.

```text
Interpret(handle_deep E[perform op(a)] with H)
  ~= Interpret(H.op(a, k)), with resume k(b) interpreted as handle_deep E[b] with H

Deferred shallow extension:
Interpret(handle_shallow E[perform op(a)] with H)
  ~= Interpret(H.op(a, k)), with rehandle k(b) with H' interpreted as E[b]
     handled by H' at k's invocation frame, for H' of H's effect signature
```

`~=` denotes the checked anchor behavior/resource relation (never a source reduction axiom). Deep resumption reinstalls `H` and evaluates `H.return` once per completed resumption. Deferred shallow capture moves `H`'s environment into the clause leaving a delimiter hole; `resume` is permitted only inside a same-signature `rehandle` at `k`'s invocation frame (fresh incarnation or clone frame), where specialization fixes a finite rehandler set for $O(1)$ dispatch and the rehandler's `return` clause receives raw body results/resources (ordinary completion runs `H.return` once; Effekt, [Lexa](https://doi.org/10.1145/3689770) OOPSLA 2024, and System C offer deep handlers only).

| Rule | Required state and resulting obligation |
| --- | --- |
| Enter handler | Split exclusive env from body; bind declared frame + shared `perform` capability scoped to body; establish stable ref/lifetime laws (deferred clone/rehandle stores body-internal refs delimiter-relatively). Type clauses under lexical rules; check all exits against result transform. Sharing an immutable descriptor still needs permission. |
| Capture | Move `Delta_k`, transitive loan/authority graph, and exit duties (including intervening frames/capabilities) into `k` (clause loses them). Enforce represented extents/lifetimes with no dangling stack refs. One-shot keeps stable frames; deferred clone/rehandle preserves frame-relative refs and rejects absolute refs into the copied segment. `Suspend` preserves premises across gaps. |
| Perform past intervening handlers | Reach named outer frame directly; capture intervening `E` frames unexecuted and restore them on resume. |
| Explicit forward from a clause | Move `k` once into an adapter composing outer replies with `k` and performing via a supplied outer capability; retain no alias/reset allowance; compose both capture/disposal duties. |
| Resume once | Consume one-shot authority, transfer `Delta_k` + reply resources to resumed graph, return indexed result (errors still consume the descriptor). |
| Resume multiple times (deferred) | Require transitive `Dup` (including reinstated handler envs). Assign live clones distinct preassigned invocation frames + fresh incarnations; copy templates without rewriting relative refs; check fresh `Delta_i`, all exits, and finite resumption bound (sequential reuse waits for release; shared mutable handles need [interference laws](interior-mutability.md); descriptor copies grant no mutation). |
| Rehandle a shallow continuation (deferred) | Fill `k`'s hole at its invocation frame with a same-signature handler from its specialized finite rehandler set (fresh incarnation of vacated slot or clone frame) under one-shot/multi-shot premises; refuse shallow resume outside `rehandle`. |
| Dispose without resumption | Run declared bounded disposal graph: end descendant loans, erase must-erase contents, eliminate mandatory verdicts, request cancellation, join in-flight ops (may suspend under `Suspend`; waiting never frees the frame). |
| Leave handler | Consume, dispose, or transfer every continuation with its lifetime/exit contract while retaining needed env; no result outside a transferred segment retains the handler capability, and inside it reaches only the reinstated live handler. |

Result types/resources may change across branches only if they entail a common predicate or return a represented indexed sum (disposed vs resumed-loan packets cannot join as writable owners). Disposal follows its own bounded graph under the same judgment. Specialization/loop derivations bound nesting, forwarding, and resumptions (recursive forwarding needs a decreasing bound); capture either binds complete capacity or returns uncaptured resources via `CapacityExhausted(pool)` (without that branch, capacity must be proved; partial moves forbidden).

## Frames, child ownership and reaction execution

Live frames occupy preassigned immovable slots holding finite PC state, incarnation, represented environment, handler links, child membership, cancellation latch, bounded mask state, and indexed result slot. Validity restricts reads to initialized variant fields; erasure removes proof obligations while preserving executable bases, extents, tags, and identities. Checked incarnation exhaustion detects stale handles without kernel epochs.

Slots start at incarnation 0, increment per activation, retain their last identity on release, and retire upon reaching max representable incarnation: allocating from a pool with free storage but exhausted incarnations returns `IncarnationExhausted(pool)` with the unchanged dormant computation and input owners (distinguishing permanent retirement from temporary occupancy; restarting a namespace needs a new pool identity or proof all prior capabilities/completions retired).

Scopes/continuations own frames; dropping a handle does not detach scope membership. Outside segments, refs name slot + live incarnation under `Suspend` and cannot outlive moving/retiring storage. Handler links are `perform` capabilities, not search positions; returning a frame view transfers a pin/loan until ended (APIs may instead return owners/copies). Inter-core transport needs `Transfer`/`Share`, composition grants, and a publication theorem.

One-shot capture transfers existing frame ownership once under `Suspend` without clone templates or shallow holes. For the deferred cloning/rehandling candidate only: delimiter-to-running frames form a capture segment whose internal refs (including nested handler capabilities and deep delimiters) are delimiter-relative from entry; `Dup` copies the template into a fresh clone frame without rewriting, resolving slot+incarnation through that frame's capability (shallow delimiters use the rehandler hole; specialization fixes nesting bounds and base capabilities; absolute refs may target only external storage under its permission, failing `Capture`/`Suspend`/`Dup` if pointing inside). Stack-address systems require heavier machinery: Lexa aborts multi-shot resumptions containing handlers and allows one uncopied segment ([Virtualizing Continuations](https://cs.uwaterloo.ca/~yizhou/papers/multilexa-pldi2026.pdf)), while [the strategy](../assurance/verification-strategy.md#general-handlers-with-resource-safe-resumptions) notes Effekt's active-copy global and Virtualizing Continuations' software MMU.

Task PC states refine R-08-046's frame-pool lifecycle, while [IDL profile](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/idl-profile.md#43-the-ring-schema-and-its-lifecycle) and [RingContract.v](https://github.com/symbiogenesis/VerifiedOS/blob/main/proofs/RingContract.v) own request-slot states and terminal statuses (task completion, ring reclamation, and reader release remain distinct).

| Source event | Frame and scope transition |
| --- | --- |
| Construct async computation | Move captures into a dormant owned value in declared storage with no body effects (disposing unspawned requires `Dispose`; storage must fit plan). |
| Directly await a dormant computation | Consume once into a bounded sequential subgraph ([sequential rules](#sequential-async-composition)) using declared nested storage; no child registration or completion record created. |
| Scoped spawn | Transactionally bind frame + completion slot and transfer dormant value to child slot, reading scope's latched cancel bit (if set, register already marked); execution starts only at admitted activation. Failure returns unchanged dormant value + capacity verdict with no registration. Only the scope owner's graph has a registration edge (scope handles do not pass to children; cleanup registers none). |
| Run activation | Execute declared finite CFG branch for frame state within compartment reaction (proved bounded control flow; no ready queue). |
| Await checkpoint | Require closed invariants + released default dynamic guards, check suspension/restoration premises, observe sticky cancel bit and deadline (elaboration inserts only separately proved close/release ops before this edge). Runs even when ready (semantic checkpoint, not mandatory OS dispatch). |
| Await ready | Match result at checkpoint and take declared successor (same bounded reaction if admitted). Enclosing cancellation routes through cleanup while still accounting for any produced result. |
| Await pending | Save continuation PC + retained resources and return at syntactic poll site; later activations recheck authoritative state in declared order (coalesced notifications are hints; ring index/recheck still required). |
| Child reaches terminal | Store result/resources in reserved completion record; keep scope membership until collection (local result never hides unexamined service completion; R-12-093 / R-12-100 govern service publication). |
| Join child | Consume mandatory result by named outcome and transfer/restore resources; reclaim child frame only after loans, readers, erasure, and pool release gate permit. |
| Finish scope | Normal exit joins every child; early return, explicit scope-crossing error propagation, declared failure, or scoped timeout marks descendants (including post-latch registrations; cleanup adds none) and joins all of them before releasing captured parent storage. Completed error values alone do not trigger early exit; detached children are excluded. |

Composition fixes activation order without unplanned wakeups, poll-spins, or work donation (R-07-037b rotation has no task scheduler); collect completed/cancelled/failed children by declared index ([completion policy](#task-completion-and-scope-failure)) and eliminate every outcome (including post-cancel failures). Every variable occupancy (dormant envs, frames, scope membership, completions) needs R-08-046 classification/manifest contracts, transactional slot binding, and pre-reserved cleanup capacity (R-08-045 charges metadata/unused reserves; R-08-047 forbids borrowing other pools).

### Sequential async composition

Static types distinguish `await dormant` (sequential execution in current task) from `await child` (observing/joining a registered child); neither creates concurrency, extends lifetime, or grants a fresh cancellation budget. Directly awaited helpers may use caller handler capabilities while the enclosing lexical scope/frame stay live (never relaxing the ban on spawned children capturing outer capabilities); invariants and default dynamic guards close before direct await, even when immediately ready.

```text
async Result<Data, Error> Load()
{
    return await ReadAndValidate();
}
```

`ReadAndValidate()` moves captures into a dormant value; `await` executes the caller's checkpoint first (even if ready)—on cancellation, helper `Dispose` cleans up unstarted captures; otherwise the helper runs, saves PC/resources at poll sites on pending (resuming before caller), transfers results/resources on return, and declares any enclosing-failure exit in its contract. Extracting synchronous work into a ready async helper adds an observable checkpoint (preserve behavior via a synchronous helper or unchanged checkpoint placement; test equivalence by latching cancellation before the checkpoint and checking whether the next body write occurs vs clean execution). Specialization accounts for bounded call nesting, local PCs, storage, captures, loans, and cleanup (inlining/out-of-line share one source contract; zero-cost call-graph erasure of unused handler/context capability parameters requires lowering and frame evidence; recursive helpers require static depth bounds and storage/cost proofs; returned views must point into caller backing or outliving pinned regions; resource requests remain explicit and fallible).

Caller and helper share the task's cancellation latch and commit phase: precommit helpers cannot silently commit enclosing ops without explicitly consuming the unique commit permission and returning its receipt, after which both follow the bounded postcommit continuation (no rollback by late cancellation; independent service requests keep separate commit/quiescence contracts). Accepted cancellation closes active helper loans and runs helper cleanup before caller cleanup (disposing/transferring dormant values and results once). Cleanup may directly await a cleanup-compatible helper whose effects, storage, and bound were pre-reserved: checkpoints preserve sticky cancellation without abandoning/restarting cleanup or admitting non-cleanup work, spawning, recursion, new commits, or unreserved resources; failures follow bounded recovery/fail-stop without inventing ownership, and finite masks share the task's cancellation bound.

### Task completion and scope failure

Source APIs index resources by task outcome (examined by name or explicitly propagated; stricter payload duties still apply):

| Outcome | Meaning and scope effect |
| --- | --- |
| `Completed(value)` | Returned declared `T` and resources (`Completed(Err(e))` on `Result<A,E>` is ordinary completion and does not cancel siblings). |
| `Cancelled(resources)` | Accepted cancellation and finished cleanup; stays in scope until collected and released (collection does not turn it into failure). |
| `Failed(reason, resources)` | Selected an interface-declared failure exit after establishing its predicate (empty failure set if none); initial scope policy latches sibling cancellation on observation at an admitted site. |

Checked failure returns never hide panics, illegal accesses, or missed quiescence (environmental fail-stop keeps platform recovery semantics); postcommit contracts constrain postcommit failure outcomes without undoing committed effects, and service mappings preserve terminal statuses/ownership. The fixed first policy cancels/joins remaining children on `Failed`; handling `Completed(Err(e))` normally leaves siblings alive, while explicit scope-crossing error/cancellation propagation cancels/joins without rewriting recorded outcomes (no name-based implicit promotion). Simultaneous terminal records are observed in composition-declared child order, preserving every outcome and latching early exit once (later failures never erase results or restart cleanup; postcommit siblings join normally; collect-all/supervisor policies need separate contracts/bounds; stopping waits or failing never makes storage reusable).

## Cancellation, commit and all exits

Cancellable children declare frame-incarnation identity, checkpoints, commit, bounded masks, cleanup/join graph, quiescence, and terminal bound (service cancellation also uses R-12-097 generation/request IDs and control plane without new wire fields or rings; local `Task` does not restore deleted IDL `future`).

Delivery latches a persistent bit and marks descendants in bounded graph order (separate from terminal completion); post-latch registrations start marked and take the unstarted path (only owner graphs register into scopes; cleanup registers none and may run sync steps, [cleanup-compatible sequential helpers](#sequential-async-composition), child joins, and declared service/control ops; grandchildren stay in their live parent's scope/`B_terminal`). Control-plane delivery may wait for a scheduled visit (bounded transfer refusal/reoffer only; receipt ≠ release or quiescence; `too_late`/`not_live` are control replies, while `cancel_cancelled` enters cancelled completion keeping storage owned until release):

| Target state at cancellation decision | Required continuation |
| --- | --- |
| Dormant, not registered | Owner disposes locally under `Dispose`; no nonexistent service request cancelled. |
| Registered, unstarted (incl. marked registration / `Submitted` request) | Cancel pre-effects; run unstarted cleanup to restore/consume inputs and record one `cancelled` terminal result. |
| Live before commit | Accept cancellation at next checkpoint and enter cleanup (sticky bit persists across bounded inter-checkpoint segments; contract defines precommit semantics). |
| Commit already linearized | Answer `too_late` and finish committed protocol normally (scope stays cancelled without rolling back commit or token). |
| Stale generation, not live, or non-cancellable | Answer `not_live` (R-12-097) where applicable and inspect owned terminal/generation state (never invent cancellation or free frame); non-cancellable children require bounded normal join. |
| Accepted cancellation during cleanup | Keep bit latched and continue same cleanup idempotently (no restart, duplicate terminal record, or ordinary reentry). |

The final checkpoint arbitrates cancellation before a bounded no-capture/no-suspend commit segment: requests seen there skip commit; later arrivals answer `too_late` (committed state represented before next checkpoint); already-terminal targets answer `not_live` keeping original results (service lowering refines R-12-097 serialization points). At `await`, validate generation, check cancellation/deadlines (interfaces choose whether precommit expiry returns `deadline_expired` directly or cancels to `cancelled`), then collect ready child results in order before cleanup/continuation without discarding ready results or reclassifying commits.

| Runtime | Cancelled-scope behavior |
| --- | --- |
| [Kotlin default start](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-start/-d-e-f-a-u-l-t/) | Skips execution and marks cancelled if cancelled before start. |
| [Java JDK 27 `fork`](https://docs.oracle.com/en/java/javase/27/docs/api/java.base/java/util/concurrent/StructuredTaskScope.html) | Returns `UNAVAILABLE` without thread on cancelled scope; throws `IllegalStateException` post-join/closure. |
| [Python `TaskGroup.create_task`](https://docs.python.org/3/library/asyncio-task.html) | Closes coroutine and raises `RuntimeError` during shutdown. |
| [Trio](https://trio.readthedocs.io/en/stable/reference-core.html) | Child inherits nursery cancellation and raises `Cancelled` at first checkpoint. |
| [Swift SE-0504](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0504-task-cancellation-shields.md) | Outside shields, `addTask` creates an immediately cancelled child (`addTaskUnlessCancelled` starts none); shields start uncancelled. |

Unlike Kotlin's [`NonCancellable`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/), HoldFast gives marked registrations `cancelled` without body effects and runs cleanup sequentially ([R-05-065](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-065) favors sequential cleanup whose `B_cleanup` fits the terminal bound; declared service requests may still overlap waits before await).

| Exit | Resource and control duty |
| --- | --- |
| Fallthrough, return, `break`, `continue`, propagated `Result` | Close local loans, establish return/loop invariant; scope-crossing exits join/cancel; local `Err` handling keeps siblings alive. Retain reason and resource predicate. |
| Handler abort by zero resumption | Run `Dispose` graph (joins + mandatory verdicts) returning disposed resources; explicit typed branch, no unwinding. |
| Precommit cancellation / scoped timeout | Stop ordinary work, cancel/join registered children (register none), quiesce device refs, run cleanup, publish terminal result, follow pool release gate. |
| Client wait timeout | Stop wait only; scope retains task, authority, and join/cancel obligation (never returns loans early). |
| Declared child `Failed` | Preserve outcome, latch scope once, cancel/join siblings (`too_late` siblings finish normally and join); `Completed(Err(e))` remains ordinary. |
| Postcommit normal completion | Keep committed effect, finish bounded remaining work, quiesce, return outcome (cancel ack never frees storage early). |
| Fallible cleanup | Bounded recovery cleanup with retained resources or fail-stop; never returns writable owner, retries unboundedly, recurses, or allocates unreserved resources. |
| Compartment fault, teardown, restart | Source cleanup not assumed; containment/revocation/generation change govern recovery (`peer_restarted` R-12-093); storage stays held until device authority + reuse gate clear. |

R-12-100 completion retains no DMA capability; reclamation also requires all R-12-094 readers consumed, pool release-to-Reusable gate, and R-08-007a barrier/sweep (deleted handles, errors, or absent completions prove no quiescence; missed DMA bounds trigger R-12-099 fail-stop).

## Compositional handler summaries

Retained for the deferred multi-shot search extension (not needed by first async service or one-shot handlers, which still need work/frame/disposal bounds via the common derivation). Public higher-order handler contracts state `Work` and `Frames` bounds via ghost params and `requires`/`ensures` (e.g., `SearchBudget` in [`BestScore`](../assurance/verification-strategy.md#handlers-with-accountable-continuations)), binding callback model, captures, clauses, and resumption across all reply histories/nested choices/exits (invalidated by callback/handler edits). `Search.ExpansionFits(body.Model, budget)` denotes checked compositional evidence, not an assumed Boolean or renamed postcondition; failed inference leaves an open goal.

`Work` counts callback/handler steps, resumptions, cloning, and disposal (adding sequentially, taking worst case across alternatives; `d` binary choices can reach `2^d` leaves despite local `resumes(0..2)`). `PeakFrames` counts max simultaneous live source frames/continuations/envs (not total resumptions). Source summaries confer no pool capacity: lowering connects to layouts/slots/metadata ([R-08-045](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-045), [R-08-047](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-047), [R-05-102](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-102), [R-08-017](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-017); source step ≠ target cycle). `HA-resume-dispose`, `HA-suspend-scope`, and `HA-lowering-erasure` test nested choice, sequential frame reuse, and simultaneous clones, rejecting single-branch-max summaries, omitted callback/disposal work, stale summaries, and live-frame counts used as byte/time evidence.

## Bounds and progress premises

Specialization bounds nesting, children, resumptions, checkpoint distance, masks, cleanup, control delivery, quiescence, and publication via acyclic measures (requests may repeat indefinitely; each request/cancel cleanup has a finite terminal bound; no cyclic join-release waits). For finite path `p`, `L(p) = sum(C(v)) + sum(G(e)) + sum(D(e))` sums work, activation gaps, and uncharged waits (coefficients come from artifacts, not grades; R-05-102/R-08-017/R-11-006 charge polls, checks, failed visits):

```text
B_decide(t) = B_deliver(t) + B_checkpoint(t)
B_tail(t) = sum(B_terminal(child)) + B_collect(t) + B_cleanup(t)
            + B_quiesce(t) + B_publish(t)
B_cancel_suffix(t) = B_tail(t)
B_commit_suffix(t) = B_normal_remaining(t) + B_tail(t)
B_cancel_request(t) = B_decide(t)
                     + max(B_cancel_suffix(t), B_commit_suffix(t),
                           B_unstarted_suffix(t))
B_terminal(t) >= max(B_normal_from_start(t), B_cancel_request(t))
```

In one elapsed time unit, `B_decide` spans request/expiry origin to cancel/commit decision (delivery includes propagation/reoffers; checkpoint includes masks) and suffixes run from there (e.g., delay 5 + committed work 10 + tail 1 = 16, not `max(6, 11)`). Sums conservatively serialize children fixed at cleanup entry (including post-latch registrations; `B_terminal(child)` includes cancel/normal/unstarted/grandchildren; `B_collect` covers parent handling; `B_normal_from_start` includes registration-to-activation delay; release still awaits completion, readers, erasure, revocation, and sweep). Direct awaited helpers add work/waits/checkpoints once to the enclosing task (either expanded or via subgraph summary, never double-counted or resetting masks). Witnesses state units matching [RingContract.v](https://github.com/symbiogenesis/VerifiedOS/blob/main/proofs/RingContract.v) (`cancellation_interval`/`op_max_to_terminal`) and [CopyRingService.v](https://github.com/symbiogenesis/VerifiedOS/blob/main/proofs/CopyRingService.v) (unconnected to HoldFast frames/waits here). Progress assumes admitted WCET, cadence, live generations, bounded quiescence, and delivery without scheduler fairness; unbounded/unavailable peers require failure/teardown branches or no hard progress claim.

<a id="qualification"></a>

## First async service qualification

After [synchronous qualification](../language/first-release.md#qualification) and [delivery plan](../../PLAN.md#holdfast-first-release-delivery) deliverables, freeze a real bounded request service's format, capacities, cleanup reserve, independent valid/invalid fixtures, result/resource contracts, generation/commit interface, and target endpoint (no shared counter or general handlers needed unless used). Exercise one reusable sequential async helper and one structured child (adding a second child only for pre-fixed scope-failure ordering) with inhabited entry states and checked elaboration resources:

| Case | Required behavior and evidence |
| --- | --- |
| Sequential helper, ready and pending | Matches synchronous value/resource contract where applicable; one task, bounded nested storage, checkpoint even on ready, no child registration; factored/inline equivalent without requiring inlining. |
| Error value vs task failure | Local `Completed(Err(e))` keeps siblings alive; scope-crossing propagation cancels/joins; `Failed` triggers scope policy without implicit promotion. |
| Capacity exhaustion and pre-start cancel | `spawn` returns unchanged dormant value on exhaustion; marked child / cancelled direct helper runs zero body effects and disposes/returns captures once. |
| Commit race and cleanup helper | Precommit cancel runs helper then caller cleanup once; postcommit preserves effect and bounded suffix; repeated cancel during cleanup helper neither restarts nor spawns. |
| Ready result beside cancel or failure | Preserve/eliminate every result/resource by outcome, including simultaneous records in order and `too_late` committed siblings. |
| Cleanup failure, late completion, stale handle | Bounded recovery/fail-stop, retain unavailable backing, reject stale generation/incarnation, enforce quiescence and release-to-Reusable gate. |
| Cost, storage, source maintenance | Charge nested frames, masks, results, children, cleanup once; edits invalidate stale evidence; helper factoring/contract edits trigger diagnosed rechecks. |

Negative neighbors must fail their semantic premise (never unsupported syntax): skipping ready checkpoint, omitting helper state, double-consuming resources, promoting `Err`, resetting commit phase, spawning in cleanup, or reclaiming on cancel ack.

## Positive derivations and invalid neighbors

Symbolic paper derivations (not executable checker outputs; multi-shot and shallow stay deferred and do not replace [first async service](#first-async-service-qualification)); fix positive capacities, initialized representations, authority, live generation (`emp` = empty), and expected branches before implementation:

| Case | Trace and resource derivation |
| --- | --- |
| Zero resumption with disposal | `Own(packet) * EraseRequired(packet)` moves into `k`; rejection runs `dispose(k)` finite erasure graph, clears obligation, returns cleared owner (no resumed body events). |
| One resumption with a loan | Pinned outer packet lends shared prefix into `k` (parent suspended); `resume k(reply)` uses view, ends loan, restores parent once. Deep `return` runs once; shallow `rehandle` uses identity return and clause transforms raw result. |
| Multiple resumptions | Handler over `let b = perform choose(); callback(snapshot,b)` captures only immutable snapshot + repeatable effect-free callback (packet/frame outside delimiter). `Dup` clones template, resumes `false`/`true`, collects scalars, disposes template; callback runs twice with independent clone locals/handlers and shared immutable snapshot. |
| Nested lookup and forwarding | Outer `c` (`choose`) + inner `t` (`trace`): performing via `c` captures inner frame unexecuted (deep resume restores both); intervening unhandled `choose` joins `k` unexecuted; explicit forwarding moves `k` into outer-`choose` adapter retaining disposal of `k` and both trace envs. |
| Shallow rehandle | Shallow `S(0)` binds `s` (`tick`) with `emp` resources; first `tick` captures `k1` (`s` is delimiter hole), clause rehandles `k1` with `S(1)` at `k1`'s invocation frame (fresh incarnation of vacated slot), second `tick` reaches `S(1)` capturing `k2` rehandled by `S(2)` whose `return` pairs scalar with `2` (finite specialized set `{S}`). |
| Incarnation exhaustion | 2-bit slot issues/releases 0–3 while holding stale handle 0; 5th allocation returns `IncarnationExhausted(pool)` unchanged without transferring inputs, and stale handle observes/cancels nothing. |
| Ready await | Child finishes `Completed(value)`; parent checkpoints with clear cancel bit and takes ready edge (if cancel latched, still collects ready result then runs parent cleanup without ordinary continuation). |
| Pending await | Spawn, parent checkpoint, store PC, poll-site return; child finishes later; parent revisits, rechecks authoritative completion, checkpoints, matches result (loans stay pinned/closed across gap). |
| Cancellation race | Precommit checkpoint -> cancelled cleanup (token unspent); post-commit segment -> `too_late` then normal completion; post-terminal -> `not_live` and normal collection. |
| Child failure and cleanup | Lower-index child fails precommit -> scope latches, marks sibling -> sibling answers `too_late`, completes normally, joins -> returns indexed pair after cleanup; cleanup failure keeps ownership held under recovery/fail-stop. |
| Spawn after the latch | Within one cooperative segment (R-07-037a), parent reads child 1's `Failed`, latches bit, then `spawn`s child 2 already marked; child 2 runs unstarted path (`Cancelled`, zero body events), and parent's next checkpoint joins both. |
| Capacity and timeout | Full pool -> `CapacityExhausted(pool)` + unchanged dormant value; client wait timeout leaves task in scope; scoped timeout cancels/joins under `B_terminal` (including `too_late` committed child). |

The [combined client](full-language-review.md#composed-client-and-inhabited-entry) adds a repeatable choice callback and atomic counter commit (`N=4`, `n=2`, source `[1,2]`, dst `[1,2,0,0]`; packet owner, frame, and `AddOnce` outside delimiter; final checkpoint + single aligned `AMOADD` form bounded commit segment emitting `Added(c,g,k,n,old)` before next checkpoint; second child tests simultaneous failure/join; service mapping requires explicit cancellation/commit declaration and generation).

| Well-formed change to a positive case | First refusing premise |
| --- | --- |
| Clone one-shot `k` or store in shared cell and invoke aliases | `Dup` for transitive owner/loan or one-shot consumption (cell descriptor copies ≠ contents). |
| Keep `AddOnce` inside multi-shot delimiter | `Dup` for unique commit token (callback repeatability insufficient). |
| Dispose `k` without erasing packet or inspecting child failure | `Dispose` erasure or mandatory-verdict elimination obligation. |
| Resume after parent expires, move self-ref frame, or store absolute ref into captured segment | `Suspend` live incarnation/stable address/parent lifetime; `Capture`/`Suspend`/`Dup` frame-relative premise. |
| Perform via captured handler capability outside handler scope | Lexical-scope premise (every capture must be in scope at use). |
| Pass closure retaining `c` into `c`'s own handler clause (arg or cell) | Lexical-scope premise (arg types bar body-bound capabilities; clauses exclude own `c`). |
| Spawn child whose dormant value captures handler capability | Lexical-scope premise (spawned values type with no handler capability in scope). |
| Resume/clone/rehandle/dispose `k` while clause holds arg loan into `k`'s frames | Argument-loan premise (loan must end before acting on `k`). |
| Resume shallow `k` retaining its handler capability outside `rehandle` | Shallow rehandle premise (delimiter hole filled only by `rehandle` frame). |
| Rehandle shallow `k` with handler outside specialized set | Finite rehandler set (slot sizing and $O(1)$ dispatch fixed at specialization). |
| Perform via handler capability absent from enclosing effect contract | Effect-contract membership. |
| Return parent writable owner while pending child or returned view holds loan | Indexed exit restoration and structured-scope extent. |
| Skip ready-await checkpoint when cancel bit is set | Checkpoint trace and cancellation-priority simulation. |
| Clear cancel bit in mask or resume ordinary work after accepted cancel | Sticky cancellation invariant and cleanup-only transition graph. |
| Spawn child from cleanup graph | Cleanup-only graph (no registration edge). |
| Register into scope from child holding scope handle | Owner-only registration (scope handles do not transfer to children). |
| Spawn after latch and claim child body events or `ok` | Registration-time marking (unstarted `cancelled` path only). |
| Reuse terminal slot under live reader, DMA holder, or pending sweep | Request reclamation and release-to-Reusable gate. |
| Ignore sibling failure or overwrite full completion record | Mandatory outcome elimination / pre-reserved completion capacity. |
| Free task on `too_late`, `not_live`, or wait timeout | Missing terminal ownership transfer and quiescence/reclamation evidence. |
| Add unbounded cleanup retry, forwarding cycle, or ready-task queue | Finite path/ranking proof or R-07-037a lowering obligation. |
| Mutate packet after counter-only AMO as if published | Distinct publication/ownership theorem (counter gives no payload access). |

Negatives must preserve valid parsing/resolution, unrelated entry resources, and op identities, failing at the named premise (not syntax errors or timeouts); deferred cases are not first-release duties.

<a id="open-laws-and-amendment-duties-for-q25d"></a>

## Proof and admission obligations

Each row is a theorem obligation over `Interpret` and the selected anchor (including exact source correspondence), scoped to the commissioned subset (one-shot/sequential async omit cloning, shallow rehandling, and general grade domains until commissioned):

| Open obligation | Required statement and evidence |
| --- | --- |
| `HA-capture-substitution` | Context moves preserve usage dependencies, separation, capabilities, and loans; reply substitution preserves deep/forwarded contracts. Selection reaches named frame and captures intervening frames unexecuted; effect-polymorphic handlers never intercept param capabilities. Lexical scoping holds across args, replies, cells, and spawns; arg loans resolve to `k`'s invocation frame and end before resume/dispose. Include nested envs and forwarding adapters. (Deferred clone/shallow: close arg loans before clone/rehandle; shallow hole resolves only to same-signature rehandler.) |
| `HA-resume-dispose` | One-shot transfers once; zero-shot disposal closes erasure, restoration, verdicts, and protocols on every exit. Duplicated capabilities authorize `perform` only. (Deferred multi-shot: transitive `Dup` for separated invocations, fresh `Delta_i`, compositional traces, clone-local internal refs/handlers; mutable-cell continuations keep disposal duties.) |
| `HA-suspend-scope` | Every activation preserves frame typed representation, stable concrete addresses, and loan tree; parents/frames release only after all child indexed outcomes and returned views discharge. Direct await composes nested state without child registration, keeps lexical capabilities, and restores helper resources. |
| `HA-cancel-progress` | Relate sticky-bit/commit machine to R-12-097 replies with unique terminal result, finite masks, and delivery/child/quiescence bounds; direct helpers inherit cancel/commit without fresh mask budgets or duplicate cleanup. Distinguish `Completed(Err(e))` from `Failed` (fixed-order policy / explicit scope exit). Cover owner-only registration, marked post-latch registrations, cleanup adding none (`B_tail` over fixed cleanup-entry child set; `B_terminal` bounding grandchildren), paths with both decision delay and committed suffix, and crash/cleanup-failure safety without assuming cleanup. |
| `HA-lowering-erasure` | PC-graph simulation of checkpoints, slot lookup, return transforms, and indexed exits; erasure keeps executable tags/effects; one-shot preserves stable frames. (Deferred clone/rehandle: delimiter-relative refs from entry so capture/Dup copy without rewriting, resolving via invocation frames/incarnations including shallow holes and finite rehandler dispatch.) Prove legal effect motion/cloning across checkpoints/commits/handlers; link graph cost/storage to TAL and pinned Sail. |
| `HA-combined-embedding` | Instantiate interface with real bounded async service (helper, child, outcome/cleanup negatives); prove no-suspension restriction matches synchronous core semantics/exits. Later cell/multi-shot extensions instantiate their protocol and combined counter/search fixture. |

The [extension plan](../../PLAN.md#language-extensions) assigns implementation.

| Platform requirement | Acceptance evidence |
| --- | --- |
| R-08-045 through R-08-047 | Declare and account for all frames, scopes, continuations, and completions under [runtime storage](full-language-review.md#runtime-storage). |
| R-05-009 and R-05-020a | Check interpreted computation, exact source correspondence, and concrete laws. [Frontend admission](full-language-review.md#frontend-admission) |
| R-05-100 and R-07-037a | Prove typed absence and cooperative reactions over PC graph with bounded nonblocking joins and explicit exits. |
| R-12-093 through R-12-095, R-12-097, R-12-100 | Use declared control replies, terminal ownership, completion capacity, and device quiescence. |
| R-05-132 through R-05-134 and R-11-006 | Project source evidence into admitted TAL attributes and separate kernel-checked obligations with schedule evidence. |
