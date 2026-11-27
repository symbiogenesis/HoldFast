# Interior mutability and interference contract

> Design for local cells, checked dynamic borrows and concurrent protocols
> beyond the [first-release subset](../language/first-release.md#release-boundary).

## Scope and shared interface

Each selected cell, dynamic borrow or concurrent protocol needs a concrete
consumer and checked representation and operation laws. Sealed interfaces grant
only their declared operation rights. The [synchronous library contract](../language/first-release.md#ownership-libraries)
specifies ordinary ownership and loans.

Use the [resource and computation interface](graded-foundation.md#resource-and-computation-interface): stable `Gamma`, separate computation/type use and dependency rows, and `Delta` for owners, loans and protocols. Outcome-indexed transitions retain captures, effects, event counts, representation and exit duties. This specializes the [synchronous core](../language/core-design.md#judgments-and-interpretations), without a second resource interpretation.

`Capture`, `Dup`, `Dispose`, `Suspend`, `Transfer` and `Share` need semantic evidence. A grade counts invocations only through its trace interpretation; it creates neither ownership, access authority nor release. `Own(r,shape,snapshot)` belongs in `Delta`; stable identity `r` and historical snapshots may index `Gamma`, never unsynchronized current contents.

The concurrent candidate uses private packets and tasks with an atomic scalar
counter. It needs an actual consumer and a proof over the selected memory
model. [Atomic profile](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-15-026)
· [Exclusive-access constraints](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-096a)

### Interpretation commitment

Local operations use the selected resource logic. Target operations and
interference refer to the pinned Sail term. Substitution, capture, exit
preservation and erasure quantify over those computations and their
representations. [Frontend admission](full-language-review.md#frontend-admission)

## Representation, authority and open invariants

A cell declaration binds identity, domain, fixed footprint/layout, lifetime/generation, contents type, invariant, transitions, interference, operation rights and concrete memory representation. The latter includes CHERI permissions, tags, provenance, temporal state and initialization; naming an invariant proves none of them.

The proposed proof interface is schematic; its arrows relate assertions about the selected anchor computation and grant no independent operational semantics:

```text
CellDecl(c, domain, generation, footprint, representation, invariant, protocol)
Closed(c, state) * OpRight(c, operation) * Frame
  -- operation --> Exit(result, Closed(c, state') * Returned(result) * Frame)

open:  Closed(c, s) * OpenPermit(c, scope)
       -> Open(c, scope, s) * Representation(c, s) * CloseDebt(c, scope)
close: Open(c, scope, s) * Representation(c, s') * invariant(s')
       * CloseDebt(c, scope) -> Closed(c, s')
```

These proof transitions cannot extract resources from duplicable propositions. Prove exclusive opening permission, a mask preventing reopening, and absence of overlapping representation permissions outside the region. When a record or cell declaration factors its invariant into named conjuncts (`invariant Clause: P`), [`open (ref ...) lifts Clause, ... { ... }`](../language/surface-grammar.md#resource-contracts-and-lexical-handler-capabilities) refines `Open` and `CloseDebt(c, scope, lifted)` to open only the listed conjuncts: unlifted conjuncts remain active without re-proof across writes to disjoint or non-invalidating fields, any write that invalidates an unlifted conjunct must immediately re-establish it at that write, and `close` requires re-proving only the lifted conjuncts at the closing brace while refusing early exits (`return`, `break`, `continue`, `?`), suspension, handler capture or whole-receiver calls while `CloseDebt` is live. Nested openings follow an acyclic order over nonconflicting footprints; the frame rule and interference preserve unborrowed resources.

A local opening permits no interfering activation before close. A concurrent invariant opens only for a proved logically atomic operation or a proved exclusive ownership phase; an indivisible AMO does not make surrounding code atomic. Close consumes its debt once, restores the current representation and ends interior loans before return.

Seal representation primitives against forged handles, casts, exposed fields and untyped bypasses in source and final code. Load/store capability permission alone proves no ownership state. [R-05-096b](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-096b) still requires binary splits and the manifest join. Shared scalar capabilities are privately injected at composition; a received integer identity grants none.

## Local cells

`LocalCell(d,c,T,I)` is confined to domain `d`, with state `Full(v)` satisfying `I(v)` or an explicitly supported `Empty`. Its fixed representation stores authority once. Private storage may hold owners/capabilities only under its representation and lifecycle laws; this grants no concurrent sharing.

| Operation | Entry and result contract |
| --- | --- |
| `snapshot` | Establish a stable mathematical value related to the current representation during one authorized observation. An executable copy additionally requires a duplicable contents representation and declared destination storage. |
| `replace(new)` | Consume the new represented value, prove `I(new)`, install it and return the old value by move. No copy of either owner survives inside the cell. |
| `take` | Available only for a cell whose invariant includes `Empty`. Move the value out, leave `Empty`, and make operations requiring `Full` return a typed empty result. |
| `put` | Consume `Empty` and one owned replacement; return `Full` under its invariant. An occupied-cell result returns the unconsumed replacement. |
| `with_update(f)` | Open the invariant and pass a scoped view to a callback with checked transitive effects and captures. Every callback outcome closes the invariant and returns no interior view. The contract states whether an error preserves the entry value or returns a valid changed value. |

Authority-bearing `T` supports scoped observation, authority-free pure projection or `take` by move, never unrestricted `get : T`. An unretained displaced value from `replace` requires explicit disposal.

A scoped callback cannot suspend, capture control, call unknown/reentrant code, publish its view or retain it transitively in a result, closure, cell, task, continuation or exception-like encoding. Exclude the opening identity and descendant loans from the whole result capture closure; a lifetime marker alone is insufficient. Frame laws permit disjoint resources. The default rule also forbids alias reentry into the open cell.

## Checked dynamic borrows

`BorrowCell(d,c,T,I)` supports same-domain aliases with sealed guard identities and represented states `Idle(v)`, `Readers(v,S)` and `Writer(v,g)`: bounded live-reader identities `S` or unique write guard `g`. A bounded count plus accounted guard slots may implement them only with identity correspondence, overflow exclusion and exact decrement proofs. This ordinary local state word is no concurrent lock.

| Transition | Required result |
| --- | --- |
| `try_read` from `Idle` or `Readers` | Allocate a guard from declared capacity, preserve the same immutable contents, suspend conflicting writes and return a scoped read view. |
| `try_read` from `Writer` | Return `BorrowConflict`; leave cell and caller resources unchanged. |
| `try_write` from `Idle` | Produce one scoped write guard, suspend all overlapping parent access and open the representation under its close debt. |
| `try_write` from `Readers` or `Writer` | Return `BorrowConflict` without a view or partial state change. |
| Reader capacity exhausted | Return the declared capacity verdict, with no counter wrap and no guard created. |
| Release read guard | Consume its identity once, remove exactly that reader, and restore `Idle` only when no reader remains. |
| Release write guard | End descendants, prove the invariant of the final value, consume guard and close debt, and restore `Idle`. |

Public `with_try_read` and `with_try_write` bracket nonescaping library guards.
Clients must examine conflict and capacity results. Each successful acquisition
creates a release obligation. The checker rejects a missing or duplicate
release, a duplicated guard, or a forged decrement.

Reader guards permit compatible reads and forbid footprint mutation; writer guards exclude all overlapping parent, wrapper, device and closure access. Reborrows suspend parents until descendants end. Both scopes forbid suspension/capture, including ready `await`; a future stable read-guard extension needs its own `Suspend`, represented lifetime and cancellation release proof. A conflict branch runs only the sealed state operation, with no callback or second opening.

## Snapshots and dependent indices

`Snapshot(c,e,x)` relates immutable `x` to observation event `e`; `e` is logical unless explicitly represented, not an implicit version counter. It proves neither `current(c) = x` nor current read/length permission. A concurrent scalar observation describes one linearization point, not a separate payload snapshot.

For a packet with capacity `N`, represented length `n` and `length(xs) = n <= N`, snapshot `n0,xs0` remains stable after replacement with length `n1`. `i < n0` still indexes `xs0`; current access needs fresh permission and `i < n1`. A type-changing shape update consumes the old owner and returns a dependent pair with represented `n1` and erased inequality proof.

A multi-field copy needs exclusion throughout or a proved snapshot protocol; separate loads, a sequence counter around a racing non-atomic copy, or atomic payload bytes do not suffice. The selected interface publishes a complete immutable payload. Retained refinements must withstand actual interference, including hidden getters/callback writes.

### Ante as a candidate for static invalidation

[Ante's place-and-mutation design](https://antelang.org/blog/safe_cyclic_mutability/) could infer local-view invalidation. Distinguish address validity from current-content refinements: stable scalar overwrite may preserve a view while invalidating `current(c) = x`. Accept disjoint stable-field updates preserving view/invariant; reject use after invalidating replacement, container mutation or destruction. Hidden callback writes and handler capture need the same analysis.

The proposed proof context records a current fact's dependency footprint
separately from a view's address and lifetime footprint. Dependencies use resolved
places and operation contracts, including transitive call effects. After a
possibly overlapping write, reuse needs checked preservation or re-establishment
of the current fact; an unknown effect leaves that premise unresolved. Historical
snapshot facts remain stable. The [borrow-analysis promotion contract](../language/core-design.md#borrow-analysis-promotion)
connects these obligations to source checking without selecting shared mutation
for the synchronous release.

Qualification requires ownership, opening, closing and capture laws for every
exit, including suspension and cancellation, plus local-domain and artifact
exclusivity evidence. [Ante design comparison](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#ante-place-sensitive-mutation-and-invalidation)

## Transfer, sharing and lifecycle eligibility

Eligibility is transitive through fields, instantiated parameters, environments, tasks and stored continuations. Sealing representation requires a checked theorem exposing its real captures/operations to verification.

| Predicate | Evidence required |
| --- | --- |
| `Capture(v)` | Whole transitive set of retained identities, permissions, loans, close debts and terminal obligations; distinguish temporary evaluation effects from retained state. |
| `Dup(v)` | Duplicating the represented value and its associated resource predicate preserves ownership and all protocol obligations. A duplicable descriptor does not duplicate an access grant. |
| `Dispose(v)` | Exact disposal transition for stored owners, must-erase values, guards and relevant results. An unknown finalizer is no evidence. |
| `Suspend(v)` | Stable represented storage, closed invariants, permitted live loans, preserved obligations and a bounded resume/cancel path at the checkpoint. |
| `Transfer(v,d1,d2)` | Sender loses access before receiver gains it; every retained field is transferable and remains live. Cross-compartment transfer conforms to the fixed grant/manifest protocol. |
| `Share(v,D)` | All participants have separately justified operation rights; the contents representation, permitted interference and observation policy remain sound under simultaneous use. |

Default `LocalCell`/`BorrowCell` have no cross-domain `Share`. Moving a quiescent cell requires no guards, loans or open debt, loss of old-domain handles, and proved domain/storage transfer/rebinding. Wrappers, grades, callbacks and hidden local/thread-local state bypass none of these. [Ambient-state exclusion](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-039) includes caches, registries and lazy initialization behind pure-looking methods.

Shared scalar capabilities stay in private participant environments. Shared mutable memory holds only declared scalars, never capabilities, capability-bearing closures/continuations or task frames. Private stable storage may hold a capability-bearing continuation; transferring it needs a proved fixed-authority-graph protocol, not a pointer serialized into a shared cell.

## Concurrent protocols and the actual memory model

`ConcurrentCell(c,g,S,P)` declares state machine `P`, interference, participant roles, scalar representation `S`, rights and linearization/release points. Each operation proves its functional relation, invariant preservation, published resource transfer and observations. An atomic success is one transition at its proved point; failures establish declared unchanged/partial state, not implicit rollback.

The target is [Ztso](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-15-004) with [whole-path ordering](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-15-015a). The [Sail AMO implementation](https://github.com/symbiogenesis/VerifiedOS/blob/main/model/model/extensions/A/zaamo_insts.sail) decodes `AMOADD`, adds a word and writes it; [memory access](https://github.com/symbiogenesis/VerifiedOS/blob/main/model/model/sys/mem.sail) classifies accesses. These are inspected subjects, not checked HoldFast atomic laws or a concurrent-logic instance.

Lowering names the same pinned Sail term, width/alignment, capability load/store permissions, PMA support, tags, `aq`/`rl` and observations. Distinguish ordinary memory, MMIO and DMA. Forbid widening across neighbors, synthesized CAS/LR-SC, locking `libatomic`, unsupported capability atomics and non-atomic aliases into atomic footprints.

### Immutable publication and reclamation

The [SPSC lifecycle](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-12-094) permits exclusive initialization, consumes writing at publication, grants immutable reader access and restores writing only after all readers/device holders end or are revoked with quiescence. Shared descriptors contain scalar indices/lengths; receivers resolve private tables and validate generation, extent and rights.

Publication orders payload stores and producer loads before the publication-index store; consumption orders the observing load before subsequent descriptor/payload loads and consumer stores. Prove these store-to-store/load-to-store and load-to-load/load-to-store edges from Ztso, compiler preservation and per-hart fabric ordering. The [fence-free ring contract](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-12-008) requires that proof; annotations supply none.

Ztso lacks general store-to-later-load ordering. Reclamation needs terminal acknowledgments and ownership transitions; local store-then-load proves no peer stop. A protocol needing that edge must prove a legal drain fence's semantics/bound or use another protocol. Fences cannot repair overlapping non-atomic authority. Guard release, publication, cancel acceptance, terminal completion and reuse remain distinct.

[R-12-099](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-12-099) changes generation before restart/revocation reuse, invalidating old handles/queued indices. Equal indices/counts prove no freshness: retire all old-generation rights. [R-08-046](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-046) also retains quarantine, revocation and sweep where applicable.

## Concrete scalar service and composed client

Retained for a later concurrent-library experiment (a synchronous local-cell client needs no atomic publication, tasks, or handlers; the cross-feature packet/search/counter fixture is a deferred stress case). `CountCell(c,g)` is an aligned atomic `u64` (zero at generation `g`) summing committed packet lengths without storing payloads, pointers, request IDs, or capabilities (privately injected capabilities and operation rights are required; integer handles in `Gamma` grant neither). `AddOnce(c,g,k,n)` is a unique `Delta` token for live request `k` and represented length `n` (never a copyable grade), conserving `sum(n) <= U64_MAX` across generation `g` by spending on issue and retiring once on cancel/commit (new traffic needs fresh allowance or quiescent generation, never wraparound or load-then-check). Analogous sequential RC pre-allocation ([Evergreen's `starts_owner` / 3-state conservation](../assurance/verification-strategy.md#rust-and-low-level-verification), `count = owners + reserved_clones + retiring_owners`) is distinct from `CountCell`'s Ztso `AMOADD` protocol.

```text
commit_add(private_handle, AddOnce(c,g,k,n), represented n)
    -> Added(c,g,k,n,old)

cell transition: value = old  -> value = old + n
resource transition: AddOnce -> one committed receipt
target candidate: one aligned AMOADD.d, aq = false, rl = false
```

The AMO commits counter arithmetic only (no payload publication, stable current value, or cross-client old-value ordering; `aq`/`rl` bits must be proved; callback grades prove neither AMO execution nor allowance consumption). In [the combined client](full-language-review.md#composed-client-and-inhabited-entry), `commit_add` is a child action excluding packet/frame owners and `AddOnce` from handler capture (witness: `N=4`, `n=2`, backing `[1,2,0,0]`, prefix `[1,2]`, immutable 2-use callback env, free slots, live grants, zero counter, allowance 2; or two children with allowances 3 and 2 yielding 5 with intermediate 3 or 2—requiring checked [resource carrier](full-language-review.md#the-representation-the-composed-duties-are-stated-over) inhabitants and grant/atomicity/publication/schedule proofs).

### Cancellation, completion and reset

Under [R-12-097](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-12-097), final checkpoint, AMO, and private committed-receipt store form one bounded no-suspend/no-capture/no-reentry/no-source-failure region with sticky cancellation (arrivals between checkpoint and AMO decide postcommit).

| Reachable outcome | Cell and resource result |
| --- | --- |
| Cancel before registered child starts | No AMO; retire allowance, place returned inputs in reserved `cancelled` completion record, keep frame until terminal collection and release gate. |
| Cancel at pre-commit checkpoint | Close prior scopes, retire allowance unchanged, clean private state, join `cancelled`. |
| Commit succeeds | Consume allowance at AMO, keep receipt until normal terminal completion, bar replay. |
| Cancel after checkpoint/commit region starts | Decide at next point; once committed, answer `too_late` and finish normal completion without decrement or replay. |
| Stale or nonexistent request | Answer `not_live` under generation/request test without allowance or stale access. |
| Frame or completion capacity unavailable | Return pool capacity verdict pre-start with unstarted inputs intact and no AMO obligation. |
| Parent stops waiting | Scope retains child/packet/frame until terminal join (wait timeout releases nothing). |
| Generation restart or environmental fault | Fail-stop, revocation, and quiescence (no assumed source cleanup, normal completion, cross-generation counter preservation, or replay). |

DMA quiescence is `n/a` here (task/reader quiescence and pool release still apply; DMA extensions keep packet loans until HAL completion/quiescence—`too_late`, dropped handles, or seen increments prove none). Completion uses private records or immutable SPSC publication; reset requires joining all terminals and retiring old-generation rights; live loads require single-copy width/alignment atomicity laws (not multi-field snapshots). [Task outcome policy](handlers-async.md#task-completion-and-scope-failure) leaves `Err(BorrowConflict)` / `Err(CapacityExhausted(...))` as ordinary completed values rather than implicit `Failed` outcomes.

## Exit closure and bounded progress

Ordinary outcome-indexed exits restore invariants and end guards without unproved destructors:

| Exit or control event | Closure obligation |
| --- | --- |
| Fallthrough, ordinary return, `Result` propagation | End descendants, consume close/release debts, establish outcome-tagged cell state and resources (rollback only if contracted). |
| `break`, `continue`, bounded-loop back edge | Close loop-local invariants/guards and restore loop predicate before jump. |
| Effect operation, callback, reentrant call | Close before any potentially capturing/suspending/reentrant call (certified local callbacks run inside only if contracted free of those effects/captures). |
| Ready/pending `await`, cancellation checkpoint | Closed invariants, no default guards, stable frame storage, explicit `Suspend`/cleanup derivation (direct helpers share the task without fresh guard/cancel budgets; ready does not skip checkpoint). |
| Handler discard / deferred multi-shot | Account for transitive `Dispose` or `Dup` (open debts/guards/allowances fail unsupported discard/duplication). |
| Accepted cancellation | Enter bounded cleanup with invariant closed, retire/return tokens, join before reuse. |
| Cleanup failure | Default close/release are total; fallible external cleanup needs an explicit quarantined terminal state and proved containment (never ordinary reusable ownership). |
| Panic, trap, environmental fail-stop | Prove trap absence under premises (no unwinding); external faults stop domain/session with revocation/quiescence without assuming source closing. |

Map local steps, checkpoints, cleanup/publication, joins, and quiescence to [R-07-037a](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-07-037a) and [R-11-006](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-11-006), composing elapsed bounds `Lcheckpoint`, `Lcleanup`, `Ljoin`, `Lterminal` (direct helpers share enclosing state/bounds without an extra child term; postcommit has its own bound; no-checkpoint AMO region must fit locally). Progress names admitted activations and service/HAL bounds without hidden fairness, spinning, or hardware-recovery substitution.

## Qualification cases and rejection neighbors

Commissioned extensions freeze consumer, ops, and cases under [the delivery plan](../../PLAN.md#holdfast-first-release-delivery) (local cells, dynamic borrows, and concurrent protocols may qualify separately; async/multi-shot apply when selected; negatives parse/elaborate from satisfiable entry states and fail at the named premise).

| Case | Expected accepted derivation or first rejected premise |
| --- | --- |
| Local `replace` returns owner by move | Updates invariant and returns displaced resource once; returning a second copy fails split. |
| Two readers then writer | Both read guards keep one immutable value; writer returns `BorrowConflict`; releasing both restores `Idle`. |
| Writer updates then returns `Err` | Error predicate holds valid updated state; guard release precedes propagation (rollback needs own proof). |
| Child returns borrow/capacity error | Local handling keeps siblings active; scope-crossing propagation runs early-exit join; silent `Failed` promotion violates outcome policy. |
| Snapshot length 3, replacement length 1, access index 2 | Snapshot stays valid history; current access fails fresh bound/resource predicate. |
| Hide owner in cell inside unrestricted callback | Transitive capture includes stored owner; duplicating callback fails `Dup` regardless of grade. |
| Return view in nested wrapper or continuation | Result capture retains scoped loan; escape fails scope closure. |
| Reenter same cell via pure-looking getter | Transitive effects expose conflict; open-invariant callback premise fails. |
| Cancel or await with open write invariant | Checkpoint lacks closed invariant/release proof (ready/pending alike); bounded-region arrivals wait for checkpoint. |
| Read immutable published packet, reclaim after holders end | Publication consumes write, readers share immutable access, quiescence restores write once (early reclaim fails). |
| Copy non-atomic payload under live writer | Exclusive-access premise fails pre-copy (sequence counters/retries cannot repair). |
| Two additions with conserved allowances 3 and 2 | Either linearization gives 5 post-join; second call with allowance 1 fails linear consumption. |
| Check counter below limit, add without allowance | Historical load cannot exclude concurrent adds; overflow premise fails. |
| Precommit vs postcommit cancel | Precommit retires allowance without add; postcommit gives `too_late` and completes once (in-region arrival decides afterward; pre-join parent reuse fails ownership). |
| Capability-bearing frame in shared cell | Representation/`Share` reject shared mutable capabilities even through sealed wrappers. |
| Generic CAS, LR/SC loop, or widened sub-word AMO | No admitted exact-op lowering law; target rejects unsupported instruction/footprint. |
| Both components accept with overlapping non-atomic grants | Composed manifest join fails R-05-096b. |
| Observe completion and reuse old generation handle | Generation and rights-retirement premises fail despite matching scalar indices. |
| Ignore child failure or borrow/capacity result | Missing mandatory verdict elimination (cell restoration does not discharge it). |

## Separate theorems and missing-law handoff

| Guarantee | Required theorem subject and premises |
| --- | --- |
| Functional correctness | Interpreted state machine refines contracts; `commit_add` linearizes once and generation count matches committed allowances (needs representation/read/write/atomic laws, conserved bound, no-replay history; linearizability alone does not prove intended meaning). |
| Race freedom | Composed source derivation excludes conflicting non-atomic access and transports via correspondence/lowering/TAL to all binary/manifest-admitted Sail executions (needs exact footprints, atomic classes, permissions/frames, device participants). |
| Progress and release | Normal/accepted-cancel traces reach declared terminal predicates within bounds and reusable regions quiesce (needs bounded activations, total local close/release, reserved terminal capacity, external bounds; race freedom ≠ progress). |
| Leakage and policy | Related initial states preserve public observations over architectural leakage model and final artifact (needs security labels, allowed releases, address/branch/AMO observations, schedule/resource accounting, relational compiler preservation). |

Example exposes public lengths, schedules, and count while keeping contents private (no declassification of secret lengths, failures, occupancy, AMO order, or completion time; security grades alone give no relational theorem). [Sharing/disposal](../assurance/verification-strategy.md#effect-handlers-sharing-and-protocol-logics) and [Rust surveys](../assurance/verification-strategy.md#rust-and-low-level-verification) note mechanized temporary guarding (`MUT-CELL`), resource-leak adequacy (`MUT-EXIT`), VerusBelt, and RustHornBelt Cell/Mutex proofs over foreign languages/models/provers—none builds this concrete CHERI/Sail representation or inhabited cell.

Applies to the selected elaboration image and exact source correspondence ([Extension plan](../../PLAN.md#language-extensions)):

| Debt | Concrete acceptance predicate and ownership boundary |
| --- | --- |
| `MUT-CELL` | Interpret sealed cell predicates, invariant masks, unique open/close debts, and framing over concrete resource logic; prove `replace`/`take`/`put`/callback rules. |
| `MUT-BORROW` | Borrow-state correspondence, bounded guard capacity, alias exclusion, exact release, and all exits (incl. nested captures) with graded substitution/handler exit rules. |
| `MUT-SNAPSHOT` | Observation-to-snapshot intro, interference stability, current-predicate invalidation, dependent shape transport, and executable copy to initialized memory. |
| `MUT-SHARE` | Transitive capture and `Dup`/`Dispose`/`Suspend`/`Transfer`/`Share` across sealed reps, frames, and handlers, excluding shared mutable capabilities and bypasses. |
| `MUT-ATOMIC` | Concrete counter invariant/history, one-use allowance, exact AMO linearization, overflow exclusion, width/alignment/permission/PMA, and atomic observation against pinned Sail. |
| `MUT-PUBLISH` | Instantiate SPSC proof with immutable packet/completion publication, Ztso/compiler/fabric ordering, reader/DMA quiescence, and generation retirement. |
| `MUT-EXIT` | Join cancellation, checkpoint masks, helper cleanup, no-replay receipt storage, child completions, and reset with async rules (outcome-indexed resources/bounds; `Completed(Err)` ≠ `Failed`; helper preserves commit phase and cleanup count). |
| `MUT-OBSERVE` | Information-flow contract for counter/packet (AMO results, occupancy, cancellations, schedules) preserved through optimization and final bytes with noninterference/WCET/compiler owners. |
| `MUT-CLIENT` | Construct inhabited concrete entry witnesses, replay all positives/negatives, independently review byte/behavior contracts, and connect trace to final representation (plus [composition rules](full-language-review.md) when combined). |

<a id="requirement-disposition-owed-at-q25d"></a>

### Platform requirements

| Requirement | Acceptance evidence |
| --- | --- |
| R-05-096a and R-05-096b | Retain exclusive non-atomic access and explicitly atomic shared cells; check binary and manifest together. |
| R-15-024 through R-15-027 | Use admitted scalar `Zaamo`/`Zabha` ops; exclude CAS, LR/SC, and shared mutable capability storage. |
| R-05-039 and R-05-100 | Inject mutable state and use explicit bounded exits. |
| R-05-020a and R-05-026 | Check interpretation and exact source-to-artifact correspondence. [Frontend admission](full-language-review.md#frontend-admission) |
| R-05-132 through R-05-134 | Use admitted TAL attributes and separate kernel-checked source evidence. |
| R-07-037a and R-11-006 | Use cooperative reactions, bounded masking, and nonblocking guard acquisition. |
| R-08-045 through R-08-047 | Declare storage and exhaustion behavior; reuse requires checked lifecycle release. [Runtime storage](full-language-review.md#runtime-storage) |
| R-12-094 through R-12-099 | Implement publication, capacity, cancellation/commit, terminal, and generation rules. |
