# Language extension composition

> Design for a joint graded, handler, async and cell client. The
> [first-release contract](../language/first-release.md#release-boundary) defines
> the synchronous baseline. [Extension plan](../../PLAN.md#language-extensions)

<a id="inputs-and-common-boundary"></a>

## Common boundary

The [graded](graded-foundation.md), [handler and async](handlers-async.md) and
[mutability](interior-mutability.md) designs share the same checked interpretation.
The [admission requirements](#frontend-admission) apply to their composition.

## Composed client and inhabited entry

This proposed client exercises the interaction of multi-shot handlers, async,
and concurrent scalar mutation. The [first-release delivery plan](../../PLAN.md#holdfast-first-release-delivery)
qualifies a synchronous buffer operation and an independent package first. The
[first async service](handlers-async.md#qualification) exercises sequential
async composition and one child before optional cloning or a concurrent counter.

The client uses one declared child slot, a private packet frame and the mutability dossier's scalar accepted-byte counter. Its packet has represented length `n`, capacity `N`, and immutable `xs` satisfying `length(xs)=n` and `n<=N`. The child owns the packet, live frame identity/generation, request identity and a linear allowance to add `n`. Other children require disjoint frames/allowances. The counter stores no capability.

A source-level witness chooses `N=4`, `n=2`, `xs=[1,2]`, initialized backing `[1,2,0,0]`, a free slot, zero counter and allowance two. These are examples, not profile constants. The counter reserves range for all outstanding allowances; each increment consumes its allowance. A pure callback `f(xs,b)` sums the snapshot independently of its represented public Boolean. Its stable environment requires a separate duplication law, captures no packet owner, borrow guard or single-use verdict, and permits two invocations under the foundation's separate type-dependency rules.

A bounded choice handler resumes with `false` then `true`, producing `(3,3)` for this witness. Each resumption retains only the duplicable snapshot; the exclusive packet/frame owner stays outside the delimiter. Control and grade proofs must establish capture and demand, beyond lexical free-variable analysis. The child then reaches a cancellation checkpoint and, if live and uncancelled, performs its one atomic increment: the commit point. Terminal publication and scope join follow the control protocol.

The witness inhabits only the proposed source data/protocol model. No checked inhabitant of the concrete CHERI separation-logic interpretation is supplied.

## Paths the join must preserve

| Path | Required source outcome and resource account |
| --- | --- |
| Ready result, no cancellation | The ready await still performs its semantic checkpoint. Both callback uses are accounted; the counter increment consumes the allowance once; the parent releases the private frame only after observing the terminal result and discharging held references. |
| Pending result | The bounded frame stores represented state and the declared continuation point, then returns at a syntactic poll site. Only the admitted reaction graph can resume it. The counter and allowance remain unchanged before commit. |
| Cancel before start | The registered scope still owns the dormant child's captured packet and allowance. Typed cleanup returns or disposes of them and publishes `cancelled`; a request alone does not free the frame. |
| Cancellation observed at a pre-commit checkpoint | The checkpoint selects cleanup. The counter is unchanged, the unused allowance is returned, and the cancellation result is observed before safe reuse. |
| Request arrives after the last pre-commit checkpoint | Arrival alone does not accept cancellation. If the bounded commit region reaches the atomic update before the request is handled, the post-commit observation returns `too_late` and follows normal completion. |
| Cancel after commit | The operation answers `too_late` and finishes its normal terminal protocol. The counter is not decremented; the consumed allowance is not returned as unused. |
| Full child/frame pool | Binding returns the mandatory capacity verdict and the unstarted computation's resources. No implicit wait or borrowing from another pool occurs. |
| Child failure or cleanup failure | The owning scope observes the declared result. A fail-stop/restart path uses the platform's revocation and containment obligations; safety cannot depend on running ordinary source cleanup after a crash. |

The control bound includes parent-child order, checkpoint delay, cleanup, device quiescence and terminal publication, covering decision delay plus the selected cancelled/committed suffix and separately ordinary execution. This example supplies no numeric target. Public witness values and schedule choices establish no confidential-input observation or constant-time result.

## Well-formed neighbors and their judging premise

These are proposed semantic judgments, not results from an executable frontend.
Each neighbor retains the client's supported syntax and well-typed ordinary
data while changing the stated resource premise.

| Neighbor | Required refusal |
| --- | --- |
| Hide the packet owner in the callback or a stored continuation | The transitive captured-resource duplication premise fails before a multi-shot continuation can be copied. Idempotent analysis grades cannot repair it. |
| Permit two resumptions but supply a one-call exact budget | Computation-use reconstruction cannot establish the required demand. The callback's duplicable memory environment does not duplicate its declared usage budget. |
| Reuse an old cell snapshot as a proposition about its current value | The operation lacks the current invariant/snapshot agreement premise. A stable historical value is not evidence that interference has not occurred. |
| Suspend or perform a capturing effect with a dynamic exclusive guard open | The suspension/capture rule lacks a closed invariant and transferable exit account. A ready result does not remove that checkpoint duty. |
| Release the parent frame after a cancellation control reply such as `cancel_cancelled` or `too_late` | Release requires terminal completion, quiescence and the end of outstanding references. |
| Ignore the child failure or capacity verdict | The branch cannot eliminate its mandatory outcome obligation. Affine ownership disposal supplies no verdict-elimination rule. |
| Replace the scalar increment by conditional capability CAS | The operation lacks an admitted primitive and violates the shared-mutable-capability restriction. No source wrapper authorizes it. |
| Return an allowance as unused after the atomic increment | The counter invariant loses conservation of committed value and outstanding allowances. Cancellation cannot roll back the commit point. |

## Conservative connection to the synchronous slice

Restrict syntax/representation to the [core](../language/core-design.md): stable data, flow-sensitive loans, explicit exits and existing callback contracts, without handlers, async, cancellation or concurrent cells. Select domains/structural rules for those uses without weakening `Delta`; preserve runtime lengths, tags and represented values through erasure.

Conservativity must map derivations and executions to the core with identical entry/exit interpretation, effects and observations, introducing no control/memory operations or lost loan/verdict duties. Substitution, reindexing, preservation, erasure, interference and every exit must commute with the projection. Qualification requires the conservativity theorem and a concrete returned-view law.

## The representation the composed duties are stated over

All composed duties use one byte-and-capability carrier: memory regions and tagged capabilities over the Coq definitions emitted by Sail (R-05-019b). Grades, proofs and counter allowances are erased; frames, child slots, continuations and completion records occupy ordinary storage. The [concrete foundation](../../PLAN.md#shared-foundation-and-retained-route) supplies the `byte-instance` and `scoped-resources` laws.

| Composed duty | What it states over that carrier | The missing constant that would discharge it |
| --- | --- | --- |
| Simultaneous substitution with dependency reindexing | A substituted telescope's resource account is the substitution of its account: reindexing a dependency moves no footprint, changes no tag, and leaves the disjoint audit and payload fields where they were. | `byte-instance`'s memory-frame law over the disjoint footprints the substitution preserves. |
| Resource preservation across a step | Each step carries the entry account to the exit account of its outcome, with every returned owner, loan, mandatory result, continuation and terminal obligation still separately owned. | `scoped-resources`' disjoint split and join, shared and exclusive reborrow, suspended-parent access and restoration entailments. |
| Erasure | Erasing grade, proof and allowance data leaves the carrier's bytes, tags, initialization predicate and observations unchanged, and two instances differing only in erased data have related retained behavior. | `byte-instance`'s initialization, write and tag-effect laws, which decide that erasure moves no initialized byte. |
| Interference | A snapshot's proposition survives exactly the writes the cell's invariant admits, and the counter's committed value and outstanding allowances are conserved across the atomic update. | `machine-logic`'s invariant and mask machinery, with the pinned term's own clause for the atomic operation. |
| Each exit of the path table above | Every ready, pending, cancelled, `too_late`, capacity and failure exit restores the account that path names, and the frame is released only after terminal collection. | `scoped-resources`' restoration entailments and `byte-instance`'s write law for the reserved completion record. |

The client requires checked machine-logic, byte-instance and scoped-resource laws
that construct inhabitants of these carriers. See the
[shared foundation](../../PLAN.md#shared-foundation-and-retained-route) and
[extension plan](../../PLAN.md#language-extensions).

<a id="existing-owners-and-where-each-decision-is-taken"></a>
<a id="reviewed-implementation-pricing"></a>

## Implementation obligations

The predicates below apply to the selected extension. The
[extension plan](../../PLAN.md#language-extensions) assigns scope, owners,
budgets and entry conditions. The
[shared foundation](../../PLAN.md#shared-foundation-and-retained-route) supplies
concrete resources and the base compiler route.

The frontend checks named receiver views, once-only evaluation and overlapping
arguments. Diagnostics check [claim freshness and scope](assurance-profiles.md#evidence-beside-the-declaration).
[Handler summaries](handlers-async.md#compositional-handler-summaries) specify
compositional traces and frame accounting.

| Obligation | Acceptance predicate |
| --- | --- |
| Graded resource and erasure laws | [Graded proof obligations](graded-foundation.md#proof-and-qualification-obligations) |
| Handler and async laws | [Control proof obligations](handlers-async.md#proof-and-admission-obligations) |
| Cell, borrowing and interference laws | [Mutability proof obligations](interior-mutability.md#separate-theorems-and-missing-law-handoff) |
| Elaboration, domain evidence and grade reconstruction | Public signatures resolve domain IDs, grade variables, constraints, call modes, captures, effects, and representations; unresolved constraints remain explicit goals with proposition, dictionary, substitutions, and replayable certificate (fails if timeouts, inconsistent models, or failed reconstructions pass as equalities, or if search weakens exact declarations to upper bounds). |
| Handler capture and bounded async lowering | Emit checked capture boundary, callback demand, and reaction-graph state/poll sites from the derivation (fails if captures infer from lexical names or lowering adds threads, run queues, or inner schedulers barred by R-07-037a). |
| Cell, borrow and snapshot protocol checking | Check sealed interfaces, borrow states, and snapshots at source; derive transfer/sharing structurally across fields, closures, tasks, and stored continuations (fails if getters or hidden-effect callbacks pass under open exclusive guards). |
| `SourcePackage` correspondence, specialization and stale-source rejection | Parsing, resolution, instance selection, and desugaring bind to exact core computation; specialization fixes phase, ABI, layout, and erasure pre-emission; results carry generation (fails if stale core accepts changed source, or if grade-polymorphic functions share an ABI across represented and erased instantiations without uniform-erasure proof). |
| Source diagnostics for the added rules | Locate first unsatisfied obligation in author ops/values and separate rule violations, refuted contracts, unknown/timed-out goals, unsupported features, and profile refusals (fails if stale/unfinished results pass as accepted or semantic edits leave reported obligations unchanged). |
| Preset selection, mixed linking and policy qualification | [Assurance policy](assurance-profiles.md) and its [qualification protocol](assurance-profiles.md#qualification-protocol). |
| Source representation and IR bridge for the added constructs | Carry graded, handler, and cell resource accounts into the selected representation (fails if claimed by naming constructs rather than discharging representation duties). |
| Attribute projection under R-05-132 through R-05-134 | Project grades/protocol laws into admitted attributes where rules suffice and carry the rest (including the target theorem that shared mutable memory holds no capabilities, assumed by R-15-026's `Zacas` exclusion) as kernel terms (fails if general domains, dependent normalization, or grade dictionaries are asked of an attribute without new admissibility proof). |
| Final-byte admission and source correspondence under R-05-023a and R-05-026 | Final image refines committed-source behavior across assembly, linking, and image construction with rechecked tier certificates (fails if digest matches pass as semantic theorems). |
| Arbitrary-context preservation under R-05-024 and R-05-032 | Quantify over adversarial linked contexts and compose with exact final artifact (fails if closed-code theorems or finite emission replace the context quantifier). |
| Reaction-graph cost and schedule admission under R-07-037a and R-11-006 | Bound reaction-graph cycles via max-path sums with loop bounds and include masked-cancel distance (fails on unbounded cleanup retry, forwarding cycles, ready queues, or unproved asserted bounds). |

### Metaprogramming and compiler-service extension

A selected [metaprogramming client](metaprogramming.md#qualification) exercises
required-static evaluation, opt-in descriptions or checked generation. The
[tooling plan](../../PLAN.md#tooling-and-metaprogramming) selects the compiler
services and adapters it needs. [Compiler inspection contract](../tooling/tooling-protocols.md#compiler-inspection-api)

| Duty | Existing join and additional acceptance |
| --- | --- |
| Static evaluation, dependent reindexing and generated resource uses | `core-soundness`: preserve the graded/resource interpretation and kernel-compatible conversion; no static knowledge follows from erasure or a grade. |
| Description, hygiene and generated-source correspondence | `core-frontend`: bind descriptor dictionaries, declaration identities, scoped generated terms, target/ABI and the exact resulting computation; no arbitrary elimination of `Type` or trusted generator result. |
| Diagnostics, claims and tooling | `core-diagnostics` and `preset-policy`: preserve source provenance and current evidence status; `holdfast-compiler-services` exposes shared versioned views, and LSP/SARIF/SCIP consume projections. Syntax assets follow the canonical grammar; build, remarks and trace adapters consume their actual producers. No second semantic implementation or proof-acceptance path. |
| Lowering and runtime-cost qualification | Existing compiler, admission and hardware owners: retain effects, exits, leakage, representation and final-artifact evidence; inspect removal of generator machinery and measure residual code, descriptors and specialization growth. |

<a id="r-05-009-r-05-020-and-what-holds-the-frontend-rows"></a>

### Frontend admission

[R-05-020a](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020a)
requires untrusted elaboration with kernel rechecking under R-05-009. The
extension judgments state substitution, dependency, ownership, exit and erasure
obligations over the elaboration's image in the selected semantic anchor.

Checked source correspondence relates parsing, resolution, instance selection,
implicit insertion and desugaring to the exact checked term and generated
inputs. Stale source, a changed dependency and a well-typed replacement
operation must fail that binding. Concrete resource laws and represented
lowering are additional prerequisites for executable claims.

An independent semantics or a trusted frontend requires admission under
R-05-020. A replacement ISA model also meets the
[canonical-model substitution criteria](unified-source-contract.md#replacement-admission).

<a id="r-08-046-and-what-the-languages-runtime-varying-storage-is"></a>

### Runtime storage

R-08-046 requires declared bounded pools and complete manifests for static
backing with variable occupancy. Task frames, child slots, scope records,
continuations, completion records and dynamic-borrow guards need a new pool
class. The accepted-byte counter is a single fixed-width scalar charged under
R-08-045. Its outstanding-allowance invariant and overflow behavior belong
to `MUT-ATOMIC`.

Each selected pool requires the following manifest and lifecycle evidence.

| Manifest field | Required evidence |
| --- | --- |
| Owning compartment, element type and fixed capacity | Name the concrete owner, represented slot type and finite capacity. |
| Derivation of contents | Identify the selected typed task family and its lowering to a reaction graph. |
| Binding and release | Identify compartment-level authorization and prove that scope registration, join and cleanup refine the monotone member lifecycle. |
| Low and exhausted thresholds, release bound and reserve | Supply numeric thresholds, a target bound from release request to `Reusable`, and the recovery reserve. |
| Exhaustion action | Return the typed capacity verdict under R-08-047. |
| Occupancy and telemetry | Declare their confidentiality labels and qualify observations under the selected leakage contract. |
| Restart and generation migration | Prove restart and migration behavior under the platform containment and revocation rules. |

A runtime extension that uses these pools requires the declared manifest,
checked lifecycle refinement and admission of the pool class under R-08-046.
