# Compiler route comparison

HoldFast targets the retained CHERI-C/Clight route. A conditional comparison
would exercise it and direct capability-aware lowering at the same
[artifact endpoint](#equivalent-artifact-endpoint). Both routes need the
canonical machine logic and arbitrary-context proof. Entry requires
[checked prerequisites and priced work](#re-entry-packages). [Release contract](../language/first-release.md#release-boundary) ·
[Compiler route decision](verification-strategy.md#compiler-route-decision)

## Fixed consumers and common source boundary

Use the [parser and held-out staging clients](workflow-contract.md#clients-and-baseline-evidence) preserving identical init, results, reads, callbacks, failures, and owner restoration. Follow [baseline independence rules](workflow-contract.md#freeze-and-independence) and freeze emission rules before adapting S.

Both arms consume one content-addressed [source package](verification-strategy.md#mechanically-produced-evidence), interpreted computation, and representation contract: sequenced op graph, stable runtime indices, erased checked evidence, branch resource predicates, bounded loops, closed read/write/call/no-alloc effects, and fixed layout/ABI. Semantics covers inputs/outputs, I/O, prescribed refusals/faults, and tier leakage/cost observations; source owners prove parsing, resolution, desugaring, interpretation, and erasure (maps/hashes alone do not suffice). Each route proves transport through internal CFG/block/SSA IR to machine traces, relating helper abstractions to source observations, authority, refusal/trap classes, and leakage/cost.

Maintain the independent manual baseline at the same contract/evidence endpoint; regenerate unoptimized and optimized candidates from authoritative source with matching source changes, inputs, caller grants, primitive contracts, placement, link context, eligible transforms, and evidence duties. Larger grants or weaker failures invalidate comparison.

## Baseline identity and evidence

Bind each producer's revision, dependency closure, build recipe, theorem subjects/assumptions, and binary digest at entry. Check concrete CHERI/Sail coverage using the [VerifiedOS foundation map](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/cheri-foundation-map.md) and [the compiler plan](https://github.com/symbiogenesis/VerifiedOS/blob/main/PLAN.md#m1-toolchain-spine-incl-the-cheri-compcert-prerequisite). [Workflow baselines](workflow-contract.md#clients-and-baseline-evidence)

## Equivalent artifact endpoint

Package contents: authored source closure, elaboration/interpretation evidence, representation, generated IR, transform records, primitive/ABI contracts, final linked image/digest, TAL certificate, tier CIC proofs, and validation of assembly, relaxation, link, layout, and image construction. Machine theorems resolve R-05-019b's Sail-generated Rocq definitions for hardware refinement (separate transcriptions need admitted agreement theorems).

Final-image correspondence covers all model/context-permitted behaviors against committed source and declared assumptions: failures, divergence/termination treatment, authority, initialization, and observations (terminating postconditions supply no progress). R-05-024 robust preservation quantifies over adversarial linked contexts (emitted-program induction or hostile-caller samples cannot substitute).

R-05-023a requires CIC-checked decompilation into R-13-017's Iris-over-Sail logic (unary safety, universal capability contract, relational constant-time, syntax-directed cost); TAL soundness and deeper tier duties meet the binary under R-05-026. Bounded emission cannot replace this logic, and host SMT/oracle/differential checks supply falsification only.

Validate, run, and promote each route's exact final image: bytes may differ, source contract/assumptions/observations may not. Any change to bytes, relocations, certificates, source bindings, or configuration invalidates evidence and requires recompilation.

In the [first-slice harness](../language/first-release.md#first-slice-qualification), program and harness share one label namespace: duplicate labels (including trap-handler/exit-mailbox collisions), undefined constant names, and cyclic constant definitions refuse assembly; constants resolve to the latest preceding assignment or, for forward references, the first definition. Differential runs verify `main` addresses an aligned executable word before image emission, require consecutive retirements from harness entry with every PC (including startup/trap-handler) inside the executable segment, and validate handwritten ELF executable segments against the scalar instruction family (tested by inserting an untaken-branch vector instruction and asserting word/address detection); compiler images use [their own admission requirements](../../PLAN.md#q25ba).

### Evidence for each deployed claim

Each shipped claim identifies its public law, exact linked image and entry point, target/ABI, permitted callers/observations, and [endpoint evidence](workflow-contract.md#review-and-evidence-endpoints). Record the TCB, checking kernel, machine/hardware/runtime/FFI premises, checked transforms versus untrusted generation/search tools, and premise-to-claim paths exposing any [assumption change](workflow-contract.md#reviewing-a-public-contract-change).

For the packet entry point, trace functional result, returned-view authority, and pre-metadata descriptor validation to their proofs; include foreign-input adapter paths in the same evidence and cost ledger. Substituting host execution during trials must flag missing target evidence.

For the importing library, trace one claimed proof/ownership erasure through inlining to admitted machine code, inventorying surviving checks, copies, allocations, refcounts, and indirect calls (`n/a` when outside representation) vs the [matched hand-written baseline](workflow-contract.md#cost-of-the-verified-abstraction) with measured/proved bounds and units (never guessing missing metrics). Each target image tracks its own evidence, assumptions, and costs.

## Route boundaries and closed emission family

**Clight arm.** Prove common-graph-to-imperative transport and CHERI-C/Clight representation bridge (plus C printing if used), keep CHERI-CompCert pass proofs, and complete final Sail validation/admission (simulations may retain invariants; annotation erasure preserves semantics).

**Direct arm.** Prove transport to explicit-memory capability IR at the same boundary, compose bounded emission rules, and verify/validate optimization/allocation before the same Sail/admission endpoint. Explicit blocks are default; SSA requires proved conversion, phi/parallel moves, and capability-preserving allocation (charged here; no general frontend, LLVM path, or optimization framework is commissioned).

The closed producer grammar binds encodings/primitives solely via the selected [profile](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/isa-profile.md) and R-05-023b Sail clauses: input constructor, emitted term, entry/exit representations, consumed/restored frame, word-arithmetic premises, effects/observations, termination/cost duties, and Sail-simulation Rocq constant (missing constants block the rule).

| Rule family | Permitted form | Required proof obligations and refusing neighbor |
| --- | --- | --- |
| `value` | Fixed-width scalar constants, comparisons, arithmetic, explicit extension/truncation; structured initialized values | Checked ranges/modular meaning, field layout, observable result; hidden pointer/int cast refused |
| `read` | Bounded byte or declared scalar read via live read capability | Tag, provenance, permissions, range, alignment, init; frame preserved; hoisting load above guard refused |
| `write` | Declared field/byte write via exclusive fixed-destination authority | Exact initialized-range transition, zero padding read, no overlapping writer; failure exits keep partial state |
| `capability` | Tag-preserving moves/spills/reloads, bounded advance, attenuation, exact narrowing | No forged authority, exact tags/representability, declared width/registers, matches Sail traps; integer spill/outward bounds refused |
| `sequence` | Explicit left-to-right composition and pure local bindings | Matching intermediate predicates, composed frames, legal post-erasure uses; duplicating affine authority refused |
| `branch` | Boolean branch or closed discriminant case with explicit result/resource joins | All ordinary/failure exits restore resources; secret observations obey relational contract; missing failure restoration refused |
| `loop` | Bounded loop with declared invariant and ranking/bound evidence | Init/preservation/exit, finite bound, effects/cost, consistent per-iteration loan restoration; data-dependent unbounded loop/implicit alloc refused |
| `frame` | Static entry/exit and declared spill slots under composed plan | Fresh init live ranges, tag-preserving spills, stack bounds, callee-saved regs, exact return authority; zero runtime alloc/GC/dynamic frame |
| `call` | Statically linked helper or contracted sentry/primitive call with matching return form | ABI/authority, effects, observations, relocations, termination, Sail-bound primitives; unchecked external/callback/suspension/reentrancy excluded |

The trial uses clients' scalar ops, specializing the repeatable zero-byte callback to a proved loop body or contracted static helper (preserving invocation, capture, effect, and restoration duties; unchecked dynamic callbacks excluded). Success qualifies only this family/clients, leaving R-18-014 vector/scalar-FP/production completeness intact (M1.3/M1.3a keep outlining/tail-merging without a second budget).

Closure order (rules and proof constants frozen pre-lowering):

1. Build constructor census from initial graph and post-erasure/lowering/opt/alloc/link intermediates; every reachable construct, helper, and linker stub resolves to one rule/checked contract (unknowns fail with site ID).
2. Prove generic composition theorem across all admitted family programs (loops, branches, failures), compose with source interpretation and Sail connection, and audit assumptions (example enumeration fails).
3. Lower reserved staging client with unchanged grammar, definitions, and proof constants (new client instances/invariants allowed and counted; new semantic constructors, representation exceptions, special rules, or stronger caller assumptions fail—report the gap instead of widening tests).
4. Decode final image and verify total site coverage, primitive meanings, typed linkage, relaxation preconditions, and artifact identity (ignoring linker stubs fails).
5. Run intended-layer mutations on exact artifacts, separating compile-failing stillborns from semantic/admission kills (any survivor is an unresolved finding).

## Reproduction and measurement protocol

Freeze a reviewed pre-entry manifest (missing fields make the package incomplete; `n/a` cannot replace required proofs/targets/comparators; record real artifacts only):

```text
contract_revision; route; client; baseline_kind;
source_closure; SourcePackage; interpretation; representation_instance;
repository_revision; generated_interface_identity; selected_Sail_closure;
producer_source_and_binary; package_locks; commands_and_options;
primitive_contracts; emission_grammar_and_constants; optimization_configuration;
ABI; link_context; composed_layout; target_class; timing_model_and_parameters;
image_digest; TAL_certificate; CIC_obligations_and_assumptions;
post_compilation_validation; reproduction_lane; licence_record; reviewer;
input_generator_and_seed; mutation_identity; host_machine_and_worker_limit;
attended_work_log; wall_and_CPU_time; peak_RSS; result_and_missing_premises
```

Freeze [comparator identities](#baseline-identity-and-evidence) and revisions pre-measurement (post-result baseline/threshold changes require a revised run, rationale, and retained prior output); track licences across compiler binary, runtime/primitives, and copied preambles.

Apply the [target protocol](workflow-contract.md#target-and-production-artifact-protocol) identically across manual, generated unoptimized, and generated optimized runs (secondary unoptimized isolates construction overhead without performance credit) using declaration-generated initial, empty, 1-element, boundary, full, malformed-discriminant, truncated-field, overflow, and failure inputs.

Corpus traces give retirements/capability memory effects, not cycles; timing needs R-18-024/R-18-025 annotations/core class or a justified timing instrument. Host elapsed time measures build/proof cost and instruction counts trace size—neither yields WCET/cycles, and SRAM/interconnect/tag effects cannot be guessed.

| Measurement | Predeclared criterion |
| --- | --- |
| Functional behavior, source identity, initialization, authority, failure and leakage guarantees | Exact correspondence and unchanged assurance assumptions across variants (zero tolerance for safety diffs) |
| Admitted bounds and declared resources | Admitted bounds, island peak footprint, stack/storage/alloc support <= baseline with zero displaced components (R-18-014 constraints override experimental ratios) |
| Executable target cost and encoded image bytes | [Native-code and cycle thresholds](workflow-contract.md#accounting-and-decision-thresholds) govern executable code size and per-case cycles; report total image bytes (incl. padding/metadata) separately without substitution; missing cycles block that verdict, and sampled maxima != WCET |
| Applicable optimization | Optimized per-case cost <= unoptimized and total image bytes <= unoptimized while preserving resource/assurance criteria (failure declines only the optimization result) |
| Host machine budget | Caps: 4 workers, 16 GiB peak RSS, 60 min clean-build/replay, 8 h aggregate wall time per route (workflow's shorter local-edit replay limits keep their own endpoint; caps stop runs rather than estimate missing proofs) |
| Reproduction and stability | Clean independent lane reproduces final images/evidence; deterministic runs repeat cleanly; record cold + complete warm runs (never cherry-pick fastest or drop contention) |
| Adoption and maintenance | Apply [accounting thresholds](workflow-contract.md#accounting-and-decision-thresholds) across full endpoint incl. establishment/repair (source savings cannot offset unmeasured machine work) |

Attribute capability costs by site (narrowing/derivation, redundant auth ops, tag-preserving spills/reloads, peak live capabilities, ABI/slot padding, representability refusals, alloc/promotion tags; merged scalar ops get no capability-saving credit); separate qualified reuse from new proofs in CSE/coalescing/allocation using profile-defined widths/registers.

## Negative and disagreement cases

Generate variants recording expected failure layers pre-mutation; source neighbors may fail elaboration, whereas backend/artifact variants must reach downstream checks (syntax errors refute nothing).

| Mutation or disagreement | Required outcome |
| --- | --- |
| Swap equal-width direction/content fields keeping total size | Layout/source correspondence rejects changed interpretation (arithmetic reflexivity/unchanged bytes missed Q2a's field-order bug) |
| Hoist read above length guard; truncate destination; claim untouched field initialized | Construction/representation proof or final evidence rejects access/exit (error status never excuses OOB reads) |
| Int-cast capability, strip spill tag, widen bounds, or raise permissions | Representation/emission or final Sail/TAL check fails despite matching low bits/host run |
| Duplicate writable loan or drop restoration on error/loop exit/return | Source resource check or binary/frame proof rejects (exempting exits changes the contract) |
| Re-read source post-validation in staging client | Copy-once/source-stability fails on distinct images (distinct from concurrent race over non-atomic writable buffer) |
| Insert secret-dependent addr/branch or variable-latency op in opt | Relational leakage check fails despite matching outputs |
| Add unlisted stub, alter sentry role, or mis-preserve registers | Closed emission coverage or typed linkage fails (no ad-hoc external-call axioms allowed) |
| Change resolution/desugaring, dependency, or representation while reusing old proof | `SourcePackage` or evidence binding invalidates; old-core theorems cannot certify new source |
| Tamper bytes, relocations, layout, TAL evidence, or primitive map post-check | Identity, coverage, typing, or refinement fails at boundary (rebuilding another image does not fix this one) |
| Routes disagree on status, effects, tags, failures, resources, or observations | Keep both images and debug against common source + Sail (neither route wins by incumbency/brevity) |
| Routes agree while weakened contract or broken shared parser/layout fails negative tests | Common-mode dependency flagged in manifest; cross-route agreement != independent proof |

Probe independent changes to a client bound, equal-width field interpretation, representation/ABI, and admitted optimization, logging unchanged generic replay, updated instance/client proofs, invalidated certificates, and repair effort (new client byte semantics != generic reuse).

## Pricing and entry conditions

Log human attended hours, agent hours, machine wall, CPU, and RSS separately per complete endpoint with owner-linked `establishment`, `remaining_port`, `shared_maintenance`, and `per_client_repair` (estimates pre-work, measurements at adoption; missing values = `unpriced`; shared items appear once per alternative and once in integrated totals).

| Obligation | Clight route ownership and credit | Direct route ownership and credit |
| --- | --- | --- |
| Exact source and interpreted core | Shared source/interpretation owners | Same shared owners and missing prerequisites |
| Primitive, representation and restoration laws | [Foundation map](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/cheri-foundation-map.md#foundation-ownership-ledger) `machine-logic`, `byte-instance`, `scoped-resources` owners; credit checked subject laws | Reuse matching subjects; bounded replacement lemmas must state exact replaced obligation + checked substitute (machine + arbitrary-context parts remain) |
| Decoder realization and source-to-imperative/Clight transport | Q2b owns P + `source-transport` decision; M7.1 owns S (excess scope needs owner extension pre-entry) | Same P/S behavior/baselines; direct graph-to-IR + representation transport needs compiler owner's separate estimate (`unpriced`); reuse source interpretation |
| Capability carrier, permissions, ABI, narrowing and functional backend | Incumbent M1.2 children (canonical cells + acceptance credit) | Reuse only compatibly qualified subjects; direct selection/alloc/emission/composition unpriced |
| Optimization and required target completeness | M1.3/M1.3a + R-18-014 owners with capability/leakage duties | Reuse same owners or price compatible port (no separate speed-only checker/stream) |
| Final validation, TAL, source correspondence, leakage and robust preservation | `context-preservation` + `artifact-admission` producers supply secure-compilation, R-05-023a, TAL evidence | Same endpoint/logic owed plus independently checked arbitrary-context connection (bounded emission does not erase this cost) |
| Linkage, production join and reproduction | Existing assembler/composer + proof owners | Shared if unchanged; modified ABI/link bridges need explicit owner/estimate pre-work |
| Bounded comparison execution and review | Budgeted against completed prerequisites | Same package/caps; per-route repair charged to repaired artifact's owner |

Price full machine/context links, source/representation bridges, direct backend, and maintenance pre-trial: bounded emission organizes local proofs only and still owes all foundation, context, and admission results.

### Re-entry packages

Track owner, inputs, check, consumer, and separated `establishment`/`remaining_port`/`maintenance` costs per package:

| Package and accountable owner | Required output and predeclared check | Join and stopping condition |
| --- | --- | --- |
| Shared foundation and secure-compilation owners | Bind Sail closure + checked constants; list missing arbitrary-context/tier work (closed-client or unagreed machine theorem fails review) | Shared one-record input across routes; halt if common logic/context lacks scope/price (never open direct lane to discover it) |
| Retained compiler producer | Bind source/build/digests to acceptance predicates; audit reuse across source-to-Clight transport, carrier/ABI, emission, opt, certificates for P and S | Join shared foundation + M1 realization; halt if total price extrapolates from functional bring-up or admit counts |
| Direct compiler producer | Break down files/passes/proofs for graph-to-IR transport, representation, alloc, closed emission, composition, reused pass licences, trace relation, ABI/link, hardening | Review pre-lane; halt if needed rules/context theorems are named-only or if closed grammar cannot express P/S |
| Client and baseline owners | Executable byte-memory defs + independent baselines per [workflow contract](workflow-contract.md#freeze-and-independence) (explicit init/failures); price scope excess at existing owner | Qualify concrete laws and freeze interface pre-S adaptation; halt if S leaks design feedback or uses a core fixture |
| Trial and adoption owners | Freeze manifests, cost allocation, reviewer, target/cycle setup, licence readings; apply identity, mutation, closure, and [thresholds](workflow-contract.md#accounting-and-decision-thresholds) | Accepted producer/foundation packages unlock measurement; missing historic/recurring cost leaves adoption `undecided` |

<a id="conditional-amendment-and-reviewer-requirements"></a>

## Alternative route approval

[R-05-043](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-043) mandates Clight for synthesized decoders; alternative intermediates require checked evidence for descriptor transport, fixed-dest init, copy-once, failures, bounded representation, source-to-Sail refinement, automated construction, and bounded runtime:

| Existing duty | Evidence or decision owed before any substitution |
| --- | --- |
| R-05-043 decoder synthesis | Checked synthesis/representation chain through proposed intermediate to final endpoint incl. error paths and source anchor |
| R-05-019b, R-05-020 and R-05-020a | Shared Sail-generated defs; new authoritative semantics/logic/checker must satisfy R-05-020 bridge/non-duplication/retirement; untrusted elaborators satisfy R-05-020a (supplying no resource law, compiler, or artifact acceptance) |
| R-05-023, R-05-023a and R-13-017 | Final CIC-checked Iris-over-Sail refinement (substitutes need explicit approval covering every obligation) |
| R-05-024, R-05-026 and R-05-032 | Adversarial-context robust preservation, binary-tier evidence, authored-source correspondence with declared leakage/progress |
| R-05-023b | Total primitive-site checks vs profile-bound meanings and TAL rules (no private instruction semantics or second consumer checker) |
| R-18-014 and its refinements | Keep CHERI-CompCert TCB and certifying-Rust duties intact (direct generation counts as neither; replacement requires owner/scope/bootstrap/independence decision) |
| Typed interoperation and compiler independence | Proved verified-C/Rust linkage; disclosed shared frontend/model/validator/proof deps (distinct binaries alone != independent assurance) |

Review duties: compiler owner (emission/backend), foundation owner (subjects/assumptions), source owner (interpretation/failures), target/admission owner (image/timing); Tier-A reviewer inspects/replays both routes at pinned revisions (inaccessible dependencies block review).

Read file and transitive licences pre-incorporation from the [CompCert/SECOMP record](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#compcert-and-secomp) and [tool inventory](../../THIRD-PARTY.md#development-tools-contained-by-use), re-reading on pin/file updates across inspection/replay, commercial use, compiler redistribution, preambles, and helpers (this doc grants no licences). Dependency removal requires absence from implementation/proof closure (changing IR leaves reused-pass licences intact); commercial rebuildability still disposes of Clight dual-licensed files, TCB/Rust duties, Velus, and the oracle env.

## Readiness decision

Conditional on [entry packages](#re-entry-packages); keep correspondence, admission, resource evidence, and target timings distinct and compare cost/performance only once both arms reach the same endpoint. [Backlog](../../PLAN.md#q-assessment-actions)
