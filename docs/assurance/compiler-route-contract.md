# Compiler route comparison

Vela targets the retained CHERI-C/Clight route. A conditional comparison
would exercise it and direct capability-aware lowering at the same
[artifact endpoint](#equivalent-artifact-endpoint). Both routes need the
canonical machine logic and arbitrary-context proof. Entry requires
[checked prerequisites and priced work](#re-entry-packages). [Release contract](../language/first-release.md#release-boundary) ·
[Compiler route decision](verification-strategy.md#compiler-route-decision)

## Fixed consumers and common source boundary

Use the [parser and held-out staging clients](workflow-contract.md#clients-and-baseline-evidence)
from the workflow comparison. Both arms preserve the same initialization,
results, reads, callbacks, failures and owner restoration. Apply the
[baseline independence rules](workflow-contract.md#freeze-and-independence)
and freeze the emission rule family before adapting the held-out client.

Both routes consume the same content-addressed [source package](verification-strategy.md#mechanically-produced-evidence), interpreted computation and representation contract: sequenced operation graph, stable runtime indices, erased checked evidence, branch resource predicates, bounded loops, closed read/write/call/no-allocation effects, fixed layout and ABI. Meaning includes inputs/outputs, I/O, prescribed refusals/faults and tier-required leakage/cost observations. The source owner proves parsing, resolution, desugaring, interpretation and erasure to that graph; maps/hashes alone suffice for none. Each route proves transport through its internal CFG/block/SSA representations to machine traces. Abstracting implementation-only helper events requires a checked trace relation preserving source observations, authority, refusal/trap classification and applicable leakage/cost interpretation.

Maintain the manual baseline independently as the experimental comparator at the same contract/evidence endpoint. Regenerate unoptimized and optimized candidates from authoritative source. Give both routes identical source changes, inputs, caller grants, primitive contracts, placement, link context, eligible optimizations and evidence duties. Larger grants or weaker failures invalidate the comparison.

## Baseline identity and evidence

At entry, bind each producer's selected revision, dependency closure, build
recipe, theorem subjects and assumptions, and binary digest. Use the
[VerifiedOS foundation map](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/cheri-foundation-map.md)
for concrete laws and [the compiler plan](https://github.com/symbiogenesis/VerifiedOS/blob/main/PLAN.md#m1-toolchain-spine-incl-the-cheri-compcert-prerequisite)
for available backend evidence. Verify that the selected facts cover the
client's CHERI representation and final Sail behavior.
[Workflow baselines](workflow-contract.md#clients-and-baseline-evidence)

## Equivalent artifact endpoint

The endpoint package contains authored source closure, elaboration/interpretation evidence, representation, generated IR, transformation records, exact primitive/ABI contracts, final linked image/digest, TAL certificate, tier-required CIC proofs and validation of every assembly, relaxation, link, layout and image-construction step. Machine theorems resolve R-05-019b's same Sail-generated Rocq definitions as hardware refinement. A separate machine transcription needs an admitted agreement theorem.

Final-image correspondence covers every behavior permitted by the model/context against the exact committed source and declared assumptions: failures, required divergence/termination treatment, authority, initialization and observations. A terminating postcondition supplies no progress. R-05-024 robust preservation additionally quantifies over adversarial linked contexts; emitted-program induction or hostile-caller samples cannot replace it.

R-05-023a requires CIC-checked decompilation into R-13-017's Iris-over-Sail logic, including unary safety, universal capability contract, relational constant-time and syntax-directed cost. TAL soundness and deeper tier obligations meet the final binary under R-05-026. Bounded emission may discharge construction/instruction cases, but cannot replace that logic. Host SMT, oracle and differential results supply falsification, not substitute kernels.

Validate, execute and promote each route's exact final image. Bytes may differ across routes; their source contract, assumptions and observation model may not. Changed bytes, relocations, certificates, source bindings or configuration invalidate dependent evidence; recompilation requires a new package.

The [first-slice harness](../language/first-release.md#first-slice-qualification)
checks each handwritten control's executable ELF segment against its scalar
instruction family. The native regression inserts a vector instruction in an
untaken failure branch. The checker must report the offending word and
address even when the passing Sail trace matches. This covers the control
images. [Compiler image admission](../../PLAN.md#q25ba)

## Route boundaries and closed emission family

**Clight arm.** Prove common-graph-to-imperative transport and its capability-aware CHERI-C/Clight representation bridge, including C printing if used. Retain proofs for applicable CHERI-adapted compiler passes, then supply final Sail validation/admission. Simulation relations may retain invariants; annotation erasure must preserve their semantic consequences.

**Direct arm.** Prove transport to explicit-memory capability IR at the same source/representation, compose the bounded emission rules and reuse or verify/validate applicable optimization/allocation before the same Sail/admission endpoint. Blocks are the default for explicit sequencing/joins. SSA additionally needs proved conversion, phi/parallel moves and capability-preserving allocation, charged here. This commissions no general frontend, LLVM path or optimization framework.

This proposed closed producer grammar resolves encodings and primitive names exclusively through the selected [profile](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/isa-profile.md) and Sail clauses under R-05-023b. Each rule binds input constructor, emitted term, entry/exit representations, consumed/restored frame, word-arithmetic premises, effects/observations, termination/cost duties and its Sail-simulation Rocq constant. A missing constant blocks the rule; a desired-theorem comment is insufficient.

| Rule family | Permitted form | Required proof obligations and refusing neighbor |
| --- | --- | --- |
| `value` | Fixed-width scalar constants, comparisons, arithmetic and explicit extension/truncation; structured initialized values | Checked ranges or modular meaning, field layout and observable result. Pointer/integer reinterpretation cannot be hidden in a cast. |
| `read` | A bounded byte or declared scalar read through a live read capability | Tag, provenance, permissions, range, alignment and initialization; frame preserved. Moving a load before its admitting guard is refused. |
| `write` | A declared field or byte write through exclusive fixed-destination authority | Exact initialized-range transition, no padding read, no overlapping live writer; failure exits retain their actual partial state. |
| `capability` | Tag-preserving moves and stores/reloads, bounded advance, permission attenuation and exactly representable narrowing | No authority creation, correct tags and representability, declared pointer width/register organization, and the same trap behavior as Sail. Integer spill/reload and outward-rounded bounds are refused. |
| `sequence` | Explicit left-to-right composition and pure local bindings | Intermediate predicates match, frames compose, runtime uses remain legal after erasure; duplicating affine authority is refused. |
| `branch` | Boolean branch or closed discriminant case with explicit result/resource joins | Every ordinary and failure exit restores the declared resources; secret observations obey the selected relational contract. Missing failure restoration is refused. |
| `loop` | A bounded loop with a declared invariant and ranking/bound evidence | Initialization, preservation and exit, finite bound, accumulated effects and cost, consistent loan restoration on every iteration. No data-dependent unbounded loop or implicit allocation is admitted. |
| `frame` | Static entry/exit and declared spill slots under the composed plan | Fresh initialized live ranges, tag-preserving spills, stack bounds, preserved registers and exact return authority. No runtime allocator, garbage collector or hidden dynamic frame exists. |
| `call` | A statically linked helper or explicitly contracted sentry/primitive call with the matching return form | Required/provided ABI and authority, effects, observations, relocations and termination behavior; no unchecked external, callback, suspension or reentrancy is added. Primitive semantics is its profile-bound Sail clause. |

The trial uses the clients' scalar operations. Specialize the workflow comparison's repeatable zero-byte callback to a proved loop body or contracted static helper, preserving invocation, capture, effect and restoration duties; unchecked dynamic callbacks are excluded. Success qualifies only this family/clients, leaving R-18-014's vector, scalar-floating-point and production completeness intact. M1.3/M1.3a retain required optimizations, including outlining/tail merging, without a second budget.

Closure is decided in the following order, with the rules and proof constants frozen before the reserved client is lowered:

1. Generate the constructor census from the initial source graph and from every intermediate after erasure, lowering, optimization, allocation and linkage. Every reachable construct, helper and linker-created stub resolves to one rule and one checked contract. Unknown constructs fail with a source/site identifier.
2. Prove the generic composition theorem over all programs of the admitted family, including loop invariants, branches and failures. Compose it with the source interpretation and the Sail connection, then inspect its assumptions. Enumerating example programs alone cannot satisfy this step.
3. Lower the reserved staging client with the unchanged grammar, definitions and proof constants. New instances and checked client invariants are permitted and counted; a new semantic constructor, representation exception, special-case rule or stronger caller assumption fails this closure trial. Report the missing rule instead of expanding the test population after observing it.
4. Decode the final image and check total site coverage, primitive meanings, typed linkage, relaxation preconditions and artifact identity through the required existing validation path. A producer census that ignores linker-introduced code fails.
5. Run the mutations below against their intended judging layer and the exact artifacts. Separate compile-failing stillborn mutations from those that reach a semantic or admission judgment. A survivor is an unresolved finding, not part of the passing denominator.

## Reproduction and measurement protocol

Before producer/trial entry, freeze a reviewed manifest with these required fields. Missing fields leave an incomplete package; justified `n/a` cannot replace a required proof, target or comparator. Record actual artifacts, never fabricated values.

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

Keep [comparator identities](#baseline-identity-and-evidence) fixed; owners freeze actual producer revisions before measurement. Changing a baseline/threshold after results requires a revised experiment, explicit reason and retained old result. Identity/licence accounting includes compiler binary, runtime/primitive closure and copied third-party preambles alongside authored source.

Apply the [target protocol](workflow-contract.md#target-and-production-artifact-protocol) with identical actual profile/Sail closure, memory classes/slots, ABI/call context, generation constants, link policy and eligible transforms. Compare manual, generated unoptimized and generated optimized variants at equal assurance. A secondary unoptimized comparison isolates construction overhead without production-performance credit. Generate shared initial, empty, one-element, boundary, full-capacity, malformed-discriminant, truncated-field, overflow and failure inputs from frozen declarations.

The corpus trace supplies retire order/capability memory effects, not cycles. Timing needs R-18-024/R-18-025's annotation and core class, or an identified instrument with a justified model. Host elapsed time measures proof/build cost; instruction counts measure code/traces. Neither supplies target cycles or WCET. Report SRAM/interconnect/tag effects only from supported observations, without invented cache-miss or silicon-stall metrics.

| Measurement | Predeclared criterion |
| --- | --- |
| Functional behavior, source identity, initialization, authority, failure and leakage guarantees | Exact required correspondence and unchanged assurance assumptions for every variant. Any disagreement is investigated; no tolerance permits a safety difference. |
| Admitted bounds and declared resources | No worse admitted bound or island peak footprint, no larger declared stack/storage/allocation support than the matched baseline, and no displacement of an admitted component. R-18-014's existing constraints take precedence over experimental ratios. |
| Executable target cost and encoded image bytes | The [native-code and cycle thresholds](workflow-contract.md#accounting-and-decision-thresholds) govern final executable code size and each measured case against the equivalent manual baseline. Report total encoded image bytes separately, including padding and metadata; that larger quantity is not substituted for executable code size. Missing cycle evidence leaves that verdict blocked, and a sampled maximum is not a proved worst-case bound. |
| Applicable optimization | Optimized cost is no worse on each declared case and optimized total image bytes are no greater than its unoptimized counterpart, in addition to the resource and assurance criteria. A failed comparison declines this optimization result, not a theorem for an unrelated artifact. |
| Host machine budget | Proposed common experiment caps are four concurrent workers, peak RSS at most 16 GiB, at most 60 minutes per full compiler clean-build or replay run, and eight hours aggregate measured machine wall time per route. The workflow comparison's shorter local source-edit replay limits still apply at that different endpoint. These are stopping limits requiring pre-entry review, not estimates for constructing missing proofs. A limit hit reports an incomplete run. |
| Reproduction and stability | A clean independent lane reproduces each route's final image and checks its evidence under permitted toolchain access. Deterministic target results must repeat exactly. Record a cold run and repeat warm runs until the prescribed workflow sample is complete; do not select the fastest sample or erase contention. |
| Adoption and maintenance | Apply the [accounting thresholds](workflow-contract.md#accounting-and-decision-thresholds) at this full endpoint, with shared establishment and later repair included. A source-level saving cannot pay for an unmeasured machine connection. |

Attribute capability costs by source/site: narrowing/derivation, redundant authority operations, tag-preserving spills/reloads, peak live capabilities, ABI/slot padding, representability refusals and allocation/memory-promotion tag effects. A scalar transform in the merged register file earns no capability-saving label by itself. Distinguish qualified reuse from new proof work in provenance-preserving CSE, coalescing and allocation. Read widths/register organization from the selected profile/model.

## Negative and disagreement cases

Generate variants from selected declarations and emitted sites, recording each intended failure layer before mutation. Source neighbors may fail elaboration; backend/artifact variants must reach the downstream judgment under test. A syntax error supplies no semantic refutation.

| Mutation or disagreement | Required outcome |
| --- | --- |
| Swap equal-width direction/content fields while leaving total size unchanged | The descriptor-layout/source correspondence judgment rejects the changed interpretation. Existing arithmetic reflexivity checks and unchanged emitted bytes alone do not catch Q2a's recorded field-order gap. |
| Move a read before its length guard; truncate the destination; claim an untouched field initialized | Construction or representation proof fails at that access/exit, or final evidence refuses the resulting image. No error status excuses an out-of-bounds read. |
| Convert a capability through an integer, strip a spill tag, broaden a bound or increase permissions | Representation/emission or final Sail/TAL evidence fails even if the low data bits and a host test result agree. |
| Duplicate a live writable loan or omit restoration on failure, loop exit or return | Source resource checking or the binary/frame proof refuses it. Exempting an exit is a changed contract, not a passing mutation. |
| Re-read the source after validation in the staging client | The copy-once/source-stability claim is refuted using distinct first and second images. It is not implemented as a concurrently racing read of a live writable non-atomic buffer. |
| Add a secret-dependent address/branch or an invalid variable-latency operation during optimization | The applicable relational leakage judgment fails even if functional outputs agree. |
| Introduce an unlisted helper/stub, change a sentry role or preserve the wrong register set | Closed emission coverage or typed linkage fails. No unmodeled external-call assumption is appended to rescue the image. |
| Change source resolution/desugaring, a dependency or the representation while reusing an old core proof | `SourcePackage` or a dependent evidence binding is invalidated; a valid theorem about the old core cannot certify the new source. |
| Alter bytes, relocation, composed layout, TAL evidence or primitive mapping after validation | The package fails identity, coverage, typing or refinement at the affected boundary. Independently rebuilding another image does not repair this one. |
| The two routes return different statuses, effects, tags, failures, resource use or allowed observations | Preserve both images and reduce the disagreement against the common source contract and pinned Sail definitions. No route serves as truth merely because it is incumbent or shorter. |
| Both routes agree but the reference contract is weakened or common parsing/layout is wrong | The negative contract cases must still reject; shared parsers, source generation, semantics, proof kernel and validation infrastructure are recorded as common-mode dependencies. Agreement is not independent proof. |

Separately change a client bound, equal-width field interpretation, representation/ABI and admitted optimization. Record unchanged generic replay, changed instance/client proofs, invalidated certificates and attended/machine repair costs. New byte semantics for the reserved client is not generic reuse.

## Pricing and entry conditions

Record human attended hours, agent-session hours, machine wall time, CPU and RSS separately. Price each route at its complete endpoint.

For every row record owner-linked `establishment`, `remaining_port`, `shared_maintenance` and `per_client_repair` intervals: estimates before implementation, measurements at adoption. Establishment includes reusable prerequisites needed for this endpoint; remaining port credits demonstrated artifacts, not historical hours indiscriminately. Unknown work is `unpriced`. Common work has one owner, appears once in each full alternative and is charged once to the integrated plan.

| Obligation | Clight route ownership and credit | Direct route ownership and credit |
| --- | --- | --- |
| Exact source and interpreted core | Shared source and interpretation owners | Same shared ownership and same missing prerequisites |
| Primitive, representation and restoration laws | The `machine-logic`, `byte-instance` and `scoped-resources` owners in [the foundation map](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/cheri-foundation-map.md#foundation-ownership-ledger). Credit checked laws for the selected subjects | Reuse those laws where subjects match. A bounded lemma replacing a construction layer requires an exact replaced obligation and checked substitute; the machine and arbitrary-context portions remain included |
| Decoder realization and source-to-imperative/Clight transport | Q2b owns P and the `source-transport` decision; M7.1 owns S. Use each existing scope once; an excess needs its owner's reviewed extension before entry | The same P/S behavior and baselines are needed. Direct graph-to-IR and representation transport need the compiler owner's separately estimated package; currently unpriced. Reuse the shared source interpretation |
| Capability carrier, permissions, ABI, narrowing and functional backend | M1.2's existing children own the incumbent work; their estimate cells remain canonical and their acceptance evidence determines credit | Reuse only qualified subjects under compatible terms. Direct selection, allocation, emission and composition have no accepted full implementation estimate; currently unpriced |
| Optimization and required target completeness | M1.3/M1.3a and R-18-014's existing owners, with all applicable capability and leakage qualifications | Reuse through those owners if suitable, or obtain a separately estimated port within their required duties. No new speed-only workstream or checker is created |
| Final validation, TAL, source correspondence, leakage and robust preservation | The `context-preservation` and `artifact-admission` producers supply secure-compilation, R-05-023a and TAL evidence | The same endpoint and logic are owed, including an independently checked connection for this route to the arbitrary-context result. Finite emission does not remove their establishment or maintenance cost |
| Linkage, production join and reproduction | Existing assembler/composer and proof owners; measure the checked artifact join | Same owners when genuinely shared; a different ABI/link bridge needs an explicit owner and estimate before implementation |
| Bounded comparison execution and review | Budget the trial against completed prerequisites | Same package and equal experiment caps; route-specific repair is booked separately at the owner of the repaired artifact |

Price the full machine and contextual connection, source and representation
bridges, direct backend, and recurring maintenance before scheduling a trial.
The finite emission family organizes local proofs. Both routes still need
checked machine, byte-instance, scoped-resource, adversarial-context and
artifact-admission results.

### Re-entry packages

For each package, record an owner, inputs, check, consumer and separate
establishment, remaining port and maintenance costs.

| Package and accountable owner | Required output and predeclared check | Join and stopping condition |
| --- | --- | --- |
| Shared foundation and secure-compilation owners | Bind the actual Sail closure and checked constants. Identify any missing implementation for the arbitrary-context and tier obligations. A closed-client theorem or a separate machine without agreement fails the required statement review | Both routes consume one ownership/cost record. Stop if the required common logic or context result still has no defensible scope and price; no direct-route implementation opens to discover it |
| Retained compiler producer | Bind the source, build and digests to the compiler's acceptance predicates; identify reuse by theorem subject, source-to-Clight transport and remaining capability carrier, ABI, emission, optimization and certificate work. Review both P and S at the full endpoint | Join the shared foundation and M1's existing realization. Stop if the full price is inferred from the functional bring-up cell or from unchanged admit counts |
| Direct compiler producer | Supply a file/pass/proof breakdown for graph-to-IR transport, representation, allocation, closed emission and composition; name reused passes, their selected licences, client and generic proofs, and the separate source/machine trace relation. Price its own ABI/link and hardening connections with the common foundation allocated once | Review before commissioning a compiler lane. Stop if a needed semantic rule or context theorem has only a name or an execution cap, or if the bounded family cannot express P's or S's contract |
| Client and baseline owners | Supply executable byte-memory definitions and independent matched baseline evidence under the [workflow contract](workflow-contract.md#freeze-and-independence), with exact failure and initialization behavior. State any scope excess at its existing owner and price only that extension | Qualify the concrete laws and freeze the interface before adapting S once. Stop if S has supplied design feedback or if a core fixture is substituted for either workload |
| Trial and adoption owners | Freeze complete manifests, cost allocation, independent reviewer, target/cycle evidence and licence dispositions; apply this contract's image identity, mutations, closure and the [comparison thresholds](workflow-contract.md#accounting-and-decision-thresholds) | Only accepted producer/foundation packages can release the conditional measurement cell. Unknown historic or recurring cost keeps full-endpoint adoption undecided; it is not silently cancelled as common cost |

<a id="conditional-amendment-and-reviewer-requirements"></a>

## Alternative route approval

[R-05-043](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-043)
requires Clight for synthesized decoders. Approval for another intermediate
requires evidence for descriptor transport, fixed-destination initialization,
copy-once behavior, failures, bounded representation and exact-source-to-Sail
refinement. The route must preserve automated construction and the bounded
runtime contract.

| Existing duty | Evidence or decision owed before any substitution |
| --- | --- |
| R-05-043 decoder synthesis | Checked synthesis and representation chain for the selected decoder family through the proposed intermediate to the required final endpoint, including its error paths and source anchor |
| R-05-019b, R-05-020 and R-05-020a | Both towers quantify over the same Sail-generated definitions. A new authoritative semantics, logic or checker demonstrates R-05-020's bridge, non-duplication and retirement conditions. An untrusted source elaborator instead meets R-05-020a's complete interpretation and exact-source correspondence criteria; this classification supplies no concrete resource law, target compiler or artifact acceptance. |
| R-05-023, R-05-023a and R-13-017 | Final-step refinement in the required CIC-checked Iris-over-Sail logic. Any substitute requires explicit approval and evidence for all of those obligations |
| R-05-024, R-05-026 and R-05-032 | Robust preservation against an adversarial linked context, binary-tier evidence and correspondence to the authored source closure, with the declared leakage and progress claims |
| R-05-023b | Total checking of emitted primitive sites against their profile-bound meanings and applicable TAL rules, without a private instruction semantics or a second consumer checker |
| R-18-014 and its refinements | Retain the named CHERI-CompCert TCB and certifying-Rust deliverables and their full target/optimization/placement duties. A direct generated route counts as neither. Any replacement needs an explicit owner, scope, bootstrap and independence decision at those requirements |
| Typed interoperation and compiler independence | Proved linkage to retained verified-C and Rust components; shared frontend, model, validator and proof dependencies disclosed. A differently named executable is not an independent assurance path |

Review responsibilities: compiler owner, emission/backend facts; foundation owner, theorem subjects/assumptions; source owner, interpretation/failures; target/admission owner, final package/timing. Independent Tier-A review must inspect and replay both routes' proof/IR artifacts at stated revisions. An inaccessible contained dependency blocks that review/reproduction endpoint.

Read selected-file and transitive-dependency licences before incorporation, starting from the [CompCert/SECOMP record](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#compcert-and-secomp) and [tool inventory](../../THIRD-PARTY.md#development-tools-contained-by-use). New files/pins need new readings. Separately qualify inspection/replay, commercial use, compiler redistribution, generated preambles and runtime/helpers. This contract conveys no compiler source or licence grant.

Dependency removal requires its absence from the selected implementation/proof closure; changing IR leaves reused-pass licences intact. Whole-toolchain commercial rebuildability separately disposes of Clight's dual-licensed material, retained TCB/Rust duties, Velus and the oracle environment. A route-local result is insufficient.

## Readiness decision

The comparison remains conditional on the [entry packages](#re-entry-packages).
Treat correspondence, admission, resource evidence and target measurements as
distinct acceptance obligations. Compare cost and performance only once both
arms reach the same declared endpoint. [Backlog](../../PLAN.md#q-assessment-actions)
