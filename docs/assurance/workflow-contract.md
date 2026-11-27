# Workflow and artifact comparison

The [release contract](../language/first-release.md#release-boundary) defines
the language and artifact endpoint. This document defines adoption criteria
and conditional trials for bounded copying and a private linked queue.
[PLAN.md](../../PLAN.md) tracks which work is active.

<a id="commissioning-disposition"></a>

## Comparison prerequisites

A comparison requires a concrete consumer blocked by the retained route, checked primitive/representation laws, reproducible implementations, an independent baseline, and a priced budget with a stop threshold. Record a new suffixed [checklist item](../../PLAN.md#checklist-conventions) before commissioning one. Artifact comparisons target the pinned Sail model; replacing that model follows the [whole-system option](../extensions/unified-source-contract.md).

## First-release qualification and adoption

Assess the [bounded first release](../language/first-release.md#release-boundary) along three dimensions.

| Decision | Acceptance and stop rule |
| --- | --- |
| Technical feasibility | Checked concrete primitive/representation laws plus a source-connected useful component at its declared endpoint. Missing laws, vacuous entry states, or exhausted investigation budgets halt dependent work with a named blocker. A weaker endpoint cannot pass. |
| Recurring developer value | Measure authoring, annotation, review, and repair separately across an independent client, contract change, representation change, and semantics-preserving refactor. Record diagnostics/checking latency, resource costs, and unsupported patterns; hidden manual rewrites or repeated proof reconstruction count against the result. Freeze tasks, baseline, and material-benefit criteria before observing results. |
| Product adoption | Record establishment, shared maintenance, per-client costs, and measured target envelopes. Projected amortization must state workload and uncertainty; two initial small clients need not repay all foundations. Must identify an independently reviewed useful benefit and acceptable recurring cost without weakening mandatory guarantees. |

Candidates must preserve correctness, authority, confidentiality, declared termination/progress, and hard admission limits. Performance comparisons share endpoint and target; selected optimizations may trade code size, cycles, or reserved space inside a separately reviewed envelope—report every affected case/dimension, including regressions. Missing target measurements yield no performance verdict. Do not require universal improvement across metrics or average a safety/hard-budget failure into a passing score.

[Two-client thresholds](#accounting-and-decision-thresholds) apply to the copying comparison; release adoption freezes workloads, endpoint, resource envelope, and thresholds for the actual clients beforehand.

### What a caller can prove from the public contract

Before building the held-out package, its author records required per-exit caller observations with legal inputs, independently expected results, a boundary distinguishing two caller-observable outcomes, and any provider-left choices. To test specification strength: weaken one public law, exhibit a legal input with two weaker-compliant outcomes where independent expectation rejects the wrong one and the original caller proof loses the guarantee, then restore the law and replay that proof ([wrong-store case](#change-and-weakening-probes) illustrates this for bytes).

Freeze the caller's entry domain and resource permissions independently of provider preconditions. Compatible replacements must prove every old legal call satisfies new preconditions and each reachable exit delivers the promised value, resources, effect bound, and termination. Test this by tightening a precondition just enough to exclude a prior witness (for the validator: a readable 3-byte packet and disjoint writable 8-byte destination; requiring 4 bytes removes the framing-error guarantee and disqualifies the interface).

Supply the caller only the published interface (laws and exposed computational definitions). Build/check the caller before and after private provider representation changes, renewing locks and artifact evidence each time. Record repaired provider laws, caller code/proof edits, and any private facts learned; credit proof reuse only when unchanged caller code/proof replays against the frozen interface ([representation comparison](#representation-transfer-comparison) tracks provider proof work).

### Reviewing a public contract change

For releases or package upgrades, diff locked interfaces and evidence to identify, per changed claim, the affected caller and gained/lost premise, observable result, or resource (authority, effects, permitted leakage, progress, resource bounds). Track transitive assumption shifts and responsible components separately; an unchanged signature acquiring a trusted foreign dependency must display that path.

Compatibility requires [caller obligations](#what-a-caller-can-prove-from-the-public-contract) under prior assumptions at the claimed endpoint (new premises may be discharged from them with checked evidence; unresolved ones stay open). Intentional trust/behavior changes follow the [public API evolution policy](../language/first-release.md#public-api-evolution); retain independent behavioral review alongside compatibility so weaker-spec passes remain visible.

Exercise both change kinds across two clients:

- [Packet validator](../language/first-release.md#first-slice-qualification): keep the legal short packet with a valid input, then test requiring 4 readable bytes (lost short-input witness) and contradictory entry bounds (empty entry domain); neither qualifies for the old contract.
- Importing client: keep reachable exit witnesses and a distinguishing wrong result for one weakened promise; replay with the provider opaque; replace one discharged premise with a declared external assumption and check the review names the assumption, affected claim, and broken policy before restoring the original proof/assumptions.

### Cost of the verified abstraction

Compare the held-out client to a handwritten baseline matching behavior, safety guarantees, and resource bounds on the same target, ABI, and backend config. Inventory erased facts versus surviving operations (incoming checks, failure branches, copies, allocation) tied to lowering and the [admitted image](compiler-route-contract.md#equivalent-artifact-endpoint). Inspect lowered calls (and inlined bodies) for erased proof parameters; any extra argument, stored witness, or branch solely carrying a proof fails erasure.

Report code bytes, stack, peak storage, per-case memory traffic, and cycles on agreed success/failure paths with instruments or checked bounds; keep proof-checking time in developer metrics. Missing target measurements or equivalent baselines leave cost comparisons open; apply frozen client thresholds where measured.

### Representation-transfer comparison

The package trial's representation-change probe begins with standard Rocq relations, explicit transport lemmas, and generalized rewriting over a client-needed pure value representation. Freeze public laws, baseline, and repeated steps before comparing automation; reprove changed instance laws, replay generic caller theorems unchanged, and track handwritten transport, generated terms, review, and repair separately. CHERI memory, ownership, and primitive laws keep their foundation owners.

[CoqEAL/Trocq candidates](verification-strategy.md#existing-tooling-and-implementation-owners) become options only if that baseline exposes recurring automatable work and a new checklist item prices their prover/plugin closure, port, licence reading, and maintenance under the locked prover/assumption policy. Stop on budget exhaustion, unresolved compatibility/assumptions, or missed predeclared maintenance-benefit criteria (retaining native transport and checked lemmas). Generated proofs must establish the exact same relations and client laws without stronger preconditions or weaker results.

## Clients and baseline evidence

**P (parser destination initialization)** is copy-once ring-descriptor check with bounded fill of a fixed destination; **S (private service staging)** is held-out sequential disjoint copy into private storage.

Use the [VerifiedOS foundation map](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/hardware/cheri-foundation-map.md) for producers, representations, and gaps; [DescriptorCheck](https://github.com/symbiogenesis/VerifiedOS/blob/main/tools/bedrock2-lowering/DescriptorCheck.v) models the read-only header check, and [CopyRingService](https://github.com/symbiogenesis/VerifiedOS/blob/main/proofs/CopyRingService.v) specifies abstract read counts/extent. Entry requires runnable byte-copy baselines at the endpoint, checked CHERI byte and scoped resource laws, and actual ring/staging declarations. Freeze immutable revisions and digests; mark missing inputs `unavailable`.

### Freeze and independence

For P, freeze operational definition, intended behavior, implementation, theorem subjects, and assumptions before adaptation; baseline author works independently of generated output, and authoring costs require contemporaneous records.

For S, freeze and hash interface, generic theorems, concrete instance, and qualified environment before adaptation. If S informs the interface, reclassify it as development and name a fresh held-out consumer, owner, baseline, and budget with independent pre-observation review.

Name experiment author, baseline author, and a reviewer independent of implementations and oracle checks; observe [licensing rules](../../COPYRIGHT.md#terms-this-tree-does-not-carry) for incorporated tools.

## Operational subset and observations

The pilot uses sequential, total, bounded byte-buffer code: fixed destination capacity, runtime length, erased bounds evidence, explicit failures, and a callback-shaped scoped loan. Each candidate has one authoritative executable definition and independently reviewed behavior; generated implementations, representations, and proofs carry provenance and are regenerated, never hand-repaired.

Keep runtime branch inputs (lengths, discriminants). The representation relation defines byte order, integer widths/overflow, capability provenance/bounds/permissions, initialization, layout, and abstract-owner/concrete-byte correspondence, connected to admitted CHERI semantics (not generic byte or printer-assigned models).

Freeze declaration-owned capacity `C`, stable readable source extent, exclusive capacity-`C` destination, and disjointness witness for both clients. Verify representations of `C`, indices/lengths, receiver-relative bounds, and unexecutable symbolic overflows; derive target input sizes from the frozen owner without duplicating layout constants.

### P: composed positive client

P combines the selected mechanisms in one executable definition and theorem:

1. Enter a scoped callback with destination owner, stable source read authority, and runtime length `n`; validate `n` against source extent and `C` before any source read, destination index, or pointer calculation.
2. Zero-fill the entire destination using a total repeatable callback returning `0`, capturing only stable public values with no competing destination loan, allocation, or external effect (invocation count matches destination bound; capture and write permissions proved separately).
3. On invalid `n`, return the declared invalid result with the initialized destination owner restored. Otherwise copy the source prefix once into the private destination and run descriptor validation strictly against the private destination.
4. Return success carrying runtime `n`, its bound witness, and initialized destination owner, or invalid carrying the initialized owner and failure evidence. Neither exit leaks the scoped loan or alters destination capacity, and success excludes session-table validation left to the receiver.

Every exit preserves source and unrelated frame, fully initializes the destination, and restores ownership once. Admitted `n` yields sampled prefix followed by zeros (even on invalid headers) matching `Descriptor.descriptor_check`; rejected `n` yields all-zeros and reads no source byte. Resolve failure-write differences pre-freeze.

Exercises R-05-124 destination initialization, R-12-012a receiver validation, and selected descriptor encodings; full parser, session validation, cross-compartment init, Byzantine peers, and atomic-snapshot theorems remain out of scope.

### S: held-out staging client

S applies the frozen generic disjoint-copy interface to private staging. Its baseline locks M7.1's lifetime, capacity, initial state, result, and exact failure status against `svc_op_record` (left open in the statement artifact). Freeze payload extent `d` separately from storage capacity `C`, prove `d <= C`, and test both boundaries (staging slack allows no larger payload). From an initialized destination, copy admitted `n` bytes preserving suffix, source, and unrelated frame, returning the owner on both success and failure; rejected lengths/extents refuse with no source read or destination write.

Success payload equals the first acquired source prefix (verify `copy_once` by varying a modeled later image with fixed prefix). Adversarial atomic snapshots, concurrent SPSC, publication, notification, cancellation, DMA, and revocation require separate connection evidence.

Compare each client strictly to its matched baseline (preserving P/S init differences); generic operations must support both without client-specific CHERI facts in the generic theorem.

## Selected composition and rejection cases

Every row below must compose in P; missing mechanisms mark the trial unavailable until separately owned and priced (isolated feature examples supply no evidence).

| Interaction in P | Positive obligation | Well-formed negative neighbor and intended failure |
| --- | --- | --- |
| Stable indices and erasure | Runtime `n`, fixed `C`, erased `n <= C` witness in bounded copy; retain success/error tag | Erase `n` while branching on it, or reuse bound witness after changing bound: fail phase/stale-bound check |
| Mutation and dependency | Fill/copy update contents while preserving shape; consume old content facts | Justify final payload from pre-fill snapshot: fail memory representation or postcondition |
| Scoped loans and results | Both branches return full owner and end loan | Return loan in error payload, or error without owner: fail escape/restoration |
| Reusable callable, effects and count | Invoke zero-byte callback across loop indices with permitted captures, no external effect | Call consuming callable twice; hide captured destination write/alloc; alias capture with exclusive output: fail usage/effect/disjointness |
| Typestate and branch joins | Fill establishes whole init before either exit; result variants carry distinct bound/status facts | Skip fill iteration yet claim whole init, read uninit byte, or claim success on error: fail init or branch postcondition |
| Name and instance resolution | Local renames, qualified buffer ops, and unrelated imports preserve resolved constants | Silent representation/effect instance switch: require preserved meaning or explicit ambiguity |
| Dependent computation and automation | Compute bounded cases; replay equation lemmas and exact transitive assumption audit | Global UIP, open generated obligations, or stuck concrete term: fail assumption, completeness, or computation |

Use the locked prover's existing definition/conversion rules (proved equality for the selected decidable index is allowed; global axioms are not). Saved search reconstructions must replay without the search service.

Straight-line borrow inference, returning a loan beyond the callback, disjoint-field/nested reborrow inference, resizing, suspension, cancellation, handlers, concurrency, general grades, and a new frontend are **unavailable in this pilot**. General isolation, observation policy, and binary-leakage composition are **outside its source claim** ([core design](../language/core-design.md) covers wider mechanisms); SPSC, DMA, and atomic snapshots are **inapplicable to the sequential slice**, not proved absent.

### Expected behavior, witnesses and mutations

Before candidate proofs start, an independent reviewer freezes expected bytes/status and checks from contract/format (never treating the candidate as its own oracle). Supply inhabited entry states covering:

- Empty, 1-byte, full, and `C + 1` inputs (S also tests `d` and `d + 1` with nonzero staging slack; P covers all operation variants and truncated field positions).
- Last valid and first invalid indices; malformed tag, direction, content, and optional-deadline discriminants; invalid flag; distinct distinguishable byte positions to catch swapped reads/stores.
- Receiver-relative offset/length boundaries and word-width wraparound (retain proof case and report unexecutable large cases as unavailable rather than shrinking inputs).
- Destination residue distinct from source bytes, nonempty surrounding frames, adjacent disjoint ranges, and rejected overlap; verify source and frame bytes on all exits.

Freeze syntactically valid wrong-store, off-by-one, omitted-fill, bad-failure-result, and second-image mutations reaching target obligations; classify malformed/stillborn, intended kill, unrelated failure, timeout, unsupported, and survivor (any survivor fails). Use [oracle, seed and QuickChick](https://github.com/symbiogenesis/VerifiedOS/blob/main/tools/README.md#the-three-generators-and-what-each-answers) where supported with independent spec review and test guards kept out of theorem premises. Name per-guarantee theorems (dropping a frame theorem while keeping op laws must fail P); profile flags and source ownership alone give no adversarial isolation.

### Change and weakening probes

Shrink P's accepted bound from `C` to `C - 1` (nonzero `C`, needing an inhabited `n = C` witness). Old claims/cached feedback must turn stale/fail pre-repair; re-review expected tables, regenerate, renew source/representation/artifact evidence, record all edits, and apply the same edit to baseline before comparing repair cost.

Drop S's copied-prefix equality while keeping bounds, init, frame, and status: wrong-store passes the weaker spec but must fail independent nonuniform expected-byte checks (otherwise record a spec gap and refuse; inhabitance, proof completion, and memory safety cannot close it).

Test semantics-preserving local rename + helper extraction, unrelated import, and law-preserving instance representation change: reprove changed instance laws and replay generic theorems unchanged. Separate saved-term replay from tactic/search rediscovery (seed, limit, reconstructed proof). Changed source maps, constants, representations, contracts, or dependencies invalidate evidence despite unchanged goal spelling; new holes, admissions, or undeclared assumptions fail R-05-018a/R-05-018b under exact R-05-163.

## Measurement record and sampling

Generate a readable report from machine logs retaining raw logs, units, predicates, instrument revisions, and uncertainty (`unknown` = missing, `n/a` = inapplicable; never zero).

| Record family | Required identity or observation |
| --- | --- |
| Trial | Contract/review revision, P/S identity and development/held-out status, named authors/reviewer, entry decision, case selection |
| Source | Baseline/candidate source closure + commit; operational def + independent behavior; representation/erasure; source maps, resolved names, elaboration/desugaring, imported contracts |
| Proof | Rocq/library/plugin versions + config; interface/instance digests; theorem constants + transitive assumptions; batch, assumption, `rocqchk` evidence; search seeds/limits |
| Target | Profile, pinned Sail term/config; compiler, optimizer, assembler, linker, composer versions/flags; ABI, link context, layout; memory classes/slots; final image + evidence digests |
| Effort | Event records (setup, learning, authoring, review, failure diagnosis, regeneration, proof repair, shared maintenance); diffs across source/contract/glue/proof; duplicate executable tracking |
| Host measurements | Diagnostic latency; cold and warm batch/kernel replay elapsed, CPU, max RSS; worker count, machine, cache state |
| Target measurements | Per-case code bytes, stack, peak storage, alloc/runtime support, memory accesses, target cycles with derivation/instrument |
| Decisions | All positive/negative outcomes, first failed obligation, mutation class, change invalidation, spec-gap status, endpoint cost comparison, decision |

Record UTC event ordering with monotonic intervals (`actor`, `owner`, `category`, `start/end`, `id`); pause authoring during unattended builds, charge diagnosis separately, keep overlaps unsummed, and log all agent attempts plus integrator review.

Observe authoring and held-out adaptation once with original logs (learned repetition invalidates independence). Time batch artifacts via 1 cold + 1 unreported warmup + 5 warm runs; replay positive/edit/negative diagnostic sequences 5x alternating workflow order; report raw durations, nearest-rank p95, median, max, and environment IDs (re-run only interrupted rounds, labeling both). Diagnostic latency spans edit completion to source-bound feedback on first unsatisfied obligation (`stale`/`unfinished` resolve no obligation; timeouts keep `timed-out`, not cached success). Batch/latency timings never substitute for acceptance or authoring effort.

Compare C#/Dafny and Rust/Verus only on matching bounded algorithms/behaviors, logging unsupported features, manual restoration, and endpoint (weaker endpoints allow navigation/location/latency comparison only, never CHERI authoring claims; commissions no install, port, or LSP).

### Proof search and replay under change

Before the first edit, freeze interactive inference, batch search, and kernel replay limits, enabled [checking tiers](verification-strategy.md#layered-proof-and-staging), and solver settings; exhausted searches emit the residual proposition at its source site, local facts, and hit limit so authors can supply a matching lemma. Record time to first feedback, remaining goals, proof diffs, and fresh replay time (hosted apps set custom limits; copying pilot uses [existing thresholds](#accounting-and-decision-thresholds)).

For the packet and independent package trial, track per-goal discharge methods, consumed defs/instances/assumptions, replayable certificates, and exact source/target/checker bindings, exercising:

1. Replay saved evidence cleanly with search off; log certificate replay separately from proof discovery.
2. Change a semantic dependency while preserving goal syntax: show staleness pre-replay; replaying an old certificate for a different proposition must fail at that obligation (cached success flags prove nothing).
3. Exhaust automatic search on a provable goal; insert the missing lemma at the reported site and replay within the same limit.
4. Reprove a private provider representation preserving public laws and recheck the unchanged caller; report rediscovered vs replayed proofs and per-side repair effort under [invalidation rules](../language/core-design.md#typed-holes-and-invalidation).

## Accounting and decision thresholds

Freeze selection thresholds pre-run; protocol changes require a new identity and fresh runs.

| Parameter | Threshold | Ground and interpretation |
| --- | --- | --- |
| Correctness and evidence | All positives hit endpoint; all negatives fail intended obligation; zero new assumptions, stale accepts, or undetected weakenings | Conjunctive guarantee; safety failures never average out |
| Interactive diagnostic latency | p95 <= 2 s on frozen incremental sequence | Local edit-loop usability distinct from batch replay cost |
| Replay limit | Warm <= 10 min; cold <= 30 min | Bounds edit/rebuild loop (timeouts stay undecided; repeated timeouts reject adoption) |
| Held-out recurring effort | Candidate upper bound <= 0.90x matched baseline lower bound (incl. learning, adaptation, review, probes) | Predeclared margin above recording uncertainty, not a forecast |
| Full accounting boundary | Conservative `NetSaved` > 0 at endpoint | Both pilot clients must repay attributable setup and shared work pre-expansion |
| Native footprint and runtime support | Stack/peak storage <= baseline; zero new alloc/runtime support; hard bounds unchanged | Prevents buying speed with a larger resource envelope |
| Native code and cycles | Executable code size and per-case cycles <= 1.05x baseline; zero hard-bound regressions | Experimental ratio exposing per-dimension failures |
| Selected optimization | Cycles <= unoptimized on all cases; total optimized code bytes <= unoptimized | Retains only Pareto-dominating optimizations unless separately reviewed |

Account from the first attributable qualification/interface event through P, S, and change probes at the endpoint; close the source ledger first, then add measured artifact work (no credit for unmeasured consumers/targets/edits). Use the strategy's [break-even equation](verification-strategy.md#where-time-might-be-saved) with unique term owners:

| Term or shared cost | Unique owner and treatment |
| --- | --- |
| Library/interface establishment `L` | Proof-tool qualification, interface design, initial learning counted once |
| Shared maintenance `M` | Common interface/tooling owner; client repair stays on client series |
| Concrete instance `P_j` | Concrete/foundation work counted once at consuming endpoint (investigation separate from implementation) |
| Baseline client effort `B_i` | Q2b (P) and M7.1 (S): matched source, proof, review, maintenance, baseline prerequisites |
| Candidate client effort `A_i` | Measured adaptation + maintenance incl. learning, integration, review (S shared adaptation counted once) |
| Representation, lowering and final evidence | Representation/lowering/optimization/artifact producers' evidence; artifact comparison pays own integration |

Separate full establishment, post-freeze remaining work, and recurring maintenance; count common foundations once via transparent allocation; keep sunk baseline costs intact (another owner's needed source-to-byte work is not sunk); missing history makes full-establishment comparison `unknown`.

Keep human attended hours, summed agent hours, machine elapsed, CPU, and calendar duration unmixed, stating series/endpoint per claim (conservative `NetSaved` pairs baseline lower bounds with candidate/setup/maintenance upper bounds; missing bounds -> `unknown`). Declare predicates for duplicate executable files/changed operational lines (accepted candidates keep no manual second implementation).

Correctness/evidence failure rejects integration; missed effort/native thresholds reject expansion at that endpoint while keeping component proofs; missing logs/unsupported interactions/insufficient timings leave the trial **unopened or undecided** (unmeasured future projections never shrink estimates).

## Target and production artifact protocol

Freeze a P/S-capable CHERI target and producer closure under the provisional profile and compiler duties, recording revisions, full options, representation, ABI, code/data placement, memory classes, link env, and schedule (missing fields block comparison).

Match target, backend, and env identically across manual/generated pairs (incl. refused inputs); compare optimized vs retained unoptimized output from the same source closure varying only eligible optimization switches (cross-backend comparisons belong in [compiler-route comparison](compiler-route-contract.md)).

Measure code bytes, stack, per-class peak storage, runtime/alloc support, and memory/capability traffic alongside functional model behavior. Cycles require a timing-annotated model (not retirements, host wall time, or unqualified counters). Replay deterministic initial states verifying identical results/cycles; worst-case claims need exhaustive finite coverage or checked bounds (sampled maxima and symbolic overflow proofs are not WCET).

Requires accepted workflow results, reviewed fault model where applicable, and compiler/optimization/assembly/link/image/admission evidence at the [exact artifact endpoint](compiler-route-contract.md#equivalent-artifact-endpoint). Promote the exact exercised optimized image bound to fresh source, image validation, admission, resource, and security evidence (any byte/relocation/link/config change invalidates and blocks until renewed; digest checks identity only; never recompile/patch/rewrite accepted bytes).

Apply [Q1's limits](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/implementation/contracts/product-gate.md#2-the-limits) keeping `host_elapsed`, `target_model_cycles`, `fpga_observed`, and `silicon_measured` separate (latency/operating-point evidence needed to convert cycles to wall time; pilot proves no unexercised product workload).

## Review and evidence endpoints

Verify inhabited witnesses, intended-obligation failures for negative probes, and wrong-outcome rejection on frozen expectations. Levels: **source-verified** (source proofs), **artifact-connected** (+ lowering/link relation to exact final bytes), **production-qualified** (+ admission, resource, security, target evidence; hardware refinement and silicon sit outside).

## Private linked queue trial

The [post-release trial](../../PLAN.md#q25ea) models an independent FIFO client enqueuing owned values, borrowing the front element, and dequeuing (full enqueue returns offered value preserving queue; public interface exposes capacity, sequence, per-exit ownership). Pool uses address-stable nodes with private capability links (head and tail may alias on a singleton); prove live chain models public sequence, tail terminates it, slots partition into live chain vs free pool, and front views hold a loan on live payload.

Freeze witnesses across empty, singleton (drain, slot reuse for new value, multi-value enqueue/drain), multi-node, and full queues checking FIFO order, returned ownership, and unrelated frame. Exercise live front-view use across removal (require diagnostic naming removal + conflicting view), ending the view pre-removal, corrupting tail-to-freed-singleton (must fail invariant proof), slot-order change (reprove provider laws, replay client unchanged).

Compare at equal capacity, guarantees, target, and admission against an independent baseline across loads, stores, branches, runtime calls, code bytes, peak storage, capacity checks, abstraction overhead, provider vs caller effort under the [measurement protocol](#measurement-record-and-sampling) with frozen thresholds. Concurrent readers require a separate estimate under [sharing and reclamation rules](../extensions/interior-mutability.md#immutable-publication-and-reclamation) (delayed reader holding published value across writer reuse; linearization, ordering, quiescence; sequential trial keeps links private).
