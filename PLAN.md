# HoldFast Plan and Backlog

## Current execution

**The next milestone is acceptance of the packet validator's exact executable.**
Its source proofs already cover byte values and the returned view with zero
solver-trusted obligations. [Authored validator](examples/first_slice.hf) · [Artifact acceptance](#q25ba)

The VerifiedOS producer records at commit
`e1a50804e5d487500d44bc4e8484adeead307e5c` report a strict Rocq 9.3.0 replay of
the canonical hart-0 Sail term (`rv64d.v`) with private tag-outcome support.
The recursive kernel context matches the 31 classified floating-point axioms,
and the stock and patched emissions have identical readings for all 3,533
main-module declarations on that support. [Producer record check](docs/assurance/completion-log.md#q25ar-integrate-and-recheck-prerequisite-producer-receipts)

Two sequential generation runs for each plugin set reproduced the C++ source,
header and configuration schema. VerifiedOS accepts the comparison for the
frozen emulator-isolation inputs and requires a repeat for any revised inputs.
[Emulator isolation check](https://github.com/symbiogenesis/VerifiedOS/blob/314bd47d6e5ab398afe9f4af636a54b1a58502dd/docs/implementation/contracts/canonical-tag-outcomes.md#emulator-isolation-check)

Resume [Q25am](#q25am) when `machine-logic` supplies Q35p binding qualification,
Q35o immutable emitter qualification, Q35n and Q35q production support, and
Q35b's whole-term replay and assumption closure on that support. The decision
on the 31 floating-point axioms remains open under F-480 (R-05-164).
[Q35 emission requirements](https://github.com/symbiogenesis/VerifiedOS/blob/fd6e2ba3fd862bc3c6baba08bcc772dbf3507ccd/docs/assurance/sail-rocq-emission.md#remaining-acceptance) ·
[Q35p binding requirements](https://github.com/symbiogenesis/VerifiedOS/blob/314bd47d6e5ab398afe9f4af636a54b1a58502dd/docs/assurance/sail-memory-bindings.md#bound-and-remaining-acceptance)

The retained `holdfast-parser first-slice` result names the blocking producers in
`inventory.blocking_dependencies`. [First-slice qualification](docs/language/first-release.md#first-slice-qualification)

Advance graded checking and proof-backed borrowing in parallel with artifact
qualification. Carry separate computation and type-use demand through callable
interfaces and dependent eliminators on the ordinary build. Extend the locked
first-order replay to higher-order and box interfaces, then connect those
derivations to evaluation and erasure using the graded laws.
For borrowing, qualify path-specific loan liveness and proof-backed separation
in owner coordinates on independent clients. Compare direct source, invalid
edits and safe rewrites against the pinned Rust modes and the implemented Ante
subset. Extend the checked resource replay to lending and loop exits.
[Graded laws](#q25be) · [Graded frontend](#q25bj) · [Borrow comparison](#q25cc)

### HoldFast first-release delivery

Take the smallest checked result a release client can use. A consumer can start as soon
as the part of an interface it needs passes its checks. If an input is missing, record
the owner and the evidence needed to resume, then take another row whose inputs exist.

| Available input | Work it unlocks |
| --- | --- |
| Canonical term and compatibility evidence | Establish the machine interpretation ([Q25am](#q25am)), then the concrete byte and scoped-loan laws ([Q25an](#q25an)). |
| Machine and resource laws for the validator | Two paths can proceed in parallel as their inputs arrive. Prove the core laws and publish checked frontend correspondence ([Q25as](#q25as), [Q25at](#q25at)). Connect the retained compiler to Sail, prove contextual security, then obtain first-client image admission ([Q25ao](#q25ao), [Q25ap](#q25ap), [Q25aq](#q25aq)). |
| A producer publishes a checked result | Bind it to the exact inputs as it arrives ([Q25ar](#q25ar)). Join the first-client receipts to the existing narrow lowering to accept the validator ([Q25ba](#q25ba)). Wider frontend, admission and receipt coverage can stay open. |
| Checked frontend results | Diagnostics can consume checked derivations ([Q25au](#q25au)). The repair trial constructs its fixture from the core laws, checked frontend and concrete resources ([Q25av](#q25av)). The mathematical frontend builds locked packages against the frozen module and instance rules ([Q25ax](#q25ax)). |
| Accepted validator | Publish the scalar and text representations ([Q25aw](#q25aw)). Use the required primitive laws to build the ownership libraries ([Q25ay](#q25ay)). General lowering consumes published representation laws and returns a checked receipt for each operation, so each library can finish qualification ([Q25az](#q25az)). |
| Core loan and effect derivations, locked package graph | Qualify implicit `ref` receiver reservations ([Q25cd](#q25cd)) and inference for package-internal effects ([Q25em](#q25em)) before the supported release. |
| Natural grade derivations, checked source and resource interpretations | Qualify [default graded checking](docs/language/first-release.md#default-graded-checking) through [Q25be](#q25be), [Q25bj](#q25bj) and the [graded client replay](#q25by). |
| Checked loan derivations, concrete resource laws and frozen comparison inputs | Qualify [default borrow checking](docs/language/first-release.md#default-borrow-checking) through the [held-out comparison](#q25cc) and [loop borrowing](#q25cf). |
| Independent second client and baseline | Freeze the public observations, resource envelope and benefit thresholds before adapting the client. When its packages, libraries and lowering qualify, run the trial and obtain its own admission receipt ([Q25bb](#q25bb)). Close shared coverage across both clients, publish the reproducible release, then rehearse one upgrade ([Q25bc](#q25bc), [Q25bd](#q25bd)). |
| Independent hosted application and pinned host | Freeze the application, ABI and baseline ([Q25eh](#q25eh)). Use the common language rules and qualify the hosted runtime and bindings through their own evidence endpoint. Exercise the actual application workflow and recovery once those interfaces qualify ([Q25ei](#q25ei)). |

Use each item's **Start** and **Check** for the precise inputs and acceptance decision.
Existing parser, math and editor work can finish its frozen qualification. A language
investigation can start with the inputs for its declared evidence endpoint. Promotion
to broader language and adapter support needs the synchronous component and a named
consumer that meets the option's entry conditions. The [release boundary](docs/language/first-release.md#release-boundary)
and [qualification criteria](docs/language/first-release.md#qualification) define the supported endpoint.

### Feedback while implementing a slice

Start a bug fix with the smallest case that fails through the affected entry point.
For a contract change, establish an independently expected success and a nearby case
that reaches the intended refusal. Exercise the consumer that depends on the distinction.
Keep a minimized generated failure as an ordinary replayable fixture.

Use `python tools/run.py` (`python3 tools/run.py` on Linux) with the command that answers
the question at hand.

| Question | Command and evidence |
| --- | --- |
| Does the changed behavior pass its regression cases? | `test --only <module-substring>` runs matching modules, for example `test --only first_slice`. |
| Which inputs or edit sequences break the parser or editor? | `holdfast-parser syntax-campaigns` compares generated pure syntax with independent expected trees. `holdfast generated-tests` shrinks editor-state and formatter failures. Use `holdfast-lsp --qualify-clients` for a change to real-client behavior. [Parser campaigns](docs/tooling/parser.md#generated-syntax-campaigns) · [Generated tests](docs/tooling/tooling-protocols.md#generated-development-tests) · [LSP clients](docs/tooling/lsp-prototype.md#acceptance-and-remaining-qualification) |
| Do the proofs still hold? | `holdfast-parser elaborate-qualify` replays the elaboration fixtures in Rocq. For the validator itself, `holdfast-parser first-slice` produces fresh local proof and execution evidence. [Elaboration replay](docs/tooling/elaboration-prototype.md#commands-and-acceptance) · [First-slice qualification](docs/language/first-release.md#first-slice-qualification) |
| Does a retained validator receipt still match? | `holdfast-parser first-slice-bindings <receipt.json>` checks identities. A changed proof, compiler or artifact needs fresh evidence from the producer responsible for that claim. [Receipt checks](docs/language/first-release.md#first-slice-qualification) |

Before writing a proof, test or adapter, look for a reusable library law, generator
or compiler fact. Profile a slow check before optimizing it. Try candidate tools on
the actual case, such as a solver that can generate a term for kernel replay. Prefer
the tool that shortens feedback, removes repeated work or catches more defects at the
same acceptance boundary. Include setup, review and upkeep when adopting a dependency,
then pin and qualify the selected version. [Tool reuse criteria](docs/assurance/verification-strategy.md#where-time-might-be-saved) ·
[Dependency policy](tools/README.md#dependency-and-version-policy)

Check reported skips against the affected guarantee. Run the owning native or
independent-client qualification when that guarantee changes. Each client needs
its own artifact evidence. [Validation profiles](tools/README.md#validation-profiles) ·
[Local handoff](AGENTS.md#tool-execution-and-validation)

<a id="checklist-conventions"></a>

## Checklist items (Q25 series)

Record status here and keep each leaf's estimate, range, class (`I` for
implementation, `X` for investigation) and actual hours in its single row in
the [calibration record](#calibration-record-q25-series). The completed batches
used parallel agent sessions. Enter `n/a` when a batch's actual hours cannot be
attributed to a leaf.

Link each landed or struck item to one [completion-log](docs/assurance/completion-log.md)
entry with the exact `Q25* · Title` heading. A partial result keeps its parent
open until the parent's acceptance conditions are met.

### Shared foundation and retained route

<a id="q25am"></a>

- [ ] **Q25am · Establish the selected machine-logic interpretation and adequacy**
  - **Owner** `machine-logic`
  - **Start** Use the canonical Sail term and Q35 compatibility evidence supplied by the external producers.
  - **Check** Provide a checked operational and resource interpretation, adequacy and observation interfaces for the selected synchronous subset over that exact term. Replay inhabited byte and invalid-operation cases. The budget covers residual work beyond the booked Q35 slices.

<a id="q25an"></a>

- [ ] **Q25an · Establish concrete byte and scoped-resource laws**
  - **Owner** `concrete-resources`
  - **Start** Use the [machine interpretation](#q25am) and the existing byte-instance and scoped-resource producers.
  - **Check** Prove CHERI read, write, frame, initialization, split/join, nested loan, restoration and returned-view laws over the admitted machine carrier. Reuse the source-level `Span` and `Slots` laws from Q25af, Q25ag, Q25ak and Q25al.

<a id="q25ao"></a>

- [ ] **Q25ao · Close the retained source-to-target compiler refinement**
  - **Owner** `retained-compiler`
  - **Start** Use the [machine interpretation](#q25am), [concrete resource laws](#q25an) and retained Q35d, M1.2g and Q35j compiler producers.
  - **Check** Prove refinement from the selected Clight representation and purecap ABI through the retained compiler to canonical Sail execution. Cover calls, loops, failure exits and composition. The budget covers residual proof and compatibility work beyond the booked compiler slices.

<a id="q25ap"></a>

- [ ] **Q25ap · Establish contextual security preservation for the release closure**
  - **Owner** `context-preservation`
  - **Start** Use the [machine interpretation](#q25am), [retained compiler theorem](#q25ao) and an independently reviewed contract for observations and adversarial contexts.
  - **Check** Prove authority, confidentiality and contextual preservation at the selected endpoint, including linking, callbacks, leakage and resource assumptions.
  - For the packet entry point, identify who establishes descriptor validity before the first metadata read. Prove the calling mechanism excludes invalid descriptors from untrusted linked callers, or qualify an adapter that checks them and charge its runtime costs. In the adapter case, supply an invalid descriptor and check the specified refusal or isolation outcome. [Validator entry contract](docs/language/first-release.md#first-slice-qualification)

<a id="q25aq"></a>

- [ ] **Q25aq · Close TAL and exact-artifact admission for the release closure**
  - **Owner** `artifact-admission`
  - **Start** Use the [compiler](#q25ao) and [contextual preservation](#q25ap) theorem interfaces and the existing TAL and image-validation producers.
  - **Check** For each client, compose the TAL/checker soundness proofs with assembly, link and image validation and applicable binary constant-time and resource evidence. Reject stale, changed and malformed artifacts. Publish the validator's independently checked admission receipt as soon as it passes. Close after both clients have exact-source-to-final-byte admission.
  - On the release image, exercise an out-of-profile instruction in a reachable error branch that the passing input skips. Require the image checker to identify its address and encoding even when the passing trace agrees with the original. The [local control regression](docs/assurance/compiler-route-contract.md#equivalent-artifact-endpoint) exercises this case on the handwritten scalar controls.

<a id="q25ar"></a>

- [ ] **Q25ar · Integrate and recheck prerequisite producer receipts**
  - **Owner** `producer-receipts`
  - **Start** Identify the revisions of the local and externally supplied producers.
  - **Check** Bind each independently checked receipt to its source closure, canonical model, assumptions, tool versions and target. Replay locally and review applicable user-supplied Host CI and Guest CI verdicts. Missing receipts and skipped or canceled runs leave their guarantees pending. Publish the validator's receipts before the second-client trial. Close when every declared producer and client is covered.
  - Apply the [deployed-claim evidence](docs/assurance/compiler-route-contract.md#evidence-for-each-deployed-claim) binding at both client endpoints. Substitute a host packet run for view-authority evidence on the deployed image and require the report to identify the missing target claim.
  - Local bindings check the capacity and control sources, proof-corruption refusal, Sail capability images and complete simulator traces, and optional CompCert processes, effective inputs and images. The packet binding result names the missing deployed functional and view-authority evidence. External producer receipts and artifact admission remain open. [Partial evidence](docs/assurance/completion-log.md#q25ar-integrate-and-recheck-prerequisite-producer-receipts).

<a id="language-core-proposals"></a>

### Supported-release implementation

<a id="q25as"></a>

- [ ] **Q25as · Prove the synchronous core interpretation and composition laws**
  - **Owner** `core-soundness`
  - **Start** Use the [concrete resource laws](#q25an) and the admitted interpretation of the elaborated image.
  - **Check** Prove substitution, preservation, phase separation, authority and effect composition, and loan restoration on every exit. Show which facts survive a write. [Core obligation matrix](docs/language/core-design.md#proof-obligations-and-proposed-work-packages) and [borrow-analysis rules](docs/language/core-design.md#borrow-analysis-promotion).
  - Prove [inline proof isolation](docs/language/core-design.md#inline-proofs-and-runtime-state) with initialization, ownership, loan and verdict duties in the judgment. Replay a caller with a real initializer and its proof-only neighbor. An independently checked postcondition of the initializer must confer no runtime write on the second caller.

<a id="q25at"></a>

- [ ] **Q25at · Qualify checked synchronous frontend correspondence**
  - **Owner** `core-frontend`
  - **Start** Use the [core-law interfaces](#q25as) and existing checked parser and elaborator, including mathematical elaboration, owned loans and effects.
  - **Check** Implement and independently qualify correspondence between the exact `SourcePackage`, its interpreted core and frontend erasure. Check resolution, reconstruction and arithmetic, loan, capture and effect derivations. For every partial word operation in the qualified subset, bind the guard proof to its source span, checked operand representation and emitted primitive. Report unknown facts and exhausted analysis budgets. Publish the checked validator subset as soon as it passes. For release qualification, compare inferred and explicit clients at the same interpretation and artifact endpoint, covering literal boundaries, ambiguous instances and unstable indices. [Contextual inference](docs/language/first-release.md#contextual-inference).
  - The [word-equation replay](docs/tooling/elaboration-prototype.md#commands-and-acceptance) covers guarded operations on wider symbolic operands. Fifteen independent consumer equations replay against their source-span theorems, including signed addition and subtraction with symbolic bounds. Whole-frontend correspondence remains open. [Arithmetic evidence](docs/assurance/completion-log.md#q25at-qualify-checked-synchronous-frontend-correspondence).
  - Across a locked interface, instantiate public guarantees at their declared arguments, discharge each premise with a proof in scope, and replay the resulting term with the implementation opaque. Cover a result that is itself callable. Changing an argument to that returned function cannot supply evidence for the producer's precondition. [Package proof composition](docs/tooling/elaboration-prototype.md#client-upgrade-replay) The locked mathematical fixture replays both opaque calls and the returned callable. Its isolated control refuses when the returned callable's argument meets a premise that the producer's argument violates. [Locked-client evidence](docs/assurance/completion-log.md#q25at-qualify-checked-synchronous-frontend-correspondence).
  - [Pattern test scope](docs/language/surface-grammar.md#pattern-test-scope) in implications replays the consequent under successful antecedent bindings. The native controls refuse a binding under disjunction and a reference outside the implication. [Pattern scope evidence](docs/assurance/completion-log.md#q25at-qualify-checked-synchronous-frontend-correspondence).
  - Extend inline proof reconstruction over the release arithmetic fragment. Replay a bound that follows from a branch guard and its negated neighbor against that exact path, including strict comparisons. When reconstruction runs out of evidence, report the outstanding proposition at the assertion and allow an explicit lemma to supply it. [Kernel boundary](docs/tooling/elaboration-prototype.md#commands-and-acceptance)
  - Inline assertions replay ordinary `Nat` comparison guards on their branches, join scoped bounds by transitivity and preserve the order under common addends. The controls refuse a changed guard, different addends and a fact reused past a join. An exhausted search reports the outstanding proposition, and an explicit proof replays under the same limit. Wider release arithmetic remains open. [Arithmetic evidence](docs/assurance/completion-log.md#q25at-qualify-checked-synchronous-frontend-correspondence).
  - Scoped `Nat` comparisons also cancel shared offsets on either side of addition, including bounds obtained from false guards. [Cancellation replay](docs/assurance/completion-log.md#q25at-qualify-checked-synchronous-frontend-correspondence)

<a id="q25cd"></a>

- [ ] **Q25cd · Qualify two-phase receiver borrowing for the first release**
  - **Owner** `two-phase-borrow`
  - **Start** Use the [core loan laws](#q25as), [checked frontend](#q25at) and [retained lowering interfaces](#q25az) as their relevant results become available.
  - **Check** Interpret and lower the [receiver phases](docs/language/core-design.md#two-phase-receiver-borrows). Run the [receiver qualification cases](docs/language/loan-analysis.md#two-phase-receiver-trial) through checked source correspondence and lowering. Replay argument order, activation, cancellation and restoration, including the first conflicting access in nearby invalid cases.
  - CFG reservation/activation analysis (`tools/toolchain/loans.py`) and mathematical Rocq replay cover computed receivers, side-effecting argument evaluation, failure before activation, and conflicting-mutation negatives ([Two-phase receiver replay](tools/tests/test_holdfast_loan_returns.py#_two_phase_receiver_replay)); target lowering remains open.

<a id="q25au"></a>

- [ ] **Q25au · Qualify contextual diagnostics and invalidation**
  - **Owner** `core-diagnostics`
  - **Start** Use [checked frontend derivations](#q25at) as they become available.
  - **Check** In the existing interaction path, show each typed hole's location, exact outstanding proposition and status. A dependency change or invalid edit withdraws stale evidence, including late results from the previous generation. [Typed holes and invalidation](docs/language/core-design.md#typed-holes-and-invalidation).
  - The local mathematical playground shows named goals from the elaborator and withdraws them after source or compiler changes. The copy guard, cleanup and post-match loan diagnostics still need the checked release fixture. [Partial evidence](docs/assurance/completion-log.md#q25au-qualify-contextual-diagnostics-and-invalidation).
  - Replay a goal with sufficient and exhausted budgets. Preserve its pending status when exhaustion occurs and withdraw reused evidence after a consumed fact changes. [Proof search and replay](docs/assurance/workflow-contract.md#proof-search-and-replay-under-change)
  - The native playground reports an outstanding inline assertion with its proposition, branch facts and unresolved status. The same assertion replays with enough search or an explicit proof. A premise edit withdraws the previous result even when the assertion text stays fixed. [Interaction evidence](docs/assurance/completion-log.md#q25au-qualify-contextual-diagnostics-and-invalidation).

<a id="q25av"></a>

- [ ] **Q25av · Qualify the composed synchronous fixture and repair protocol**
  - **Owner** `core-repair-trial`
  - **Start** Use the [core laws](#q25as), [checked frontend](#q25at) and [concrete resources](#q25an).
  - **Check** Use the supplied primitive laws to construct an inhabited `PreparationOpen` fixture and its total `finish` transition. Run the independently reviewed invalid neighbors. Measure replay, review and repair after a semantic change, a preserving refactor and a representation change. [Composed fixture](docs/language/core-design.md#composed-qualification-fixture).

<a id="q25aw"></a>

- [ ] **Q25aw · Qualify represented scalar and text library behavior**
  - **Owner** `runtime-primitives`
  - **Start** Use the [accepted validator](#q25ba), [checked frontend](#q25at), [concrete resource interfaces](#q25an) and fixed target and ABI.
  - **Check** Publish representations and laws for the existing integer, UTF-8, raw-string, `TextBuilder` and `Format` definitions for [general lowering](#q25az). Join its per-operation receipts for runtime acceptance. Verify alias identity, arithmetic and conversions, malformed text, exact fit and exhaustion, instance selection, receiver-loan conflicts and static/runtime agreement. [Primitive semantics](docs/language/first-release.md#primitive-semantics) and [bytes and text](docs/language/first-release.md#bytes-and-text).
  - Run the [bounded word counter](examples/word_count.hf) with the [represented ownership libraries](#q25ay). Overwrite the borrowed input between calls. Check that a full key buffer still permits a hit with zero additional key bytes, and that a failed insertion preserves all key bytes and counts. The [mathematical example](docs/tooling/elaboration-prototype.md#try-the-mathematical-fragment) supplies expected outcomes.

<a id="q25ax"></a>

- [x] **Q25ax · Implement locked package and build closure**
  - **Owner** `packages`
  - **Start** Use the [checked frontend](#q25at) once the first-release module and instance semantics are frozen.
  - **Check** Build two independently authored packages with manifests, lockfiles and a reproducible batch graph of dependencies and target inputs. Check nominal identity, instance coherence and import-order independence. Exercise cycles, missing dependencies and stale configurations. A diamond requiring incompatible revisions of one canonical package must fail with both requirements. Replay an importing client across a local parameter rename with a stable external label and across an external-label change. [Module and package contract](docs/language/first-release.md#modules-and-packages).
  - The [locked mathematical build](docs/tooling/elaboration-prototype.md#locked-mathematical-packages) reproduces the provider and importing client from declared inputs. [Landing evidence](docs/assurance/completion-log.md#q25ax-implement-locked-package-and-build-closure).

<a id="q25em"></a>

- [ ] **Q25em · Qualify closed effect inference within release packages**
  - **Owner** `package-effects`
  - **Start** Reuse the existing [closed footprint elaboration](docs/assurance/completion-log.md#q25al-elaborate-consuming-ownership-owned-parameters-and-move-transfers-general-in-ref-runtime-value-loans-and-closed-effects-footprints-reads-writes-calls) and [locked package closure](#q25ax). Bind the inferred summaries through [checked frontend correspondence](#q25at).
  - **Check** Exercise [package effect contracts](docs/language/first-release.md#package-effect-contracts) through a locked package and an independent importing client. Infer read, write and named call bounds for eligible direct helpers across sibling modules. Verify effect identity under import aliases and distinguish same-spelled callables from different modules. Reject omitted export bounds, out-of-package access to an `internal` helper, and recursive and indirect calls without explicit bounds.
  - Replay a provider that reads one `ref` input and writes another. Move the work into unannotated sibling helpers, keep the exported bound fixed and replay the unchanged client with the provider implementation opaque. Require the old lock and receipts to fail freshness against the revised closure. In the neighboring revision, write and restore the input covered only by `reads`. Reject that body under the old bound. Widen the provider's bound and refuse the unchanged client's call at its effect check. Replay a client whose bound covers the new write.
  - The locked mathematical trial infers sibling-helper effects, resolves named calls across import aliases and replays the opaque client across the refactor. The controls exercise stale evidence, effect widening, callable identity and package visibility. Mandatory release export bounds and checked frontend correspondence remain open. [Partial evidence](docs/assurance/completion-log.md#q25em-qualify-closed-effect-inference-within-release-packages).
  - Discarding a record method's result still charges its declared receiver read in the provider and importing package. [Locked receiver-effect replay](docs/assurance/completion-log.md#q25em-qualify-closed-effect-inference-within-release-packages)

<a id="q25ay"></a>

- [ ] **Q25ay · Qualify represented sequence and ownership libraries**
  - **Owner** `runtime-ownership`
  - **Start** Use the [accepted validator](#q25ba) and published [primitive](#q25aw), [concrete resource](#q25an) and [core-law](#q25as) interfaces.
  - **Check** Reuse `Seq`, `Slots`, iterators and selective invariant lifting. Publish represented laws and generic clients covering initialized and vacant ranges, restoration on every exit, bounded iteration and tag-preserving copy into vacant slots followed by ownership transfer. At capacities 4 and 10⁹, require equal obligation counts and the same proof and certificate structure after substituting the capacity literal. Reject per-element unfolding or certificates. Replay both within the declared time and output budgets. Join [general lowering](#q25az) receipts per operation for runtime acceptance. [Ownership libraries](docs/language/first-release.md#ownership-libraries) and [capacity qualification](docs/language/first-release.md#qualification).
  - Replay [the element-loan and relocation pair](docs/language/first-release.md#ownership-libraries) against the represented slots. Identify both access sites when a live element loan blocks the move, and preserve the value copied before relocation in the accepted case.

<a id="q25az"></a>

- [ ] **Q25az · Qualify general synchronous lowering through the retained route**
  - **Owner** `runtime-lowering`
  - **Start** Use the [accepted validator](#q25ba), [frontend correspondence](#q25at), published [primitive](#q25aw) and [ownership](#q25ay) representation laws and the [retained compiler theorem interface](#q25ao).
  - **Check** Extend validator-specific lowering to the declared synchronous release subset. Check the represented-core-to-Clight mapping and source maps for calls, branches, loops, errors and resource exits against independent outputs. Reuse frontend and backend theorems, refuse unsupported constructs explicitly and publish a runtime receipt for each library operation.

<a id="q25ba"></a>

- [ ] **Q25ba · Accept the synchronous component at the exact-artifact endpoint**
  - **Owner** `holdfast-first-slice`
  - **Start** Use the [authored validator](examples/first_slice.hf), its existing narrow lowering and independently checked first-client core, machine, compiler, security and admission receipts.
  - **Check** Bind the exact source, existing proof and emitted bytes to those receipts. Check independent expected outputs, aliasing and restoration, wrong operations, stale inputs and corruption. [First-slice qualification](docs/language/first-release.md#first-slice-qualification).
  - The [opaque caller](tools/tests/test_holdfast_packet_outcome.py) consumes the public error and copied-count law. The [compiled development observer](tools/toolchain/packet_entry.py) checks all nine calls at entry and return, including bad flags with an oversized length, zeroed work area and preserved suffix. It distinguishes altered cursor and write-permission fields at return. Production acceptance still requires checked source correspondence, authority evidence and admission for the exact image. [Partial evidence](docs/assurance/completion-log.md#q25ba-accept-the-synchronous-component-at-the-exact-artifact-endpoint).

<a id="q25bb"></a>

- [ ] **Q25bb · Run the independent package and developer-value trial**
  - **Owner** `holdfast-package-trial`
  - **Start** Select the second client and its intended behavior independently of the first API design. Freeze the baseline, target envelope and benefit thresholds before observing results. Run the trial once the [validator](#q25ba), [packages](#q25ax), represented-library runtime receipts and [general lowering](#q25az) are ready.
  - **Frozen source baseline** Use the existing serialized VerifiedOS copy-service client at [`498127d6`](https://github.com/symbiogenesis/VerifiedOS/tree/498127d6be3d1a70581ba4a9cc025c2d923e66f7). Its [public C interface](https://github.com/symbiogenesis/VerifiedOS/blob/498127d6be3d1a70581ba4a9cc025c2d923e66f7/copy-service/include/vos_copy_service.h) supplies quiescent generation initialization, submit and take. Use the [Gallina reference](https://github.com/symbiogenesis/VerifiedOS/blob/498127d6be3d1a70581ba4a9cc025c2d923e66f7/proofs/CopyRingService.v), [ring declaration](https://github.com/symbiogenesis/VerifiedOS/blob/498127d6be3d1a70581ba4a9cc025c2d923e66f7/interfaces/ring-reference.json) and [fixed controls](https://github.com/symbiogenesis/VerifiedOS/blob/498127d6be3d1a70581ba4a9cc025c2d923e66f7/copy-service/test/fixed_controls.h) to freeze FIFO order, the staged source snapshot, initialized output prefix and untouched suffix, and unchanged caller outputs for empty, full, stale-generation, duplicate and too-small refusals. Keep the 64-slot capacity, 256-position wire index and declared operation payload bounds. Preserve the caller's two disjoint views across submit and take. The overlapping sibling must fail the caller check because the existing C contract requires disjoint extents.
  - Use the same [scalar purecap adapter and layout](https://github.com/symbiogenesis/VerifiedOS/blob/498127d6be3d1a70581ba4a9cc025c2d923e66f7/copy-service/README.md#scalar-target-comparison) on both routes. Hold the existing concurrency and notification adapters fixed outside the serialized trial. Freeze the exact baseline image, producer and per-class resource and timing envelopes before adaptation, then apply the [predeclared accounting and decision thresholds](docs/assurance/workflow-contract.md#accounting-and-decision-thresholds) at the matched endpoint. The target campaign gives finite comparison evidence. The [copy-service admission entry](https://github.com/symbiogenesis/VerifiedOS/blob/498127d6be3d1a70581ba4a9cc025c2d923e66f7/docs/implementation/contracts/production-admission.md#first-case-eligibility-and-consumer-disposition) still requires a qualified, installed and image-bound baseline.
  - The [independent caller](tools/tests/fixtures/q25bb-copy-client.c) freezes the public observations and the disjoint and overlapping caller inputs. The native replay at the frozen VerifiedOS revision passes and rejects changes to the payload boundary, staged prefix, untouched suffix and refusal output. The qualified producer, installed baseline image and target envelopes remain pending. [Partial evidence](docs/assurance/completion-log.md#q25bb-run-the-independent-package-and-developer-value-trial).
  - **Check** Exercise imports, instances, receiver snapshots, partial initialization, exhaustion and resource-returning success and error exits. At the same endpoint, measure annotations, first useful diagnostic, checking latency, review, repair and target costs for a contract change, a preserving refactor and a representation change using explicit Rocq relations. Obtain this client's own admission receipt before acceptance. [Adoption protocol](docs/assurance/workflow-contract.md#first-release-qualification-and-adoption).
  - Run the [public-contract trial](docs/assurance/workflow-contract.md#what-a-caller-can-prove-from-the-public-contract) on the independent client. Check what the caller loses when a required law is weakened and whether its original proof survives a private representation change. Trace [proof erasure and remaining runtime costs](docs/assurance/workflow-contract.md#cost-of-the-verified-abstraction) through the admitted image and compare with the matched baseline on success and error paths.
  - Keep a previously legal boundary input when testing a tightened provider precondition. A compatible version must cover the frozen caller domain and return its promised resources on every reachable exit. Replay both the unchanged caller and the input that distinguishes the two contracts.
  - Exercise two disjoint views retained through one public call sequence and an invalid sibling whose views overlap. Replay the same importing proof after a private layout change. Freeze and cost the equivalent Rust client where the ABI and checked claims allow direct comparison. [Systems costs](docs/language/systems-profile.md#runtime-costs-and-reproducibility)
  - Apply the [contract and assumption review](docs/assurance/workflow-contract.md#reviewing-a-public-contract-change). Replace one discharged library law with a transitive foreign premise and require old-policy failure and the responsible dependency path. Compare cold and incremental proof checking for the preserving refactor and changed dependency.
  - Measured friction can open the [borrow-checker comparison](docs/language/loan-analysis.md#conditional-borrowing-comparison) or [proof-transfer experiment](docs/assurance/workflow-contract.md#representation-transfer-comparison).
    For a loop rewrite forced by borrowing, replay the client's original loop and a neighbor with a live conflicting view. Compare the alias decision, remaining restoration duties and author edits on that pair.

<a id="q25bc"></a>

- [ ] **Q25bc · Publish a supported and reproducible release closure**
  - **Owner** `holdfast-release`
  - **Start** Use the [accepted validator](#q25ba), [independent package trial](#q25bb), qualified [receiver borrowing](#q25cd) and [package effect inference](#q25em), and all required [producer receipts](#q25ar). Use the selected default grading evidence from [Q25be](#q25be), [Q25bj](#q25bj) and [Q25by](#q25by), and default borrowing evidence from [Q25cc](#q25cc) and [Q25cf](#q25cf).
  - **Check** Publish the versioned language and libraries, conformance and refusal corpus, compatibility policy, installation guide, tutorial, reference, dependency notices and reproducible Windows and Linux artifacts. Verify cold installation, build and proof replay, and obtain independent release review. Name each published guarantee's endpoint. Assess feasibility, recurring developer value and adoption separately, including setup, maintenance and per-case target tradeoffs within hard limits. [Adoption protocol](docs/assurance/workflow-contract.md#first-release-qualification-and-adoption).
  - Run the [packet walkthrough](docs/tooling/packet-walkthrough.md) from the release installation. Check the three published byte traces and the diagnostic for each edited program.

<a id="q25bd"></a>

- [ ] **Q25bd · Rehearse one supported-release maintenance cycle**
  - **Owner** `release-maintenance`
  - **Start** Use the [supported release](#q25bc) and its pinned compiler, kernel and dependencies.
  - **Check** Rehearse one coordinated tool and dependency upgrade, including semantic cache invalidation, compatibility and migration, security response, rollback and proof and conformance replay. Record actual human effort, agent time and machine time separately.
  - Use the [evidence-aware package comparison](#q25eg) at the maintenance boundary and measure [replay under change](docs/assurance/workflow-contract.md#proof-search-and-replay-under-change), including failed searches and the first useful diagnosis.

### Remaining HoldFast ergonomics

Qualify the [authoring surface](docs/language/surface-grammar.md#ergonomic-authoring-and-bounded-collection-iteration)
on its actual clients. Checked inference belongs to [Q25as](#q25as) and [Q25at](#q25at),
represented scalars and formatting to [Q25aw](#q25aw), and iteration and relocation
to [Q25ay](#q25ay) and [Q25az](#q25az).
For borrow diagnostics, show both conflicting accesses and check that versioned suggestions
preserve evaluation order, effects, lifetimes and exit obligations. Formatting and lint
previews must preserve tokens and comments, reparse equivalently, be idempotent where
applicable and refuse stale edits. [Diagnostics](#q25au) · [Inspection](#q25ch) ·
[LSP clients](#q25ci) · [Authoring checks](docs/tooling/authoring-tools.md#qualification) ·
[Formatting and previews](#q25ck)

<a id="q25eb"></a>

- [x] **Q25eb · Offer syntax-checked formatting during semantic repair**
  - [Landing evidence](docs/assurance/completion-log.md#q25eb-offer-syntax-checked-formatting-during-semantic-repair).

<a id="q25ec"></a>

- [x] **Q25ec · Compare authored public contracts and effect clauses**
  - [Landing evidence](docs/assurance/completion-log.md#q25ec-compare-authored-public-contracts-and-effect-clauses).

<a id="q25ed"></a>

- [x] **Q25ed · Check marked documentation examples in the repository gate**
  - [Landing evidence](docs/assurance/completion-log.md#q25ed-check-marked-documentation-examples-in-the-repository-gate).

<a id="q25ee"></a>

- [x] **Q25ee · Reject confusable catch-all constructor patterns**
  - [Landing evidence](docs/assurance/completion-log.md#q25ee-reject-confusable-catch-all-constructor-patterns).

<a id="q25ef"></a>

- [x] **Q25ef · Default to qualified imports in the new mathematical edition**
  - [Landing evidence](docs/assurance/completion-log.md#q25ef-default-to-qualified-imports-in-the-new-mathematical-edition).

<a id="q25eg"></a>

- [ ] **Q25eg · Compare locked package guarantees and transitive assumptions**
  - **Owner** `package-evidence`
  - **Start** Use the locked interfaces and checked evidence of the two release clients and the [authored contract comparison](#q25ec).
  - **Check** Review public types, caller domains, outcomes, permissions, resource limits, progress and leakage to the extent each interface promises them. Show old and new assumption owners and dependency paths, including an unchanged signature with changed trust. Replay a frozen client against both releases and report the strongest compatibility verdict justified at the claimed endpoint. [Workflow contract](docs/assurance/workflow-contract.md#reviewing-a-public-contract-change)

<a id="q25el"></a>

- [x] **Q25el · Publish canonical authoring defaults for new packages**
  - **Owner** `package-authoring`
  - **Start** Qualify canonical layout and relevant lints on an independent multi-module package in the selected edition.
  - **Check** Use one canonical formatter in the package's default release checks and explicit editor formatting path. Report layout differences with a single repair command and keep build checks source-preserving. Exercise marked docs, the minimized fixture from a generated failure, and an upgrade that changes a public declaration. Apply the same checks on fresh Windows and Linux installations. [Authoring contract](docs/tooling/authoring-tools.md#qualification)
  - `math-2` root package builds use the canonical formatter and package-context advisory lints. The locked trial passes from fresh Windows and Linux tool environments. [Landing evidence](docs/assurance/completion-log.md#q25el-publish-canonical-authoring-defaults-for-new-packages).

### Language extensions

Commission an extension for a named client when its own inputs are ready. After the
synchronous release, the first bounded async service needs its R-08-046 inventory,
prose and manifests before runtime implementation. Teach the fixed modes first and
compare them and checked trace libraries with a grading increment on the selected
client. [Async service qualification](docs/extensions/handlers-async.md#first-async-service-qualification) ·
[Grading trial](#q25by)

<a id="q25eh"></a>

- [ ] **Q25eh · Qualify a hosted application runtime and foreign bindings**
  - **Owner** `hosted-runtime`
  - **Start** Select one independent application, pinned host and ABI, capability policy and executable semantics. Use checked shared language and resource rules as the relevant producers qualify.
  - **Check** Qualify the shared operations on both profiles and the hosted collection, allocation and cleanup behavior. Exercise validation, retained or moving foreign state, reentry, expired handles, exhaustion and exception translation. State the runtime and binding trust base under the selected assurance policy. [Hosted profile](docs/language/application-profile.md#foreign-calls-and-callbacks)

<a id="q25ei"></a>

- [ ] **Q25ei · Trial hosted application usability and recovery**
  - **Owner** `hosted-client`
  - **Start** Use the [qualified hosted runtime](#q25eh), the independently chosen app, and the frozen workload, C# or TypeScript baseline and thresholds.
  - **Check** Run and debug the real application across the host boundary. Replay helper extraction and a library upgrade, exercise late cancellation and durable commit with a lost acknowledgement, and retry after restart. Evaluate the specified progress assumptions and measure application repair, edit-to-run, binding and runtime costs. [Application acceptance](docs/language/application-profile.md#application-acceptance) · [Progress claims](docs/assurance/verification-strategy.md#progress-at-a-component-boundary)

<a id="q25ej"></a>

- [ ] **Q25ej · Qualify device ownership and portable low-level operations**
  - **Owner** `system-device-client`
  - **Start** Use the admitted first target and select one independent third-party driver, a second target, a frozen public interface and actual device, ordering, representation and compiler producers.
  - **Check** Qualify buffer grants through completion, cancellation and reuse. Replay stale completion and stale backing, confirm publication ordering, and exercise device, atomic and vector operations used by the client. Report missing target laws or qualify the selected fallback; retain exact-image cost and rebuild evidence. [Systems profile](docs/language/systems-profile.md)

<a id="q25ek"></a>

- [ ] **Q25ek · Qualify functional and target leakage claims for tag verification**
  - **Owner** `system-secret-client`
  - **Start** Freeze the client, target, declassification and attacker observations. Use the relevant machine, compiler and exact-image producers.
  - **Check** Replay independent equal and unequal tag cases and reject an early-exit implementation through its differing trace. Report every claimed observation at the target endpoint. If the interface promises erasure, qualify the covered storage and copies on every exit. [Secret-processing client](docs/language/systems-profile.md#secret-processing-client)

<a id="q25be"></a>

- [ ] **Q25be · Qualify the six graded-foundation law packages**
  - **Owner:** `graded-laws`. **Start:** Exercise the pure GF-domain and GF-substitution rules with exact natural grades and a dependent function fixture. Use the qualified synchronous resources and independent graded client as they become available. **Check:** Discharge GF-domain, GF-substitution, GF-elimination, GF-cbv, GF-control-mutation and GF-erasure-source under the [reviewed extension predicates](docs/extensions/full-language-review.md#reviewed-implementation-pricing). Publish the separate law qualification for the [selected first-release fragment](docs/language/first-release.md#default-graded-checking), including source and representation erasure. The combined handler and cell laws retain their wider scope.
  - In the pure investigation, reconstruct separate computation and type demand through binding and elimination. Substitute a stable witness and check the result and every retained dependent declaration row. Replay a binder with zero computation demand and nonzero type demand. Reject an incorrect computation allowance and a stale type-demand certificate. Connect the executable checks to declarative rules in Rocq. [Substitution rules](docs/extensions/graded-foundation.md#substitution-and-structural-rules) · [Pure dependent identity](docs/extensions/graded-foundation.md#pure-dependent-identity)
  - The pure Rocq trial checks dependent functions, natural-index applications and telescope row substitution with exact natural demand. [Partial evidence](docs/assurance/completion-log.md#q25be-qualify-the-six-graded-foundation-law-packages)
  - The pure Rocq trial also checks `Universe` / `TypeVar` levels, type-valued identity specialization (`ApplyType`) and dependent type-telescope substitution, rejecting self-typing universes, wrong computation allowances and stale type rows; dedicated closed-assumption Rocq developments also prove structural/substitution metatheory and the explicit `(s, r)` core calculus (`tools/rocq/graded_metatheory.v`), the unified `GradedCore` calculus (`tools/rocq/graded_core.v`) with `core_weakening`, `core_exchange`, `core_value_substitution`, `core_subgrade_admissible`, `core_grade_substitution`, and `core_zero_type_use_irrelevance` (`tools/rocq/graded_core_metatheory.v`) and `core_type_substitution` (`tools/rocq/graded_core_type_subst.v`), symbolic semiring polymorphism (`tools/rocq/graded_semiring.v`), and CBV erasure with non-interference (`tools/rocq/graded_erasure.v`, `tools/rocq/graded_cbv_erasure.v`). Remaining erasure proofs on `GradedCore` and target lowering remain open. [Partial evidence](docs/assurance/completion-log.md#q25be-qualify-the-six-graded-foundation-law-packages)
  - The ordered domain trial checks `NatExact`, `NatBound`, Boolean presence, `JoinDomain` (`LinearDomain`, `AffineDomain`, `SecurityLoHi`), symbolic `GradeExpr` normalization (`tools/rocq/graded_domains.v`), and general modal semirings (`tools/rocq/graded_modal.v`). Extend the proved demand arithmetic with the remaining target cost and handler/cell composition interpretations. [Domain laws and certificates](docs/extensions/graded-foundation.md#dimensions-and-lawful-domains)
  - The modal trial checks exact and bounded computation demand for promotion, dependent box elimination, first-class box callable elimination (`Apply` and `LetBoxValue`) and named natural/vector records with additive extent families. Extend the rules to broader indexed data and connect their demands to evaluation and erasure.
  - The call-by-value trials relate exact and bounded grades to reads of returned argument values. The scoped-span and dependent-box replays preserve the owner descriptor and frame on both exits, retain effects through failure and relate the specialized extent to one argument evaluation. Connect the interpretation to emitted source and the admitted machine resource exits. [Partial evidence](docs/assurance/completion-log.md#q25be-qualify-the-six-graded-foundation-law-packages)

<a id="q25bf"></a>

- [ ] **Q25bf · Qualify capture, resumption, suspension and cancellation laws**
  - **Owner:** `handler-laws`. **Start:** Concrete scoped resources and a named control/service client. **Check:** Discharge HA-capture-substitution, HA-resume-dispose, HA-suspend-scope and HA-cancel-progress under the [control contract](docs/extensions/handlers-async.md), including fresh clone frames, typed incarnation exhaustion, terminal resources, cancellation at an immediately ready helper's entry and finite masked distance. This aggregates four existing review rows.

<a id="q25bg"></a>

- [ ] **Q25bg · Qualify the combined handler embedding**
  - **Owner:** `handler-embedding`. **Start:** handler-laws and its selected frontend/lowering. **Check:** Discharge HA-combined-embedding over the actual carrier and returned resources; reject adapter-only capture checks and unsupported-feature substitutes. Preserve the existing reviewed range.

<a id="q25bh"></a>

- [ ] **Q25bh · Qualify the five cell and interference law packages**
  - **Owner:** `mutation-laws`. **Start:** Concrete resources, supplied atomic/publication laws, interference/observation contract and a named mutation client. **Check:** Discharge MUT-CELL, MUT-BORROW, MUT-SNAPSHOT, MUT-SHARE and MUT-EXIT under the [mutation contract](docs/extensions/interior-mutability.md), using the supplied atomic commit laws for snapshot validity, scoped invariant opening and safe backing reuse. Aggregate the five existing review rows once; machine atomicity/publication construction has a separate extension-machine-laws allocation.

<a id="q25bi"></a>

- [ ] **Q25bi · Qualify the combined mutation client**
  - **Owner:** `mutation-client`. **Start:** mutation-laws and its actual frontend/runtime support. **Check:** Run the existing MUT-CLIENT predicate with independent scalar-counter behavior, interference, commit/reuse and negative neighbors; source syntax alone earns no verdict.

<a id="q25bj"></a>

- [ ] **Q25bj · Reconstruct checked graded-domain evidence**
  - **Owner:** `graded-frontend`. **Start:** Use the pure derivations as they become available to project a parsed dependent function and its applications into Rocq. Use the graded laws and checked core frontend for extension qualification. **Check:** Implement the existing reviewed elaboration/domain/grade reconstruction row, carrying dictionaries, substitutions and replayable certificates; unresolved or exhausted solver work remains an explicit goal.
  - Qualify grading on the ordinary source and locked-package build paths. Replay the selected exact and bounded dependent, modal and record forms, reject violated allowances and stale source or grade evidence, and check the default behavior under a dependency edit. Bind the grade derivation and emitted interpretation to the same resolved source.
  - Carry checked allowances and type dependencies across local bindings and resolved callable interfaces. Replay a call with a zero-use index that specializes a later parameter and the result. Check both an allowance violation and a provider edit that changes a type-use row while preserving computation demand. Exercise imported declarations through the ordinary locked build. [Grade evidence criteria](docs/extensions/graded-foundation.md#extension-selection-and-qualification)
  - Start with `PreserveLength` in the [dependent example](examples/dependent.hf). Check a zero-use length binder, a once-used vector and partial application at `n + n` for an open index `n`. Bind the result function's domain, codomain and reconstructed dependency rows to the source. Exercise altered allowances and a changed argument or dependency.
  - The opt-in graded source trial replays exact natural demands for dependent functions, box promotion and explicit match motives over natural payloads. Extend checked source correspondence and domain reconstruction from these fragments. [Partial evidence](docs/assurance/completion-log.md#q25bj-reconstruct-checked-graded-domain-evidence)
  - The bounded natural trial uses the checked `NatBound` order for dependent functions, natural application and modal elimination while retaining exact type-use rows. Indexed records carry their own identity and checked vector extent family into the exact and bounded elimination rules. Bind the supported forms through checked source correspondence. [Partial evidence](docs/assurance/completion-log.md#q25bj-reconstruct-checked-graded-domain-evidence)
  - Ordinary replay checks natural `let` bindings, local higher-order calls, `Type`/`Type<n>` type-valued polymorphism and specialization, graded `Box` callable interfaces, first-order and higher-order definitions and callbacks through transitive locked graded imports, and unified `GradedCore` source projection (`tools/toolchain/graded_source.py`, `tools/toolchain/elaborate_graded.py`) with Rocq-checked `(s, r)` binders, structured `grade_error` spans, `domain`/`inductive` elaboration, `<grade q : D>` polymorphism, constraint inference (`tools/toolchain/graded_inference.py`), and CBV erasure verification, requiring grade-checked callers for definitions accepting graded `Box` or callback interfaces. [Current support](docs/tooling/elaboration-prototype.md#default-grade-checking) · [Partial evidence](docs/assurance/completion-log.md#q25bj-reconstruct-checked-graded-domain-evidence)

<a id="q25bk"></a>

- [ ] **Q25bk · Check and lower the selected handler and async constructs**
  - **Owner:** `handler-lowering`. **Start:** handler-laws, core-frontend and a supplied runtime graph interpretation. **Check:** Complete the existing reviewed handler/async frontend row and selected HA-lowering-erasure join with checked capture boundaries, frame/state/reaction graphs and indexed exits. Retained/native backend producers supply their target theorem once.

<a id="q25bl"></a>

- [ ] **Q25bl · Check selected cell protocols and snapshot invalidation**
  - **Owner:** `cell-frontend`. **Start:** mutation-laws and core-frontend. **Check:** Complete the existing reviewed cell frontend row, preserving ownership/interference identities, fresh snapshots and invalidation at writes; source-bound positives and well-formed negatives reach the intended rules.

<a id="q25bm"></a>

- [ ] **Q25bm · Prove correspondence for the selected extension combination**
  - **Owner:** `extension-correspondence`. **Start:** Selected graded/handler/cell frontend rows and their interpretation laws. **Check:** Complete the reviewed extension SourcePackage row across source binding, insertion, erasure and combined terms; no generated term is accepted solely because it kernel-checks.

<a id="q25bn"></a>

- [ ] **Q25bn · Qualify diagnostics for the added extension rules**
  - **Owner:** `extension-diagnostics`. **Start:** Selected extension derivations and core-diagnostics. **Check:** Complete the reviewed additional-diagnostics row with exact source goals, authority/effect traces and freshness after changes. Wider editor projection remains separately budgeted.

<a id="q25bo"></a>

- [ ] **Q25bo · Implement assurance-preset selection and evidence status**
  - **Owner:** `preset-policy`. **Start:** Checked frontend and the [assurance policy](docs/extensions/assurance-profiles.md). **Check:** Complete the reviewed selection/status-engine row with unchanged shared construct meaning, truthful missing-evidence/assumption status and no proof-dependent optimization after its proof is disabled.

<a id="q25bp"></a>

- [ ] **Q25bp · Qualify mixed-assurance linking and closure declarations**
  - **Owner:** `preset-linking`. **Start:** preset-policy, packages and applicable artifact/context evidence. **Check:** Complete the reviewed mixed-linking row over reachable implementations, instances, dependencies, generated code and runtime components; downgrade and foreign-boundary changes invalidate dependent guarantees.

<a id="q25bq"></a>

- [ ] **Q25bq · Qualify assurance-policy refusals**
  - **Owner:** `preset-qualification`. **Start:** preset-policy and preset-linking. **Check:** Run the reviewed policy-semantics predicate against invented invariants, unresolved safety, hidden assumptions and retained theorem-dependent optimizations; reject at the actual policy rule.

<a id="q25br"></a>

- [ ] **Q25br · Qualify ordinary applications under increasing assurance**
  - **Owner:** `preset-client`. **Start:** preset-policy and real parser/collection/service application interfaces. **Check:** Complete the reviewed ordinary-application row with executable reuse, explicit changes and no manual verified rewrite hidden by a preset label.

<a id="q25bs"></a>

- [ ] **Q25bs · Qualify the asynchronous systems-resource boundary**
  - **Owner:** `systems-extension-trial`. **Start:** handler-laws, mutation-laws, selected runtime and concrete resources. **Check:** Complete the reviewed systems-qualification row over an explicit arena and asynchronous operation: cancellation, late completion, failure/exhaustion, quiescence and actual release-gate backing reuse.

<a id="q25bt"></a>

- [ ] **Q25bt · Establish concrete resource laws required by selected extensions**
  - **Owner:** `extension-machine-laws`. **Start:** Shared machine/resource interfaces and frozen selected grade/control/mutation clients. **Check:** Supply additional GF-resource, MUT-ATOMIC and MUT-PUBLISH machine-connected laws, including atomic counter linearization, publication ordering, frame/address stability, capability invariants and service backing reuse. These are beyond the synchronous concrete-resources baseline and outside the 27 parameterized review ranges.

<a id="q25bu"></a>

- [ ] **Q25bu · Prove target transport for the selected language extensions**
  - **Owner:** `extension-target-transport`. **Start:** Selected extension interpretations/frontend and extension-machine-laws. **Check:** Close GF-target, HA-lowering-erasure and added source/IR representation-to-target simulation for the chosen graded/handler/cell/service constructs. Reuse shared retained-compiler and native interfaces; this is incremental extension transport, separate from source graph reconstruction and original synchronous compilation.

<a id="q25bv"></a>

- [ ] **Q25bv · Qualify extension security, cost and admission joins**
  - **Owner:** `extension-security-admission`. **Start:** extension-target-transport and shared contextual-security/admission laws. **Check:** Close MUT-OBSERVE and selected extension leakage, cost/schedule, attribute/TAL and exact-artifact admission joins over real clients. Prove added premises and counterexamples without rebuilding the shared base theorems or inventing new attribute authority.

<a id="q25bw"></a>

- [ ] **Q25bw · Implement and qualify one bounded asynchronous service runtime**
  - **Owner:** `holdfast-service`. **Start:** Accepted synchronous release, handler-laws/lowering and service-specific storage/control laws. **Check:** Implement one named service with direct helper await and one explicit child, capacity failure, ready/pending outcomes, commit/cancel races and cleanup failure. Supply required lifecycle/manifest/register acts and cost/schedule joins before acceptance; this adds runtime implementation, not a second budget for general HA proofs.

<a id="q25bx"></a>

- [ ] **Q25bx · Qualify an explicit bounded-pool library**
  - **Owner:** `bounded-pool`. **Start:** Concrete ownership laws and the release or service client needing allocation. **Check:** Supply allocator/free-list representation, manifests, capacity/exhaustion, initialization, cancellation/quiescence and reuse proofs under the [bounded-pool boundary](docs/language/first-release.md#release-boundary). Reuse shared backing laws; no implicit allocation, retry or new OS allocator is assumed.
  - Reject reclamation while a surviving list points to backing acquired after the checkpoint. Accept the [owned-copy case](docs/language/first-release.md#ownership-libraries) and verify its retained bytes after the reclaimed storage is reused.

<a id="q25ea"></a>

- [ ] **Q25ea · Trial a private linked queue behind a safe package interface**
  - **Owner** `linked-queue-trial`
  - **Start** After the [supported release](#q25bc), select an independent consumer that needs a bounded FIFO with a borrowed front element. Use the [bounded pool](#q25bx) and checked private capability load/store and layout laws. Freeze the public behavior, manual baseline, target, evidence endpoint and acceptable caller and target costs before implementation.
  - **Check** Run the [linked-queue trial](docs/assurance/workflow-contract.md#private-linked-queue-trial). Verify the private link and reclamation invariant, replay the importing client's FIFO proof, and obtain the queue client's own final-image receipt. Record every representation detail the caller had to supply and the measured cost per operation. If the released rules cannot express the queue, record the smallest missing law and price its implementation separately. The estimate covers the sequential trial using existing producers.

<a id="q25by"></a>

- [ ] **Q25by · Compare fixed modes with a bounded grading increment**
  - **Owner:** `grading-trial`. **Start:** Prepare an independent client candidate, its baseline and benefit thresholds alongside the pure investigation. **Check:** Run the [graded qualification protocol](docs/extensions/graded-foundation.md#extension-selection-and-qualification) for the first-release natural grades and type-use accounting. Record the exact evidence endpoint and measured benefit. Use separate selection evidence for general domains.
  - The audio-routing candidate checks two independent type dependencies and an exact value-use allowance. Use the ordinary replay to establish the baseline behavior and select a common endpoint for measuring benefit. [Partial evidence](docs/assurance/completion-log.md#q25by-compare-fixed-modes-with-a-bounded-grading-increment)
  - Freeze a client contract that requires a computation allowance and independence of an exported result type from a designated input. Check the same obligations with fixed modes and explicit proofs, then with reconstructed grades. Compare the annotations, repair work and checking cost of one computation edit and one dependency edit at the shared endpoint.

<a id="q25bz"></a>

- [ ] **Q25bz · Trial derived modality combinators**
  - **Owner:** `grade-derivation`. **Start:** Selected lawful grades, measured boilerplate and checked generation services. **Check:** Qualify the derived-combinator branch of the [conditional usability producers](docs/extensions/graded-foundation.md#conditional-usability-producers) against independent intent and authority preservation. Reuse generic meta construction rather than reimplement it.
  - `tools/toolchain/graded_combinators.py` and `holdfast-parser derive-combinator` implement distributive/box combinator derivation (`dist_pair`, `pull_pair`, `push_sum`, `flatten_box`, `duplicate_box`, `extract_box`, `weaken_box`) with `Linear`/resource/unsound-weakening refusals and zero-axiom Rocq replay (`tools/tests/test_holdfast_graded_combinators.py`); named client recurring-benefit qualification remains open. [Partial evidence](docs/assurance/completion-log.md#q25bz-trial-derived-modality-combinators)

<a id="q25ca"></a>

- [ ] **Q25ca · Trial grade-directed synthesis**
  - **Owner:** `grade-synthesis`. **Start:** Selected grade interpretation, independent synthesis intent and finite search budget. **Check:** Qualify the synthesis branch of the conditional-usability contract with checked output, explicit residuals/timeouts and measured benefit; proposals receive no proof authority.
  - `tools/toolchain/graded_synthesis.py` and `holdfast-parser synthesize-graded` implement resource-pruned bounded synthesis with behavioral oracle rejection, zero-axiom Rocq verification, and explicit `SynthesisResidual` (`exhausted`/`unsatisfiable`) outcomes (`tools/tests/test_holdfast_graded_synthesis.py`); named client benefit qualification remains open. [Partial evidence](docs/assurance/completion-log.md#q25ca-trial-grade-directed-synthesis)

<a id="q25cb"></a>

- [ ] **Q25cb · Trial zero-type-use substitution skipping**
  - **Owner:** `substitution-skipping`. **Start:** Proved selected type-use irrelevance and a measured substitution bottleneck. **Check:** Prove the selected skip transformation preserves elaborated meaning and compare total checking work, certificate size and replay cost; a toy speedup or zero annotation alone is insufficient.
  - For the pure `NatExact` fragment, zero checked type demand leaves the result type and its demand row invariant under substitution (covering both value binders and `TypeVar` binders). `tools/rocq/graded_erasure.v` proves `apply_nat_skip_agrees`, `apply_type_skip_agrees`, and `let_nat_skip_agrees` and replays a 40-binder dependent telescope benchmark (`tools/tests/test_holdfast_graded_metatheory.py`), and `tools/toolchain/elaborate.py` integrates zero-type-use `substitute()` short-circuiting verified with exact-equality and benchmark checks (`tools/tests/test_holdfast_graded.py#_q25cb_zero_type_use_skip_and_benchmark`); wider package-scale cost studies remain open. [Partial evidence](docs/assurance/completion-log.md#q25cb-trial-zero-type-use-substitution-skipping)

<a id="q25cc"></a>

- [ ] **Q25cc · Compare borrow-checking alternatives on held-out clients**
  - **Owner:** `borrow-comparison`. **Start:** Compare proof-backed disjoint symbolic indices against pinned Rust modes on a paired source fixture. Select held-out clients with independent intended behavior and freeze their baseline before adaptation. **Check:** Run the [borrow comparison boundary](docs/language/loan-analysis.md#conditional-borrowing-comparison) on the default HoldFast build with fixed behavior and evidence endpoints. Include conditional returned borrows, lending iteration and higher-ranked or associated-item composition, comparing pinned default and experimental Rust modes and the implemented Ante subset on matched positives and invalid neighbors. Report unsupported cases and budget exhaustion.
  - Freeze a held-out shared-view client with an owner update after the view's last use on one path and a symbolically disjoint update while the view is live on another. Require the returned value, owner writeback, untouched frame and restoration on every exit. Move a use after a conflicting write and substitute an overlapping footprint in separate invalid edits. Replay both failures at the responsible access. Compare direct acceptance against each pinned Rust mode, and record the annotations, proof terms and dynamic checks required by passing rewrites.
  - The branch-view trial replays both access orders, writeback and frame on the default mathematical frontend. The pinned Rust modes reject the direct spelling and accept a `split_at_mut` rewrite. Use these controls in the independent trial. [Branch-view replay](docs/language/loan-analysis.md#branch-local-view-use)
  - Hold two exclusive element loans from one owner under scoped evidence that the indices differ. Write through both and check the restored owner contents. Force the second loan to reuse the first index and require rejection at the call. Report direct Rust acceptance and any safe rewrite separately, including its source edits and required runtime checks.
  - The symbolic-index trial replays both writes and the frame in the HoldFast mathematical model. All three pinned Rust modes reject the direct indexing form and accept the safe slice API version. [Partial evidence](docs/assurance/completion-log.md#q25cc-compare-borrow-checking-alternatives-on-held-out-clients)
  - The nested-row and direct indexed local-borrow trials check live `in coll[i]` and `ref coll[i]` element borrows across disjoint owner writes, branch-specific last use, joined branch writebacks and simultaneous exclusive pairs over `Vec<T, n>`, `Seq<T>`, `Span<byte>` and `Slots<T, capacity>` without helper-call workarounds. [Nested row invalidation](docs/language/loan-analysis.md#nested-row-invalidation)
  - The ordered mixed-loan trial checks a simultaneous shared read and exclusive write at symbolic indices. Use its guard, returned value and frame controls when selecting held-out client cases.
  - The owner-coordinate trial checks a shared element loan from a composed slice against an exclusive element loan on its owner. Carry the same separation and restoration evidence into selected source control-flow cases. [Partial evidence](docs/assurance/completion-log.md#q25cc-compare-borrow-checking-alternatives-on-held-out-clients)
  - A composed view can survive earlier owner writes when every reachable history preserves its extent. The paired Rust direct spelling is refused in all four pinned modes. The safe rewrite passes the shared observation oracle. Carry these checks to the held-out comparison.
  - The conditional-return trials check read-only slices against sibling and joined owner writebacks, including when a common guard chooses the returned slice and the disjoint write. The shared-view and lending filter-return loop trials check returned slices against symbolic prefix fills and mutations. Extend checked source and restoration replay to the remaining higher-ranked clients. [Partial evidence](docs/assurance/completion-log.md#q25cc-compare-borrow-checking-alternatives-on-held-out-clients)
  - Use the diagnostic's branch-specific grants when replaying a joined handle and the write that conflicts on just one incoming path. Connect the reported loan ends and conflicts to checked source and restoration derivations. The integrated loan/elaborator checks additionally cover Polonius-style origin/subset/variance checking (`tools/toolchain/regions.py`), exclusive `ref<'a>` returns with prophecy lenses (`tools/toolchain/elaborate_borrows.py`), GAT `LendingIterator` interfaces, `FnMut`/`FnOnce` HRTBs, `shared ref` safe shared mutability with refinement purging and proof-backed tag/capacity preservation, partial field moves with re-initialization, `ProvedFacts`/`path.obligations` enforcement with 3-span diagnostics, zero-axiom Rocq loan soundness and `check_loan_certificate` proofs (`tools/rocq/loan_semantics.v`, `tools/rocq/loan_soundness.v`), and the 22-case `comparison_matrix` across Rust (`rustc +nightly-2026-11-20`) and Ante (`tools/toolchain/ante_borrow_compare.py`, `holdfast-borrow-compare`). [Join controls](docs/language/loan-analysis.md#diagnostic-disposition)

<a id="q25ce"></a>

- [ ] **Q25ce · Trial a selected local borrowing-alias extension**
  - **Owner:** `borrow-alias`. **Start:** Measured alias need and borrow-comparison selection. **Check:** Qualify one selected local-alias rule with explicit identity/lifetime, restoration, interference and escape controls under the [borrowing promotion contract](docs/language/core-design.md#borrow-analysis-promotion). No general alias facility follows from this envelope.

<a id="q25cf"></a>

- [ ] **Q25cf · Trial selected loop-carried borrowing**
  - **Owner:** `loop-borrow`. **Start:** Use the symbolic view and lending clients and the borrow comparison. **Check:** Qualify the default lending checker and one selected loop-carried loan shape with loop/exit invariants, termination, initialization and borrow restoration. Replay held-out valid and invalid neighbors using general flow and concrete laws.
  - Check that a loan ending before the back edge allows the next element to be lent. Retain the old loan past the next overlapping grant in a neighbor and require a located refusal. Check restoration at normal completion and early exit, including the empty range.
  - The default symbolic `Span<byte>` lending loop closes and writes back each element loan per iteration, including unconditional and terminal conditional `break` exits and range loops that return a borrowed `Span<byte>` view early while freezing post-return state with `Unit + R` folding. Extend the remaining carried-loan client shapes to runtime lowering. [Current lending replay](docs/language/loan-analysis.md#lending-filtering-loops-with-borrowed-returns)

<a id="q25cg"></a>

- [ ] **Q25cg · Trial representation-proof transfer automation**
  - **Owner:** `proof-transfer`. **Start:** Package-trial explicit-relation baseline exposes repeated work. **Check:** Run a bounded [CoqEAL/Trocq comparison](docs/assurance/workflow-contract.md#representation-transfer-comparison), including exact version/licence/assumption closure and maintenance measurement. Preserve the same client laws, preconditions and locked prover; the native baseline remains in the package trial.

### Deferred numerical workload selection

The e-means candidate is outside the priced portfolio. Revisit it when an independent
search-index or quantization-codebook consumer has a frozen contract and the required
arithmetic, sequence libraries and compiler joins are qualified. The
`numerical-client-selection` owner can then price one bounded assignment-and-update
pilot and any additional numerical semantics. Acceptance requires an independent oracle,
checked source, artifact and resource evidence, and separate measurements of numerical
quality and target cost. [Bounded pilot contract](docs/extensions/numerical-workloads.md#bounded-pilot-acceptance)
Freeze the [numerical guarantee](docs/extensions/numerical-workloads.md#portability-and-numerical-guarantees)
before target selection. Review reproducibility and qualified error bounds against the
selected scalar, vector or device operations.

<a id="owner-to-budget-allocation"></a>

### HoldFast whole-system authoring proposal

Whole-system authorship is conditional on the selected inventory. HoldFast sources define
the software, contracts, proofs, ISA and authored hardware. Software and its proofs
share one implementation. Generated Clight, Rocq terms, binaries, simulators and RTL
remain valid outputs. [Authoring contract](docs/extensions/unified-source-contract.md#authoring-end-state)

Select proof, compiler and hardware work independently as their inputs arrive. Reuse the
qualified Menhir grammar and extracted pure parser. Wider source correspondence belongs
to the checked frontend, HoldFast-authored parsing to the native compiler, and seed
retirement to bootstrap. Claim toolchain authorship once the native compiler and its
bootstrap qualify. Adopt a replacement machine model in one generation across its
consumers, including both sides of hardware refinement.
[Parser qualification](docs/tooling/parser.md) · [Frontend](#q25at) · [Bootstrap](#q25dk) ·
[Migration gate](docs/extensions/unified-source-contract.md#migration-and-retirement)

#### Tooling and metaprogramming

Start with the existing compiler facts and a named consumer. Indexing takes resolved
package identities, BSP takes the locked build graph, and native DAP takes exact-image
debug information and a qualified simulator. For code generation, the reviewed descriptor protocol lets
hygienic construction start before the codec is finished. Its checked constructors then
unblock the codec. [Protocol contracts](docs/tooling/tooling-protocols.md) ·
[Descriptor protocol](#q25cx) · [Construction](#q25cy)

<a id="q25ch"></a>

- [ ] **Q25ch · Publish qualified compiler inspection services**
  - **Owner:** `holdfast-compiler-services`. **Start:** Qualified frontend/diagnostic producers; backend for lowering views. **Check:** Meet the [inspection contract](docs/tooling/tooling-protocols.md#compiler-inspection-api) with versioned schemas, bounded snapshots/queries, origins, source reconstruction and stale-handle/input refusal in an independent consumer. Shared identities and producer semantics are charged once here and at their existing producers.
  - The pure producer supplies schema-7 source, token, trivia and syntax-tree snapshots bound to the interpreter identity. It records lexical scopes, memberships and structured identifier and expression types for bounded queries. [Partial evidence](docs/assurance/completion-log.md#q25ch-publish-qualified-compiler-inspection-services) retains wider views and their producer prerequisites.
  - The standalone reader consumes the existing pure producer. Wider views require their own qualified producers.
  - [x] **Q25ds · Qualify independent offline compiler inspection queries**
    - A serialized-snapshot reader independently checks schema, exact source/bindings, syntax/scope/declaration/reference inventories and bounded queries without invoking a parser worker. [Landing evidence](docs/assurance/completion-log.md#q25ds-qualify-independent-offline-compiler-inspection-queries).
  - [ ] **Q25dt · Complete the remaining compiler inspection qualification**
    - Retain qualified wider-language/import/generated/proof/lowering producers and all Q25ch acceptance duties beyond the independently consumed pure snapshots.

<a id="q25ci"></a>

- [ ] **Q25ci · Extend semantic editor services beyond the pure prototype**
  - **Owner:** `holdfast-lsp`. **Start:** Compiler services and qualified wider-language facts. **Check:** Meet the [LSP contract](docs/tooling/tooling-protocols.md#language-server-protocol) for selected workspace navigation, completion/signatures, rename, checked actions, token deltas and read-only proof inspection in two clients. Reuse Q25n/o/u and refuse stale or capturing edits.
  - Compiler-backed callable/value/literal discovery, signatures, token deltas and bounded single-expression recovery invalidate stale producer generations. Pinned Neovim and Vim qualify discovery, recovery and deltas. Neovim and Emacs/Eglot both apply checked local renames and reject stale versions. [Editor evidence](docs/assurance/completion-log.md#q25ci-extend-semantic-editor-services-beyond-the-pure-prototype).
  - [x] **Q25do · Qualify compiler-backed completion at checked literals**
    - The pure resolver supplies type- and scope-compatible whole-literal edits, narrows nested static arguments and shares bounded source-bound completion inventories; independent controls and an unsaved Unicode/CRLF stdio session pass. [Landing evidence](docs/assurance/completion-log.md#q25do-qualify-compiler-backed-completion-at-checked-literals).
  - [ ] **Q25dp · Complete the remaining semantic editor qualification**
    - Retain Q25ci's wider-producer, workspace, proof/action, incomplete-source and client acceptance duties. Reuse the qualified pure discovery, deltas and two-client local rename.
    - [x] **Q25du · Qualify completion at incomplete pure expression sites**
      - At a single empty or unfinished scalar expression, bounded compiler repairs recover current typed/static choices while preserving original diagnostics and source; ambiguous or unrelated failures refuse. [Landing evidence](docs/assurance/completion-log.md#q25du-qualify-completion-at-incomplete-pure-expression-sites).
    - [ ] **Q25dv · Complete the wider semantic editor and client qualification**
      - Two independent editors qualify versioned local rename and the checked Boolean comparison edit against an unsaved overlay. Wider producers, workspace and proof services, general incomplete-source support and wider actions remain open. [Semantic-edit evidence](docs/assurance/completion-log.md#q25dv-complete-the-wider-semantic-editor-and-client-qualification).

<a id="q25cj"></a>

- [x] **Q25cj · Distribute Tree-sitter and TextMate syntax assets**
  - **Owner:** `holdfast-highlight`. **Start:** Canonical Menhir grammar/corpus and named editor consumers. **Check:** Meet the [highlighting contract](docs/tooling/tooling-protocols.md#syntax-grammars-and-highlighting) with both asset formats, fresh/incremental agreement and malformed/Unicode cases; assets grant no semantic acceptance.
  - Generated Menhir-derived assets, pinned independent consumers, the complete canonical corpus with frozen recovery dispositions and eight fresh/incremental edit comparisons pass the [syntax-assets qualification](docs/tooling/highlighting.md#executable-qualification). [Landing evidence](docs/assurance/completion-log.md#q25cj-distribute-tree-sitter-and-textmate-syntax-assets) records the syntax-only boundary.

<a id="q25ck"></a>

- [x] **Q25ck · Extend canonical formatting, lints and checked previews**
  - **Owner:** `holdfast-authoring`. **Start:** Qualified wider syntax and semantic fact producers. **Check:** Meet the [authoring contract](docs/tooling/authoring-tools.md) with token/comment/documentation preservation, reparse equivalence, idempotence and source-bound explicit previews. Reuse Q25t/z/ah; default commands preserve source bytes.
  - The pure and standalone mathematical authoring commands check canonical bytes, lints and explicit previews against their respective compilers. [Landing evidence](docs/assurance/completion-log.md#q25ck-extend-canonical-formatting-lints-and-checked-previews).
  - [x] **Q25dy · Qualify checked Boolean comparison lint previews**
    - Explicit single-comparison previews recheck source and candidate, preserve operand evaluation and outside bytes, bind exact source/producer identities and refuse comments, malformed or stale edits. [Landing evidence](docs/assurance/completion-log.md#q25dy-qualify-checked-boolean-comparison-lint-previews).
  - [x] **Q25dz · Complete the remaining authoring qualification**
    - The mathematical CLI formats the checked replay corpus and preserves token spellings, comment attachment and syntax. Naming, documentation and expression lints use the current source, including the checked bitwise grouping preview. [Landing evidence](docs/assurance/completion-log.md#q25dz-complete-the-remaining-authoring-qualification).

<a id="q25cl"></a>

- [x] **Q25cl · Export qualified batch diagnostics as SARIF**
  - **Owner:** `holdfast-sarif`. **Start:** Diagnostic producers and compiler-service snapshots. **Check:** Meet the [diagnostic export contract](docs/tooling/tooling-protocols.md#diagnostic-and-semantic-index-exports) with a pinned schema and independent importer for Unicode/cross-file locations, fixes and incomplete status; partial analysis cannot appear clean.
  - The [qualified pure batch projection](docs/tooling/tooling-protocols.md#qualified-pure-batch-sarif) consumes the existing diagnostic/format producers, passes an exact-pinned schema and independent reader, and refuses stale, malformed or incomplete handoffs. [Landing evidence](docs/assurance/completion-log.md#q25cl-export-qualified-batch-diagnostics-as-sarif) preserves wider-producer and admission boundaries.

<a id="q25cm"></a>

- [x] **Q25cm · Export a qualified offline SCIP index**
  - **Owner:** `holdfast-scip`. **Start:** Resolved identities, package closure and compiler services. **Check:** Meet the semantic-index export contract with independent offline definition/reference/implementation queries across imports, shadowing, generation and rename; refuse stale bindings and incomplete absence claims.
  - A pinned reader recovers cross-package definitions, implementations, specializations and generated Gallina origins before and after a dependency rename. [Landing evidence](docs/assurance/completion-log.md#q25cm-export-a-qualified-offline-scip-index).

<a id="q25cn"></a>

- [x] **Q25cn · Expose the actual build graph through BSP**
  - **Owner:** `holdfast-build`. **Start:** The packages cell's real locked batch graph and a named client. **Check:** Meet the [build contract](docs/tooling/tooling-protocols.md#build-integration) for targets, dependencies, options and actual bridge commands; cancellation, stale graphs and failed builds preserve batch verdicts. This funds projection, not graph construction.
  - The Neovim BSP client consumes the locked mathematical build graph and its generated Gallina. Clang independently reads the packet bridge's compilation database. [Landing evidence](docs/assurance/completion-log.md#q25cn-expose-the-actual-build-graph-through-bsp).

<a id="q25co"></a>

- [x] **Q25co · Export optimization decisions and explanations**
  - **Owner:** `holdfast-remarks`. **Start:** An actual qualified optimization producer. **Check:** Meet the [remarks contract](docs/tooling/tooling-protocols.md#compiler-decisions-and-performance-traces) in an independent reader for applied/missed/refused cases and source origins; this funds export, not transformations or a speedup claim.
  - Stock LLVM reads the pure compiler's applied, deferred and refused static-call specializations and their authored and generated origins. [Landing evidence](docs/assurance/completion-log.md#q25co-export-optimization-decisions-and-explanations).

<a id="q25cp"></a>

- [x] **Q25cp · Expose bounded compiler performance traces**
  - **Owner:** `holdfast-traces`. **Start:** Named compiler phases and an independent trace consumer. **Check:** Meet the trace contract for clocks, nesting/workers, overhead and bounded recording; dropped events, truncation and cancellation remain explicit. Compiler timing supplies no emitted-program WCET proof.
  - The pure compiler and packet qualification export bounded, input-bound timings. The pinned Perfetto reader recovers phase order, nesting, worker tracks and counters. [Landing evidence](docs/assurance/completion-log.md#q25cp-expose-bounded-compiler-performance-traces).
  - [x] **Q25dq · Qualify parser trace attribution and retained viewer receipts**
    - Record the actual checked-parse/decode work and independently expected nested reader observations; strictly recheck exact reader/harness identities, controls and retained observations. Actual Windows and Linux Perfetto consumers pass. [Landing evidence](docs/assurance/completion-log.md#q25dq-qualify-parser-trace-attribution-and-retained-viewer-receipts).
  - [x] **Q25dr · Complete the remaining compiler trace qualification**
    - The offline browser renders the pure timeline. The two compiler routes bind their user-space inputs, and the pure benchmarks enforce a declared overhead budget. [Landing evidence](docs/assurance/completion-log.md#q25dr-complete-the-remaining-compiler-trace-qualification).
    - [x] **Q25dw · Qualify offline browser rendering of compiler traces**
      - A source-bound offline timeline displays phases, declarations and counters; an explicitly pinned real Chromium browser checks independent geometry, source details, focus and filtering. [Landing evidence](docs/assurance/completion-log.md#q25dw-qualify-offline-browser-rendering-of-compiler-traces).
    - [x] **Q25dx · Complete runtime and broader compiler trace qualification**
      - Trace the live checked parser and the packet compiler through proof replay and C lowering. Verify phase, clock, runtime, worker and benchmark bindings. [Landing evidence](docs/assurance/completion-log.md#q25dx-complete-runtime-and-broader-compiler-trace-qualification).

<a id="q25cq"></a>

- [ ] **Q25cq · Emit and qualify exact-image native debug information**
  - **Owner:** `holdfast-dwarf`. **Start:** Executable backend, fixed purecap ABI and compiler-owned maps. **Check:** Meet the [DWARF contract](docs/tooling/tooling-protocols.md#dwarf-native-debug-information) for scopes/types/locations/inlining/unwind and capability metadata in independent readers, including optimized-away values, malformed sections and stale-image refusal.

<a id="q25cr"></a>

- [x] **Q25cr · Qualify a simulator execution and inspection backend**
  - **Owner:** `debug-runtime`. **Start:** An executable simulator route, exact images and debug maps. **Check:** Implement known stops/stepping, stack/register/capability inspection, reconnect and bounded read-only evaluation against independent expected states; no code patching or hardware trigger is needed. This is the producer missing from the former adapter-only plan.
  - Sail stops at assembler-mapped instructions in four packet control images. The passing run and three trap paths qualify stack frames, observed register and capability fields and handle expiry. [Landing evidence](docs/assurance/completion-log.md#q25cr-qualify-a-simulator-execution-and-inspection-backend).

<a id="q25cs"></a>

- [ ] **Q25cs · Qualify a source debugger through DAP**
  - **Owner:** `holdfast-dap`. **Start:** debug-runtime and holdfast-dwarf. **Check:** Meet the [DAP contract](docs/tooling/tooling-protocols.md#debug-adapter-protocol) for lifecycle, source stepping, scopes/values and stale/unauthorized requests in two clients; reuse the execution producer.

<a id="q25ct"></a>

- [ ] **Q25ct · Qualify conditional RSP and GDB-MI integration**
  - **Owner:** `holdfast-debug-backend`. **Start:** A separately selected debugger engine and its required packet/command subset. **Check:** Meet the [debugger backend contract](docs/tooling/tooling-protocols.md#debugger-backend-protocols) for registers/capabilities, malformed packets, reconnect and stale state in an independent engine. Direct DAP backends need not select this option.

<a id="q25cu"></a>

- [x] **Q25cu · Qualify a bounded web-output producer**
  - **Owner:** `web-output`. **Start:** A selected pure release subset and independently reviewed JavaScript/WebAssembly semantics. **Check:** Implement and check one bounded output route with exact-source correspondence, independent execution/refusals and fixed runtime/resource limits before offering source maps. The existing Gallina playground is reused as UI, not counted as this compiler backend.
  - The [Boolean exporter](docs/tooling/pure-prototype.md#boolean-web-output) checks every input tuple against the selected function's Gallina interpretation before publishing an ES module. [Landing evidence](docs/assurance/completion-log.md#q25cu-qualify-a-bounded-web-output-producer).

<a id="q25cv"></a>

- [x] **Q25cv · Export qualified generated-output source maps**
  - **Owner:** `holdfast-source-maps`. **Start:** web-output or an independently qualified compatible producer and a named consumer. **Check:** Meet the [source-map contract](docs/tooling/tooling-protocols.md#generated-source-maps) for composed/Unicode/unmapped sites and exact map/output/source identities; mismatches fail before handoff. This funds maps, not output generation.
  - The pinned Node.js reader locates mathematical Gallina declarations and generated arithmetic proofs in their authored HoldFast source. [Landing evidence](docs/assurance/completion-log.md#q25cv-export-qualified-generated-output-source-maps).

<a id="q25cw"></a>

- [x] **Q25cw · Qualify target-aware aggregate and text static evaluation**
  - **Owner:** `meta-evaluation`. **Start:** Selected static interpretation subject, target types and sealed dependency closure. **Check:** Construct the incremental phase/evaluation preservation laws and meet the [phase/evaluation contract](docs/extensions/metaprogramming.md#evaluation-and-phase-boundaries) for aggregate/table freezing, deterministic inputs and budgets; refuse runtime layout fallback and host-width substitution. Reuse Q25q's scalar constant functions and the fixed core laws without expanding their budget.
  - The mathematical compiler freezes bounded vectors and UTF-8 text using its declared integer widths. Rocq replays the initializer equations and a dependent consumer, and a locked importing package checks freshness. [Landing evidence](docs/assurance/completion-log.md#q25cw-qualify-target-aware-aggregate-and-text-static-evaluation).

<a id="q25cx"></a>

- [ ] **Q25cx · Qualify opt-in descriptions and one codec derivation**
  - **Owner:** `meta-descriptors`. **Start:** meta-evaluation interfaces, nominal declarations and an independently fixed wire-format intent. **Check:** First freeze the description protocol and prove its incremental privacy/coherence/interpretation laws under the [description contract](docs/extensions/metaprogramming.md#typed-introspection-and-derivation). That milestone unblocks meta-construction before this cell closes. Final codec acceptance consumes its checked construction interface, length checks and independently expected bytes; two mutually agreeing incorrect codecs fail.

<a id="q25cy"></a>

- [ ] **Q25cy · Qualify hygienic typed construction and generated evidence**
  - **Owner:** `meta-construction`. **Start:** Compiler services and the independently reviewed descriptor-protocol/law milestone from meta-descriptors, without waiting for its final codec. **Check:** Prove the incremental hygienic-substitution/construction preservation laws and meet the [construction contract](docs/extensions/metaprogramming.md#hygienic-construction-and-composition) for dependent binders, freshness, capture/effects/resources and exact source/output evidence. Publish its checked interface for codec acceptance; reject binder escape and duplicated authority without adding a proof-admission path or widening core-soundness's budget.

<a id="q25cz"></a>

- [ ] **Q25cz · Qualify selected cross-feature metaprogramming clients**
  - **Owner:** `meta-composition`. **Start:** Selected meta and graded/resource/control laws plus the actual backend endpoint. **Check:** Run the [meta qualification](docs/extensions/metaprogramming.md#qualification) on independently specified clients, well-formed negatives, stale dependency edits and runtime/code-growth controls. This funds client composition, not the other extensions' underlying proofs.

<a id="q25da"></a>

- [x] **Q25da · Rehearse one coordinated optional-portfolio refresh**
  - **Owner:** `tool-maintenance`. **Start:** The adopted tool/meta/native/model/hardware subset and pinned dependency/consumer closure. **Check:** Perform one finite coordinated schema/client/dependency or model-interface refresh, compatibility and security triage, regression/proof/consumer requalification and rollback across adopted options. Reuse release infrastructure and record actual recurring costs; stop and reprice an exhausted cycle, and budget each later cycle separately.
  - The inspection reader, checked Boolean edit preview and Eglot action completed a forward migration, rollback and restoration against the same source and proof fixture. [Landing evidence](docs/assurance/completion-log.md#q25da-rehearse-one-coordinated-optional-portfolio-refresh).

#### Whole-system delivery

<a id="q25db"></a>

- [ ] **Q25db · Qualify complete proof authorship for the frozen proof inventory**
  - **Owner:** `holdfast-proofs`. **Start:** Checked frontend and independently reviewed proof subjects. **Check:** Meet the [proof-authorship boundary](docs/extensions/unified-source-contract.md#software-and-proof-boundary) for the frozen package inventory, including universes, inductive/coinductive reasoning and logical relations; reconstruct/audit kernel terms with no mandatory handwritten fallback. The underlying machine/security theorems retain their shared owners.
  - When an inventory theorem exceeds the [mathematical fragment](docs/tooling/elaboration-prototype.md), retain the first missing rule and an importing client that needs it. Qualify the rule by replaying the original statement and its client and auditing both for added assumptions. Reject a case that violates the new rule, such as an inconsistent universe constraint for a polymorphic theorem or an invalid decrease for well-founded recursion.

<a id="q25dc"></a>

- [ ] **Q25dc · Migrate the frozen operational software inventory**
  - **Owner:** `holdfast-software`. **Start:** Accepted release, its retained target route and supplied component contracts. **Check:** Meet the software-authoring boundary beyond the two release clients: every frozen first-party component, exit, resource/security contract and exact final-byte join uses the same HoldFast-authored implementation, without a separate optimized rewrite. Existing OS functionality/algorithm construction is not repriced as migration.

<a id="q25dd"></a>

- [ ] **Q25dd · Define and admit the native compiler interpretations**
  - **Owner:** `native-ir`. **Start:** Accepted source interpretation, target contract and reviewed replacement duties. **Check:** Define the selected native IRs, source/IR meanings, pass interfaces and admission subjects under the [native compiler contract](docs/extensions/unified-source-contract.md#native-verified-compiler-and-self-hosting); independently review the complete pipeline scope before implementation.

<a id="q25de"></a>

- [ ] **Q25de · Author the selected native parser and compiler in HoldFast**
  - **Owner:** `native-implementation`. **Start:** native-ir and sufficient supported HoldFast implementation/proof facilities. **Check:** Implement the declared compiler/parser closure in HoldFast, preserving grammar/source identities and explicit unsupported diagnostics. Reuse the qualified frontend specification and corpus; seed/development dependency retirement waits for bootstrap.

<a id="q25df"></a>

- [ ] **Q25df · Prove native representation and erasure preservation**
  - **Owner:** `native-representation`. **Start:** native-ir, native-implementation and concrete target resource laws. **Check:** Prove each selected source/IR representation and erasure pass, including ownership, dependent/static information and authority; compose checked pass theorems over actual emitted terms.

<a id="q25dg"></a>

- [ ] **Q25dg · Qualify the selected native optimization families**
  - **Owner:** `native-optimization`. **Start:** native-ir, native-representation and frozen held-out workloads, retained-route baselines, thresholds and hard envelopes. **Check:** Meet the [optimization evidence contract](docs/extensions/unified-source-contract.md#optimization-stages-and-evidence) for selected specialization, inlining, redundant-check elimination and scoped loop/layout/vector families where the target supports them; freeze the chosen list before dispatch. Qualify independent behavior, relational/resource preservation and measured applied/missed cases. No LLVM parity or blanket performance saving is assumed.

<a id="q25dh"></a>

- [ ] **Q25dh · Prove native selection, allocation and final image construction**
  - **Owner:** `native-target`. **Start:** Admitted IRs, exact purecap ABI, canonical machine semantics and qualified passes. **Check:** Construct/prove selection, register/stack allocation, calling convention, assembly, relocations, linkage and image formation to exact target bytes; preserve calls, failures, resources and tag-bearing authority. Interim compiler evidence remains required until replacement acceptance.

<a id="q25di"></a>

- [ ] **Q25di · Compose native security, resource and artifact preservation**
  - **Owner:** `native-preservation`. **Start:** native-representation/optimization/target and the shared semantic/security/admission interfaces. **Check:** Transport the shared contextual-security, leakage and hard-resource theorems through this replacement pipeline and compose its final-byte/source correspondence. This funds native transport only, not a second construction of the shared machine logic or security property.

<a id="q25dj"></a>

- [ ] **Q25dj · Qualify the native compiler closure on held-out consumers**
  - **Owner:** `native-qualification`. **Start:** Complete native pipeline and separately frozen systems/compute consumers. **Check:** Run independent positive/negative/change trials at the required source/artifact endpoint, measure target envelopes, and audit commercial redistribution/rebuild rights for the exact helper/runtime dependency closure; missing rights/evidence blocks adoption.

<a id="q25dk"></a>

- [ ] **Q25dk · Qualify verified self-hosting and resident rebuilding**
  - **Owner:** `holdfast-bootstrap`. **Start:** Qualified native compiler definition and sufficient HoldFast proof authorship. **Check:** Meet the [bootstrap contract](docs/extensions/unified-source-contract.md#bootstrap-and-qualification): connect proved definition, reviewed seed and successive exact binaries, self-compile the declared closure, and qualify reproducibility, runtime/helper/licence closure and resident rebuilding. Reproducibility alone is not the compiler theorem.

<a id="q25dl"></a>

- [ ] **Q25dl · Qualify the frozen HoldFast machine-model replacement**
  - **Owner:** `holdfast-machine`. **Start:** Admitted interpretation and the pinned canonical Sail/profile contract. **Check:** Meet the [machine-model contract](docs/extensions/unified-source-contract.md#machine-model) for every frozen operation/configuration with behavior/progress and relational leakage/cost agreement, independent executable cases and malformed/stale refusals. Original machine-logic construction remains in the shared prerequisite cells.

<a id="q25dm"></a>

- [ ] **Q25dm · Qualify hardware interpretation and migrate the frozen blocks**
  - **Owner:** `holdfast-hardware`. **Start:** Reviewed cycle/register meaning, block contracts and canonical machine interface. **Check:** Meet the [hardware contract](docs/extensions/unified-source-contract.md#hardware) for every frozen authored block with checked generation to exact synthesis inputs, cycle/commit/progress/refinement evidence and its existing artifact tier. Reuse supplied original block theorems; physical fabrication/lab work is outside language migration.

<a id="q25dn"></a>

- [ ] **Q25dn · Adopt the shared model and retire legacy authoring dependencies**
  - **Owner:** `holdfast-retirement`. **Start:** Accepted machine agreement and complete affected-consumer inventory. **Check:** Meet the [migration gate](docs/extensions/unified-source-contract.md#migration-and-retirement) by rebinding every frozen compiler, logic, TAL, constant-time, timing and hardware consumer in one admitted generation, with explicit amendments and historical evidence retention. No private model or missing consumer is permitted.

<a id="q-assessment-actions"></a>

### Completed foundations and prototypes

- [x] **Q25 · Design the full graded dependent language and its control and mutation rules**
  [Evidence](docs/assurance/completion-log.md#q25-design-the-full-graded-dependent-language-and-its-control-and-mutation-rules)
  - [x] **Q25a · Specify the graded dependent foundation** [Evidence](docs/assurance/completion-log.md#q25a-specify-the-graded-dependent-foundation)
  - [x] **Q25b · Specify handlers and structured async lifecycles** [Evidence](docs/assurance/completion-log.md#q25b-specify-handlers-and-structured-async-lifecycles)
  - [x] **Q25c · Specify interior mutability and interference guardrails** [Evidence](docs/assurance/completion-log.md#q25c-specify-interior-mutability-and-interference-guardrails)
- [x] **Q25d · Review the combined calculus and price its implementation** [Evidence](docs/assurance/completion-log.md#q25d-review-the-combined-calculus-and-price-its-implementation)
- [x] **Q25e · Build a pure HoldFast-to-Gallina prototype** [Evidence](docs/assurance/completion-log.md#q25e-build-a-pure-holdfast-to-gallina-prototype)
- [x] **Q25f · Align the executable HoldFast subset with its proposed surface** [Evidence](docs/assurance/completion-log.md#q25f-align-the-executable-holdfast-subset-with-its-proposed-surface)
- [x] **Q25g · Build the Menhir development parser for pure HoldFast** [Evidence](docs/assurance/completion-log.md#q25g-build-the-menhir-development-parser-for-pure-holdfast)
- [x] **Q25h · Qualify checked HoldFast parsing and retire the Python parser** [Evidence](docs/assurance/completion-log.md#q25h-qualify-checked-holdfast-parsing-and-retire-the-python-parser)
- [x] **Q25i · Extend the Menhir grammar across the HoldFast authoring surface** [Evidence](docs/assurance/completion-log.md#q25i-extend-the-menhir-grammar-across-the-holdfast-authoring-surface)
- [x] **Q25j · Prototype path-sensitive loan-end inference over explicit flow facts** [Evidence](docs/assurance/completion-log.md#q25j-prototype-path-sensitive-loan-end-inference-over-explicit-flow-facts)
- [x] **Q25k · Elaborate generic dependent mathematics and first-class proofs** [Evidence](docs/assurance/completion-log.md#q25k-elaborate-generic-dependent-mathematics-and-first-class-proofs)
- [x] **Q25l · Clarify HoldFast borrowing, evidence and resource interfaces** [Evidence](docs/assurance/completion-log.md#q25l-clarify-holdfast-borrowing-evidence-and-resource-interfaces)
- [x] **Q25m · Specify staged HoldFast metaprogramming and compiler services** [Evidence](docs/assurance/completion-log.md#q25m-specify-staged-holdfast-metaprogramming-and-compiler-services)
- [x] **Q25n · Prototype and qualify HoldFast LSP lifecycle and pure diagnostics** [Evidence](docs/assurance/completion-log.md#q25n-prototype-and-qualify-holdfast-lsp-lifecycle-and-pure-diagnostics)
- [x] **Q25o · Add and qualify pure HoldFast LSP navigation** [Evidence](docs/assurance/completion-log.md#q25o-add-and-qualify-pure-holdfast-lsp-navigation)
- [x] **Q25p · Improve HoldFast authoring syntax and editor hints** [Evidence](docs/assurance/completion-log.md#q25p-improve-holdfast-authoring-syntax-and-editor-hints)
- [x] **Q25q · Implement compositional HoldFast constant functions and parameters** [Evidence](docs/assurance/completion-log.md#q25q-implement-compositional-holdfast-constant-functions-and-parameters)
- [x] **Q25r · Add HoldFast numeric digit separators** [Evidence](docs/assurance/completion-log.md#q25r-add-holdfast-numeric-digit-separators)
- [x] **Q25s · Attach HoldFast documentation comments to compiler facts** [Evidence](docs/assurance/completion-log.md#q25s-attach-holdfast-documentation-comments-to-compiler-facts)
- [x] **Q25t · Integrate default HoldFast formatting and lints** [Evidence](docs/assurance/completion-log.md#q25t-integrate-default-holdfast-formatting-and-lints)
- [x] **Q25u · Add pure HoldFast editor formatting and semantic tokens** [Evidence](docs/assurance/completion-log.md#q25u-add-pure-holdfast-editor-formatting-and-semantic-tokens)
- [x] **Q25v · Settle the bounded HoldFast release and practical language contracts** [Evidence](docs/assurance/completion-log.md#q25v-settle-the-bounded-holdfast-release-and-practical-language-contracts)
- [x] **Q25w · Investigate the concrete HoldFast buffer foundation within a fixed budget** [Evidence](docs/assurance/completion-log.md#q25w-investigate-the-concrete-holdfast-buffer-foundation-within-a-fixed-budget)
- [x] **Q25x · Qualify generated tests for existing HoldFast development tools** [Evidence](docs/assurance/completion-log.md#q25x-qualify-generated-tests-for-existing-holdfast-development-tools)
- [x] **Q25y · Qualify Menhir-generated syntax campaigns** [Evidence](docs/assurance/completion-log.md#q25y-qualify-menhir-generated-syntax-campaigns)
- [x] **Q25z · Qualify the familiar HoldFast authoring surface** [Evidence](docs/assurance/completion-log.md#q25z-qualify-the-familiar-holdfast-authoring-surface)
- [x] **Q25aa · Build a local HoldFast browser playground** [Evidence](docs/assurance/completion-log.md#q25aa-build-a-local-holdfast-browser-playground)
- [x] **Q25ab · Extend the HoldFast playground authoring and inspection controls** [Evidence](docs/assurance/completion-log.md#q25ab-extend-the-holdfast-playground-authoring-and-inspection-controls)
- [x] **Q25ac · Extend pure HoldFast expressions and playground examples** [Evidence](docs/assurance/completion-log.md#q25ac-extend-pure-holdfast-expressions-and-playground-examples)
- [x] **Q25ad · Add natural division and remainder to HoldFast and its playground** [Evidence](docs/assurance/completion-log.md#q25ad-add-natural-division-and-remainder-to-holdfast-and-its-playground)
- [x] **Q25ae · Bring dependent HoldFast mathematics into the playground** [Evidence](docs/assurance/completion-log.md#q25ae-bring-dependent-holdfast-mathematics-into-the-playground)
- [x] **Q25af · Make HoldFast elaboration evidence kernel-honest** [Evidence](docs/assurance/completion-log.md#q25af-make-holdfast-elaboration-evidence-kernel-honest)
- [x] **Q25ag · Conform the HoldFast first slice to the synchronous design** [Evidence](docs/assurance/completion-log.md#q25ag-conform-the-holdfast-first-slice-to-the-synchronous-design)
- [x] **Q25ah · Resolve HoldFast surface collisions and redundant spellings** [Evidence](docs/assurance/completion-log.md#q25ah-resolve-holdfast-surface-collisions-and-redundant-spellings)
- [x] **Q25ai · Publish the HoldFast language reference and separate extension research** [Evidence](docs/assurance/completion-log.md#q25ai-publish-the-holdfast-language-reference-and-separate-extension-research)
- [x] **Q25aj · Unify HoldFast playground assets, single-source grammar sync, and single-pass worker execution** [Evidence](docs/assurance/completion-log.md#q25aj-unify-holdfast-playground-assets-single-source-grammar-sync-and-single-pass-worker-execution)
- [x] **Q25ak · Close remaining elaboration solver axioms and promote source-bound borrow and mutation-invalidation checking** [Evidence](docs/assurance/completion-log.md#q25ak-close-remaining-elaboration-solver-axioms-and-promote-source-bound-borrow-and-mutation-invalidation-checking)
- [x] **Q25al · Elaborate consuming ownership (`owned` parameters and `move` transfers), general `in`/`ref` runtime value loans, and closed `effects` footprints (`reads`/`writes`/`calls`)** [Evidence](docs/assurance/completion-log.md#q25al-elaborate-consuming-ownership-owned-parameters-and-move-transfers-general-in-ref-runtime-value-loans-and-closed-effects-footprints-reads-writes-calls)

## Planning basis and scope

- **Effort.** Estimates and ranges are judgments in attended engineering hours,
  including design, implementation, proofs, review preparation, tests,
  documentation and initial qualification. The four core estimates and 27
  extension ranges are allocated once. Keep human effort, summed agent-session
  wall time and machine time separate. Research estimates use no multiplier
  from historical actuals or person-month comparisons.
- **Release scope.** One canonical CHERI-RISC-V profile/ABI, one retained
  compiler route, the packet validator and a second independently selected
  client. Windows and Linux host tools are in scope. Resident protocol
  endpoints and resident compiler rebuilding have separate scopes.
- **Shared work.** VerifiedOS retains its machine-logic, byte-instance,
  scoped-resource, compiler, security and admission owners. The
  [foundation cells](#shared-foundation-and-retained-route) price only residual
  HoldFast needs beyond the booked Q35/M1/TAL slices. Summing both projects'
  estimates would double count shared work. OS algorithms, device design and
  other whole-system proofs remain with their owners.
- **Conditional scope.** Optional migrations use the first-party software,
  proofs, configuration and authored hardware at
  [VerifiedOS revision 3529ecd](https://github.com/symbiogenesis/VerifiedOS/tree/3529ecd08b8288b004d71766066b0c3367b9cb40)
  and the HoldFast implementation at `0354004` as the reuse baseline. Freeze the
  selected paths, theorem subjects, target features and permitted generated or
  imported artifacts at entry. Reprice additions. The estimates exclude a new
  processor, open-ended language growth, a public package registry, interactive
  proof admission and fabrication or laboratory work.
- **Stopping and maintenance.** A missing law or exhausted investigation
  budget stops the dependent slice. Record the result and reprice any remaining
  work. Proof acceptance requires checked terms and independent review of the
  intended behavior. Review an upstream's licence at the milestone that would
  incorporate it under the [licensing rules](COPYRIGHT.md#terms-this-tree-does-not-carry).
  Release and optional-portfolio maintenance each price one requalification
  cycle. Record its actual cost and estimate each later cycle separately.

## Current Summary

The estimate covers the supported release, shared prerequisites and conditional
options. Its percentage measures completed effort across that portfolio. Use
the [release milestones](#current-execution) to judge readiness.

<!-- estimate-summary:start -->
| Measure | Value |
| --- | --- |
| Total estimate midpoint h | 23,801.9 |
| Total estimate range h | 12,889.9–34,713.9 |
| Completed scope h | 1,541.9 |
| Complete by estimate % | 6.5 |
| Remaining h | 22,260 |
| Open class I h | 2,080 |
| Open class X h | 20,180 |
| Retained completion estimate h | 1,538.5 |
| Unmeasured completed items | 54 |
<!-- estimate-summary:end -->

The table counts each checklist leaf once. Completed work contributes actual
hours where known and its retained estimate otherwise. Open estimates and their
bounds determine the remaining hours and total range. After a status or estimate
changes, refresh the table with `python tools/run.py check --fix`.

## Calibration record (Q25 series)

| Item | Class | Estimate (h) | Range (h) | Actual (h) | Ratio |
| --- | --- | --- | --- | --- | --- |
| Q25a | X-authored | 10 | n/a | 0.2 | 0.02 |
| Q25b | X-authored | 12 | n/a | 0.2 | 0.02 |
| Q25c | X-authored | 10 | n/a | 0.2 | 0.02 |
| Q25d | X-authored | 10 | n/a | 0.9 | 0.09 |
| Q25e | I | 8 | n/a | 0.3 | 0.04 |
| Q25f | I | 2 | n/a | 0.1 | 0.05 |
| Q25g | I | 6 | 4–8 | n/a | n/a |
| Q25h | X | 16 | 8–24 | n/a | n/a |
| Q25i | I | 24 | 16–32 | n/a | n/a |
| Q25j | I | 12 | 8–16 | n/a | n/a |
| Q25k | I | 24 | 16–32 | n/a | n/a |
| Q25l | I | 2 | n/a | 0.3 | 0.15 |
| Q25m | n/a | n/a | n/a | 0.5 | n/a |
| Q25n | I | 6 | 4–8 | n/a | n/a |
| Q25o | I | 8 | 6–10 | n/a | n/a |
| Q25p | I | 8 | 6–10 | n/a | n/a |
| Q25q | I | 16 | 8–24 | n/a | n/a |
| Q25r | I | 12 | 8–16 | n/a | n/a |
| Q25s | I | 12 | 8–16 | n/a | n/a |
| Q25t | I | 24 | 16–32 | n/a | n/a |
| Q25u | I | 12 | 8–16 | n/a | n/a |
| Q25v | I | 4 | 2–6 | 0.7 | 0.18 |
| Q25w | X | 24 | 16–32 | n/a | n/a |
| Q25x | X | 6 | 4–8 | n/a | n/a |
| Q25y | X | 4.5 | 3–6 | n/a | n/a |
| Q25z | I | 32 | 24–40 | n/a | n/a |
| Q25aa | I | 12 | 8–16 | n/a | n/a |
| Q25ab | I | 8 | 6–10 | n/a | n/a |
| Q25ac | I | 8 | 6–10 | n/a | n/a |
| Q25ad | I | 6 | 4–8 | n/a | n/a |
| Q25ae | I | 16 | 12–20 | n/a | n/a |
| Q25af | I | 24 | 16–32 | n/a | n/a |
| Q25ag | I | 24 | 16–32 | n/a | n/a |
| Q25ah | I | 16 | 12–20 | n/a | n/a |
| Q25ai | I | 12 | 8–16 | n/a | n/a |
| Q25aj | I | 8 | 6–12 | n/a | n/a |
| Q25ak | I | 16 | 12–20 | n/a | n/a |
| Q25al | I | 12 | 8–16 | n/a | n/a |
| Q25am | X | 800 | 400–1,200 | n/a | n/a |
| Q25an | X | 400 | 200–600 | n/a | n/a |
| Q25ao | X | 800 | 400–1,200 | n/a | n/a |
| Q25ap | X | 1,200 | 600–1,800 | n/a | n/a |
| Q25aq | X | 800 | 400–1,200 | n/a | n/a |
| Q25ar | X | 40 | 24–56 | n/a | n/a |
| Q25as | X | 160 | 80–240 | n/a | n/a |
| Q25at | I | 140 | 80–200 | n/a | n/a |
| Q25au | I | 64 | 40–88 | n/a | n/a |
| Q25av | X | 48 | 32–64 | n/a | n/a |
| Q25aw | I | 96 | 64–128 | n/a | n/a |
| Q25ax | I | 96 | 64–128 | n/a | n/a |
| Q25ay | I | 120 | 80–160 | n/a | n/a |
| Q25az | I | 112 | 64–160 | n/a | n/a |
| Q25ba | X | 96 | 48–144 | n/a | n/a |
| Q25bb | X | 80 | 48–112 | n/a | n/a |
| Q25bc | I | 72 | 48–96 | n/a | n/a |
| Q25bd | I | 64 | 32–96 | n/a | n/a |
| Q25be | X | 296 | 168–424 | n/a | n/a |
| Q25bf | X | 176 | 96–256 | n/a | n/a |
| Q25bg | X | 40 | 22–58 | n/a | n/a |
| Q25bh | X | 200 | 110–290 | n/a | n/a |
| Q25bi | I | 32 | 18–46 | n/a | n/a |
| Q25bj | X | 72 | 40–104 | n/a | n/a |
| Q25bk | X | 64 | 36–92 | n/a | n/a |
| Q25bl | X | 40 | 22–58 | n/a | n/a |
| Q25bm | X | 48 | 26–70 | n/a | n/a |
| Q25bn | X | 40 | 22–58 | n/a | n/a |
| Q25bo | I | 48 | 26–70 | n/a | n/a |
| Q25bp | I | 40 | 24–56 | n/a | n/a |
| Q25bq | I | 24 | 14–34 | n/a | n/a |
| Q25br | I | 24 | 14–34 | n/a | n/a |
| Q25bs | I | 32 | 18–46 | n/a | n/a |
| Q25bt | X | 400 | 200–600 | n/a | n/a |
| Q25bu | X | 360 | 180–540 | n/a | n/a |
| Q25bv | X | 240 | 120–360 | n/a | n/a |
| Q25bw | I | 160 | 80–240 | n/a | n/a |
| Q25bx | I | 128 | 64–192 | n/a | n/a |
| Q25by | X | 32 | 16–48 | n/a | n/a |
| Q25bz | X | 64 | 32–96 | n/a | n/a |
| Q25ca | X | 48 | 24–72 | n/a | n/a |
| Q25cb | X | 32 | 16–48 | n/a | n/a |
| Q25cc | X | 32 | 16–48 | n/a | n/a |
| Q25cd | X | 96 | 48–144 | n/a | n/a |
| Q25ce | X | 96 | 48–144 | n/a | n/a |
| Q25cf | X | 96 | 48–144 | n/a | n/a |
| Q25cg | X | 32 | 16–48 | n/a | n/a |
| Q25ea | X | 96 | 48–144 | n/a | n/a |
| Q25ds | I | 24 | 12–36 | n/a | n/a |
| Q25dt | I | 88 | 52–124 | n/a | n/a |
| Q25do | I | 8 | 4–12 | n/a | n/a |
| Q25du | I | 16 | 8–24 | n/a | n/a |
| Q25dv | I | 88 | 52–124 | n/a | n/a |
| Q25cj | I | 56 | 32–80 | n/a | n/a |
| Q25dy | I | 8 | 4–12 | n/a | n/a |
| Q25dz | I | 64 | 36–92 | n/a | n/a |
| Q25cl | I | 28 | 16–40 | n/a | n/a |
| Q25cm | I | 44 | 24–64 | n/a | n/a |
| Q25cn | I | 44 | 24–64 | n/a | n/a |
| Q25co | I | 28 | 16–40 | n/a | n/a |
| Q25dq | I | 6 | 4–8 | n/a | n/a |
| Q25dw | I | 14 | 8–20 | n/a | n/a |
| Q25dx | I | 8 | 4–12 | n/a | n/a |
| Q25cq | I | 144 | 80–208 | n/a | n/a |
| Q25cr | I | 96 | 48–144 | n/a | n/a |
| Q25cs | I | 112 | 64–160 | n/a | n/a |
| Q25ct | I | 76 | 40–112 | n/a | n/a |
| Q25cu | I | 192 | 96–288 | n/a | n/a |
| Q25cv | I | 38 | 20–56 | n/a | n/a |
| Q25cw | I | 72 | 40–104 | n/a | n/a |
| Q25cx | I | 112 | 64–160 | n/a | n/a |
| Q25cy | I | 152 | 80–224 | n/a | n/a |
| Q25cz | X | 116 | 56–176 | n/a | n/a |
| Q25da | I | 192 | 96–288 | n/a | n/a |
| Q25db | X | 640 | 320–960 | n/a | n/a |
| Q25dc | X | 1,280 | 640–1,920 | n/a | n/a |
| Q25dd | X | 320 | 160–480 | n/a | n/a |
| Q25de | X | 480 | 240–720 | n/a | n/a |
| Q25df | X | 800 | 400–1,200 | n/a | n/a |
| Q25dg | X | 960 | 480–1,440 | n/a | n/a |
| Q25dh | X | 960 | 480–1,440 | n/a | n/a |
| Q25di | X | 800 | 400–1,200 | n/a | n/a |
| Q25dj | X | 320 | 160–480 | n/a | n/a |
| Q25dk | X | 640 | 320–960 | n/a | n/a |
| Q25dl | X | 1,280 | 640–1,920 | n/a | n/a |
| Q25dm | X | 1,920 | 960–2,880 | n/a | n/a |
| Q25dn | X | 640 | 320–960 | n/a | n/a |
| Q25eb | I | 12 | 8–16 | n/a | n/a |
| Q25ec | I | 12 | 8–16 | n/a | n/a |
| Q25ed | I | 8 | 4–12 | n/a | n/a |
| Q25ee | I | 8 | 4–12 | n/a | n/a |
| Q25ef | I | 16 | 8–24 | n/a | n/a |
| Q25eg | I | 96 | 56–136 | n/a | n/a |
| Q25eh | X | 960 | 480–1,440 | n/a | n/a |
| Q25ei | X | 240 | 120–360 | n/a | n/a |
| Q25ej | X | 480 | 240–720 | n/a | n/a |
| Q25ek | X | 320 | 160–480 | n/a | n/a |
| Q25el | I | 40 | 24–56 | n/a | n/a |
| Q25em | I | 56 | 32–80 | n/a | n/a |
