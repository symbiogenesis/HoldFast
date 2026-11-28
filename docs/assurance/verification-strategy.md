# HoldFast verification strategy

The [first-release contract](../language/first-release.md) defines the supported
language and artifact boundary. This document covers how HoldFast's interpretation,
proofs and compilation fit that boundary. The
[VerifiedOS requirements register](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/requirements-register.md)
governs production obligations. [PLAN.md](../../PLAN.md) tracks implementation
and qualification.

## Language product contract

HoldFast combines explicit low-level operations and machine-checkable specifications.
Stable dependent indices describe shapes, types and snapshots. A resource context
accounts for ownership and mutation through normal and failure exits. The
[language reference](../language/reference.md) describes the syntax and its
support in development tools. The [core design](../language/core-design.md) defines
the intended interpretation and proof obligations.

The bounded release pairs fixed representations and ownership modes with
ordinary error values and closed effect bounds. Measure the authoring costs of
representability proofs, transitive effect lists and receiver snapshots in the
independent package trial. [Release qualification](../language/first-release.md#qualification)
· [Adoption criteria](workflow-contract.md#first-release-qualification-and-adoption)

### Expected developer experience

Authors work with ordinary code and contracts, inferred refinements, and
explicit assertions and lemmas. The diagnostic for an unresolved goal needs its
source span, local hypotheses, resource state and expected result. Distinguish
refutation, unsupported input, and unfinished checking.
[Typed holes and invalidation](../language/core-design.md#typed-holes-and-invalidation)

Batch diagnostics, editor navigation and interchange use semantic facts from
their source checker. The [tooling contracts](../tooling/tooling-protocols.md)
define qualified subsets, result identities and independent-client checks.

### Progress at a component boundary

Public interfaces distinguish execution-wide safety, partial correctness on return, single-call termination, and ongoing service progress. A potentially nonterminating call can still preserve caller memory permissions (e.g., two tasks safely holding disjoint locks while waiting for each other). The [bounded release](../language/first-release.md#release-boundary) retains its loop/termination obligations; any future runtime admitting divergence must keep potentially divergent calls out of logical conversion and account for resources held while waiting.

Reactive services must state admissible requests, terminal outcomes, and the scheduler, peer, device, or clock premises ensuring completion. Deadlines also require a clock bound and per-dependency bounds, naming each premise's owner. An implementation withholding admission from all healthy requests fails an available-capacity admission promise. Qualification tests one admitted request to completion and one non-responding-peer execution against promised timeout/recovery if premises hold; if a premise fails, withdraw the progress claim and verify the remaining safety/ownership claims. [Structured async bounds and progress](../extensions/handlers-async.md#bounds-and-progress-premises)

When a remote operation can commit and lose its acknowledgement before retry, an interface promising at-most-once durable effect per logical request must state how request identity survives restarts, how durable state deduplicates retries, and the duplicate-protection window, exercising recovery redelivery across that interval. If outcome resolution is impossible, expose that uncertainty to the caller.

## Proposed architecture

Under [R-05-020a](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020a),
the frontend may elaborate into an existing semantic anchor and submit the
result for kernel checking. Checked source correspondence binds the
interpretation to the exact authored closure. A separate authority, semantics
or checker must meet [R-05-020](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020).

```text
Authored source closure and independently reviewed behavior contract
    -> checked interpretation and source correspondence
    -> proved representation and lowering
    -> verified or translation-validated optimization
    -> capability-aware code generation and typed linkage
    -> exact bytes with TAL and CIC evidence over pinned Sail
```

Each arrow is a proof obligation. The
[source package](#mechanically-produced-evidence) binds parsing, resolution,
implicit insertion and desugaring. Representation laws connect the program to
the selected CHERI model. Hardware refinement meets the same Sail definitions
independently. [Artifact endpoint](compiler-route-contract.md#equivalent-artifact-endpoint)

### Development parser and grammar

[Menhir](../tooling/parser.md) produces located syntax trees before resolution,
checking and elaboration. The checked pure parser's grammar-relative theorems,
the native parser's wider syntax support and the
[mathematical elaborator's kernel replay](../tooling/elaboration-prototype.md#commands-and-acceptance)
have distinct subjects. Broader checked parsing and exact source
correspondence require their own derivations.

<a id="full-language-design-commitments"></a>

## Extensions and language constraints

The [permanent exclusions](#permanent-language-exclusions) apply across the
language. The [extension index](../extensions/README.md) links the optional
designs and the [composition contract](../extensions/full-language-review.md)
defines how their rules interact. Production support requires concrete resource
laws, checked correspondence, lowering and admission for the selected feature.

### Graded dependent foundation

[Graded rules](../extensions/graded-foundation.md) track use in named, lawful
domains. Resource permissions, representation, erasure and effects each
retain their own interpretation.

### General handlers with resource-safe resumptions

The [handler rules](../extensions/handlers-async.md#handler-lookup-capture-and-return)
account for the resources retained in each continuation and the uses permitted
by the operation's resumption bound. [Illustrative handler](#handlers-with-accountable-continuations)

### Structured async and cancellation

The [task lifecycle](../extensions/handlers-async.md#frames-child-ownership-and-reaction-execution)
defines bounded frame storage, direct await, child ownership, and result
collection. Cancellation requires a declared checkpoint, commit and cleanup
protocol. [Cancellation and exits](../extensions/handlers-async.md#cancellation-commit-and-all-exits)

### Interior mutability guardrails

[Cell contracts](../extensions/interior-mutability.md) govern local mutation,
dynamic guards and concurrent protocols. Operations declare their effects,
invariants, interference rules and exit behavior.

## Compiler route decision

The bounded release targets CHERI-C/Clight and the retained CHERI-CompCert
route. The [route comparison](compiler-route-contract.md) defines the evidence
a direct explicit-memory capability IR would need. Removing a representation
step still requires checked source transport, capability preservation, ABI
and linkage evidence, and the same final-image obligations. Any substitution
must satisfy the [affected VerifiedOS requirements](compiler-route-contract.md#conditional-amendment-and-reviewer-requirements).
Native verified self-hosting has its own
[compiler and bootstrap contract](../extensions/unified-source-contract.md#native-verified-compiler-and-self-hosting).

The [compiler and device producers](https://github.com/symbiogenesis/VerifiedOS/blob/main/PLAN.md)
own the retained backend, machine connection and functional Rust toolchain.
The [HoldFast delivery plan](../../PLAN.md#holdfast-first-release-delivery) tracks the
composition of their evidence with HoldFast's source and artifact receipts.

## Research and semantic boundaries

### Research Landscape

Decision-oriented survey of primary papers, docs, and repositories from 2024 onward (plus earlier foundational systems); not exhaustive. Links are the read evidence snapshots, not pinned dependencies or reproduced benchmarks. Each entry names its evidence kind (peer-reviewed theorem, maintained tool, artifact deposit, pen-and-paper metatheory) without inferring mechanization from venue. Licences come from each artifact's own file at incorporation, never from ecosystem, sibling, or forge badges ("unread" marks a survey gap, not permission). No surveyed toolchain delivers the requested combination on VerifiedOS's CHERI target; project-fit columns evaluate that target while keeping Rocq proof checking.

#### Rust and Low-Level Verification

| System | First-class verification and useful idea | Evidence boundary and project fit |
| --- | --- | --- |
| [Verus](https://verus-lang.github.io/verus/guide/) | Rust executable, spec, and proof modes; contracts, ghost state, inductive lemmas, SMT automation. Strong reference for integrated systems-programming UX. | Guide excludes verifying the verifier and Rust/LLVM compilers; solver verdicts are not Rocq certificates. Borrow UX/library layout; do not equate source proof with certified bytes. |
| [VerusBelt](https://iris-project.org/pdfs/2026-pldi-verusbelt.pdf), PLDI 2026 | Iris/Rocq soundness for Verus proof types (cells, invariants, resource algebras, storage protocols) with Rust lifetimes, concurrency, and mutable borrows, justifying type-check-then-spec-check. | Narrows Verus's gap without closing it: frontend, VCG, ghost erasure, and solvers remain trusted; stdlib specs, decreases measures, and invariant credits are outside the model. Grounds [manual proofs for HAL-adjacent `unsafe`](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-18-018) at the type-system level only, over a simplified modeled language. |
| [RefinedRust](https://plv.mpi-sws.org/refinedrust/) | Refined ownership types for safe/unsafe Rust in Iris with Rocq-checked proofs; suited to verified code behind safe APIs. | Soundness covers the embedded Rust model; Rust translation and compilation remain separate boundaries. Best Rust proof match for the Radium anchor, not all Rust/rustc. [Bringing Foundational Verification to Real-World Rust Code](https://doi.org/10.1145/3839484) (Gäher et al., OOPSLA 2026) extends RefinedRust in Iris/Rocq to traits, closures, iterators, and ACE security-monitor page-allocator verification over that embedded model. |
| [Corten](https://arxiv.org/abs/2609.04372) | Deep embedding of Rust THIR in Rocq with WP calculus and itree denotation via hax plus authors' extension; proves buddy-allocator alloc/dealloc safety. | September 2026 preprint (unfilled template venue) naming no repository, artifact deposit, or code URL—nothing to pin, inspect, licence, or reproduce. Unverified transpiler against rustc, untrusted borrow-checker oracle, single-threaded memory model. Unrelated to Verus-verified Asterinas CortenMM (Zhang et al., SOSP 2025). |
| [Aeneas](https://github.com/AeneasVerif/aeneas) | Charon MIR/LLBC translation to functional code for functional reasoning on Rust. | Qualify exact Rocq translation and Rust subset before reuse; [2024 symbolic borrow-checking](https://arxiv.org/abs/2404.02680) is not a verified rustc backend. Largest reported use—[SymCrypt Rust crypto](https://arxiv.org/abs/2609.15648) (Sept 2026 preprint: 16.7 KLOC Rust via 237 KLOC largely agent-written Lean, Charon/Aeneas still trusted)—is Lean-only; pilot Rocq subset first. |
| [hax](https://hax.cryspen.com/) and [hacspec lineage](https://hax.cryspen.com/publications/) | Rust-to-prover translation and spec-oriented Rust (notably crypto); 2025 hax paper shows multi-prover workflows. | Homepage lists Lean, F*, Rocq; tutorials emphasize Lean and F*. A listed backend does not imply feature parity or machine-code proof. Useful for executable specs; check Rocq per example. |
| [Creusot](https://github.com/creusot-rs/creusot) | Rust contracts and logical models for mutation; translates to Coma in Why3. | Why3/solver route gives no foundational Rocq lowering/compilation proof; interactive prover alone does not validate frontend. Donor for model views, post-borrow specs, and [prophecy-based ghost-state encodings preventing causality loops](https://inria.hal.science/hal-04816198v1/document) (Denis et al., HAL `hal-04816198`). Copyleft LGPL-2.1 licence (unlike permissive neighbors); read before reuse. |
| [Local commutation diagrams](https://hal.science/hal-05428143) (Reynaud Michez, JFLA 2026) | Mechanized structural soundness proofs for NLL-style borrow checking via local commutation diagrams (HAL `hal-05428143`). | Covers an abstract borrow-checking core without compiler lowering or CHERI provenance; lightweight proof-engineering comparator for HoldFast's `loan_soundness.v` CFG soundness layer. |
| [RustHornBelt](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf), PLDI 2022 | Machine-checked prophecy foundation in Rocq over lambda-Rust: typing judgments with first-order prophecy specs, proving `Vec`, `IterMut`, `Cell`, `Mutex`. | Verifies no Rust tool (covers lambda-Rust, not rustc/surface Rust/Creusot; notes unverified stdlib APIs). Transfers the sound borrow-end prophecy principle underlying restoration contracts. |
| [Flux](https://github.com/flux-rs/flux) | Refinement types in Rust for bounds/API invariants with predictable inference and concise diagnostics. | Refinement candidate, not general dependent prover or Rocq-to-binary chain; soundness covers a core calculus conditional on Stacked Borrows (non-normative). [FLEX](https://arxiv.org/abs/2607.12226) (July 2026 preprint) reimplements solving as Lean tactics with kernel-checked proofs for 95.7% of Flux benchmarks (constraint gen still trusted, Lean kernel); shows certificate-producing shape for [refinement tier](#layered-proof-and-staging), not a Rocq route. |
| [Thrust](https://www.riec.tohoku.ac.jp/~unno/papers/pldi2025.pdf), PLDI 2025 | Prophecy refinement types inferring loop/recursion invariants via constrained Horn clauses without aliasing reasoning. | Unmechanized: CHC/SMT solvers and Rust translation are trusted oracles; results are benchmarks. Repo promises dual grant in README without a licence file; artifact deposit states MIT inside a container bundling MPL-2.0 components. Inference is transferable as a proposal for Rocq to prove. |
| [Ante](https://antelang.org/blog/safe_cyclic_mutability/), 19 October 2026 design | Places, unstable places, and mutation effects allow local shared mutation while tracking reference invalidation. | Candidate for [HoldFast static invalidation](../extensions/interior-mutability.md#ante-as-a-candidate-for-static-invalidation), not a Rocq soundness or final-code theorem. [Producer disposition](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#ante-place-sensitive-mutation-and-invalidation) deferred; no rule/compiler selected. |
| [Evergreen](https://evergreenlang.net/) and [repository](https://github.com/jordan-bonecutter/evergreen) | Plane-tree memory/revision systems language with vacant slots (`T \| shape(T)`), named invariant conjuncts (`update(self) lifts ...`), two-step bulk relocation (`copy_representation` then `transfer_type`), and `starts_owner`. Includes Lean 4 mechanizations of 3-state RC conservation (`SharedOwnership.lean`) and affine-linear certificate checking (`Tier1Cert.lean`). | Rust frontend/checker (`crates/evg-Semantic`), plane-tree rules, and VCG are unverified; Lean 4 covers isolated sub-models only. No root licence file (only `web/public/fonts/UFL.txt`), so no code incorporated. Unspecified integer overflow violates [R-05-144](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-144); untagged `A \| B` breaks CHERI capability tags; whole-continuation branch replay with hidden drop flags conflicts with structured joins. Donor for `invariant Clause: ...` / `open (...) lifts ...`, `CopyRepresentation`/`TransferType`, and capacity-invariance gating; [producer disposition](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#evergreen-plane-tree-verification-selective-invariant-lifting-and-two-step-bulk-relocation) declines it as producer/anchor. |
| [Tree Borrows](https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf), PLDI 2025 | Rust aliasing model mechanized in Rocq/Simuliris, proving intraprocedural optimizations (including read-read reordering) while keeping most Stacked Borrows optimizations. | Non-normative; neither rustc, LLVM, nor Miri is proved against the Rocq model. Crate acceptance figure is empirical, not a theorem. Bounds aliasing assumptions; gives no CHERI capability provenance rule. |
| [Prusti](https://github.com/viperproject/prusti-dev) | Viper-backed Rust contracts with panic/overflow checking and IDE support. | Comparator only (inspected repo pins older nightly); Viper gives no admitted project proof evidence. |
| [Kani](https://github.com/model-checking/kani) | Bit-precise model checking, proof harnesses, nondeterministic inputs for unsafe-code bugs. | Strong counterexample finder, conditional on harness, ops, and unwinding. [Contracts, quantifiers, and stubbing](https://arxiv.org/abs/2607.01504) (ASE 2026) extend harnesses to unbounded verification (>16,000 stdlib harnesses/change), still as a CBMC verdict over unverified MIR, not a Rocq certificate. |
| [Verifying the Rust Standard Library](https://arxiv.org/abs/2606.17374), NFM 2026 | CI campaign running Kani, Flux, VeriFast, ESBMC, KMIR on stdlib `unsafe` UB challenges (OOB, dangling, uninit). | Covers named stdlib functions, not whole stdlib or applications; solver/model-checker verdicts with own frontends, no Rocq proofs. Map of tool capability, not admitted input. |
| [RefinedC](https://plv.mpi-sws.org/refinedc/) | C ownership/refinement annotations and Lithium automation in Iris/Rocq. | Strong proof-engineering precedent, but C model differs from CHERI-C. Reuse reasoning patterns or proved transport, not a second memory semantics. |
| [CN](https://doi.org/10.1145/3571194), [VST-A](https://doi.org/10.1145/3632911), [Iris for CompCert C](https://doi.org/10.1145/3632848) | Separation-logic refinements for C, foundational annotation proofs, and CompCert C integration with Iris. | Distinct boundaries (CN Cerberus/solver vs VST-A Coq). CompCert/Iris fits the C path best; using C alone does not prove CHERI. |
| [C*](https://arxiv.org/abs/2504.02246) | Programmable proofs and symbolic states in a C surface. | 2025 language-design experiment; detailed boundary assessed [below](#c-the-useful-idea-and-the-actual-boundary). |

For existing Rust components, evaluate RefinedRust first for foundational ownership and Aeneas when functional translation fits the safe fragment. Verus is an ergonomics comparator, not proof authority; RustBelt gives safety foundations (not a push-button crate verifier); RustHornBelt and VerusBelt prove modeled fragments sound, not verifiers correct.

#### What the Rust Verifiers Contribute

**Verus: proof resources need ownership too.** [Variable modes](https://verus-lang.github.io/verus/guide/reference-var-modes.html) separate runtime values, duplicable `ghost` math values, and affine/owned `tracked` erased proof resources (e.g., sequence snapshot vs cell-mutation permission). [Interior-mutability libraries](https://verus-lang.github.io/verus/guide/interior_mutability.html) separate cell identity from contents so invariants constrain observed values without promising an immutable snapshot. `spec`/`proof`/`exec` modes separate math, reasoning, and execution (quantifiers still need trigger/unfolding care). Its [assumptions guide](https://verus-lang.github.io/verus/guide/tcb.html) flags `assume`, external bodies, and external exec specs—mirrored by HoldFast's transitive assumptions audit with no silent external-body promotion. For `VerifiedComponents`, borrow this mode/library split inside the chosen separation logic rather than trusting a Rust-like checker or translating arbitrary Verus VCs to Rocq.

**Creusot: specify the end of a borrow.** [Guide](https://guide.creusot.rs/) and [architecture](https://github.com/creusot-rs/creusot/blob/master/ARCHITECTURE.md): Rust-to-Coma/Why3find using RustHorn prophecy variables (`*` current, `^` final in Pearlite) so pure logical values bypass ownership checks and container element borrows specify initial vs restored states without exposing the heap. Borrow borrow-end specs, model views, and stdlib specs in Rocq without adopting Coma or trusting its solver encoding.

**Prusti: make restoration obligations visible at the call site.** [Pledges](https://viperproject.github.io/prusti-dev/user-guide/verify/pledge.html) (`after_expiry`/`before_expiry`) state post-borrow obligations (e.g., `Vec` preserving length and untouched elements while updating the borrowed slot); its `trusted` wrappers show contract vocabulary only, and the [verification guide](https://viperproject.github.io/prusti-dev/user-guide/verify/summary.html) guarantees partial correctness only. Implement restoration lemmas directly and discharge termination separately.

Use Verus for erased permissions/authoring, Creusot/Prusti for borrow contracts, and RefinedRust for foundational ownership; annotation syntax never removes primitive, implementation, or binary-connection proof costs.

#### Dependent Types, Effects, and Ergonomics

| System | Contribution to the ideal language | Boundary to retain |
| --- | --- | --- |
| [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html) | Dependent programming, type-directed holes, resource protocols, QTT erased/linear/reusable quantities. | Compiler and totality checker are not the Rocq kernel; Scheme and RC-C backends do not give a GC-free, allocation-free CHERI runtime. |
| [F*, Low*, and Pulse](https://fstar-lang.org/) | Dependent types, indexed effects, ghost code, SMT/tactics, low-level imperative separation logic; [PulseCore](https://fstar-lang.org/papers/pulsecore-indirection-2025.pdf) (PLDI 2025) is foundational. | Logic is F*, not CIC; PulseCore does not make F* verification or extraction Rocq-checkable. [Pulse is now integrated into F*](https://github.com/FStarLang/pulse) (avoid judging from the old separate repo). |
| [Lean 4: mvcgen](https://lean-lang.org/doc/reference/4.34.0/The--mvcgen--tactic/) and [grind](https://lean-lang.org/doc/reference/4.34.0/The--grind--tactic/) | Monadic VCG and proof-producing SMT-style automation in one dependent language. [4.33.0](https://lean-lang.org/doc/reference/4.34.0/releases/v4.33.0/) `vcgen` frames resources across calls; [4.34.0](https://lean-lang.org/doc/reference/4.34.0/releases/v4.34.0/) (14 Sept 2026) adds in-code `requires`/`ensures` and `for … invariant` ([PR #14389](https://github.com/leanprover/lean4/pull/14389) for lists/ranges, excluding `while`/residual discharge; [PR #14596](https://github.com/leanprover/lean4/pull/14596) extends to effect-free containers). | Proofs are checked by Lean, not Rocq, and native compilation/runtime remain separate. Versioned 4.34.0 manual URLs are cited because `/latest/` mutates. `mvcgen` discharges only local assumptions, conjunctions, `mvcgen_trivial`, and `mleave` (using internal `Std.Internal.Do`), and `grind` bounds away combinatorial search—neither is general solver automation. Borrow UX/automation only. |
| [Dafny](https://dafny.org/) | Readable contracts, ghost methods, calculational proofs, datatype patterns, mature LSP; closest C#-style UX comparator. | Distinguish ordinary Dafny's solver/compiler from the [CPP 2026 HOL4-verified CakeML subset](#closest-matches-to-the-complete-workflow); neither gives Rocq/purecap or runtime guarantees. |
| [SPARK](https://www.adacore.com/about-spark) | Language-level contracts, explicit data flow, runtime-error freedom, pointer ownership in industrial systems. | Ada/GNAT tooling is not the Rocq/CHERI path; source proof/tool qualification do not prove the final binary. |
| [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/) | Refinements and equational proofs as code. | Haskell runtime and solver/compiler trust chain do not satisfy this target. |
| [Granule](https://github.com/granule-project/granule) and [Gerty](https://github.com/granule-project/gerty) | Graded, linear, dependent resource/effect/permission types (including 2024 fractional-uniqueness and ICFP 2026 graded/linear correspondence). | Research tools trusting external SMT oracles for grade constraints; general grades stay in source proofs until an admission obligation needs them, never creating new TAL grade axes. Separate licences: Granule is BSD 3-Clause; Gerty has a dual file (MIT for Agda-derived parser/syntax) and no licence on its project site. |
| [OxCaml](https://oxcaml.org/) | Modal memory management ([ICFP 2024](https://antonlorenzen.de/papers/oxidizing-ocaml-modal-memory-management.pdf)), [Data Race Freedom à la Mode](https://doi.org/10.1145/3704859) (POPL 2025), and [Mode Crossing](https://doi.org/10.1145/3828681) (ICFP 2026): inferred `local`/`unique`/`once`/`portable`/`contended` axes plus modal-kind mode crossing for deeply immutable types. | OCaml GC/Multicore runtime and Iris/Rocq soundness over modeled core calculi (not CHERI/CIC or final machine bytes); informs HoldFast's zero-boilerplate mode crossing for pure immutable types and locality/contention separation. |
| [Hylo](https://doi.org/10.5381/jot.2022.21.2.a2) (Mutable Value Semantics) | Memory safety and in-place updates via projections/subscripts (`let`/`inout`/`set`/`sink`) without pervasive surface lifetime annotations (Racordon et al., JOT 2022; ongoing compiler/projection work). | Unverified compiler without a Rocq/CHERI proof chain; ergonomic comparator alongside Swift `~Escapable`/`Span` and HoldFast's `in`/`ref`/`out`/`owned` plus place-named lifetimes. |
| [Kuiper](https://doi.org/10.1145/3808280), PLDI 2026 | Combines F* dependent types and Pulse concurrent separation logic for verified, high-performance GPU kernels (Martínez et al.). | F*/Pulse logic targeting SIMT GPUs rather than CIC/CHERI-RISC-V; strong precedent for uniting dependent index shapes with separation-logic framing on data-parallel/numerical kernels. |
| [SMTCoq](https://github.com/smtcoq/smtcoq), [Sniper](https://github.com/smtcoq/sniper)/Trakt, and Carcara | Reflective and certificate-producing SMT proof reconstruction for Rocq, using Trakt FOL preprocessing for inductive datatypes/arithmetic and Alethe checking. | Keeps external solvers outside the Rocq kernel via computational reflection or explicit certificates; subject to locked Rocq 9.3.0 compatibility, assumption audits, and license review before adoption. |
| [Mizar](http://mizar.org/) and [mizar-rs](https://github.com/digama0/mizar-rs) | Layered `by` proof checking (`prechecker` propositional refutation + `equalizer` combining congruence closure, algebraic property/reduction normalization, and `polyeval` polynomial arithmetic) and multi-fact `by` justifications (Carneiro, ITP 2023 / `arXiv:2304.08391`, whose independent checker uncovered four soundness bugs in Mizar's checker). | `mizar-rs` is GPL-3.0 and Mizar is set-theoretic rather than CIC; HoldFast reimplements the Equalizer, Prechecker, and multi-fact `by` ideas clean-room under Apache-2.0 as untrusted certificate producers whose synthesized terms must replay axiom-free in Rocq 9.3.0 (`Print Assumptions`, `rocqchk`). |

Agda, ATS (proof erasure with low-level code), Stainless/Scala, Spec#/Dafny, Koka effects/FBIP, and linear Haskell provide background design ideas without assessed deployment coverage; effects/linearity alone do not establish functional correctness, and adopting Koka's FBIP/AddressC ideas does not require Koka's runtime.

Progress concentrates in foundational Rust verification, live proof-state interaction, imperative dependent proofs (Pulse, Lean), and more trustworthy Rocq extraction. AI proof synthesis supplies candidate code/contracts/scripts only: generated contracts still need review and proofs need kernel checks. Kernel checking alone cannot defeat reward-hacking search: in 2026 a model exploited [a guard-checker bug](https://github.com/rocq-prover/rocq/issues/22382) accepting `False` in Rocq 9.2.0 (`rocqchk` included), and in [a Rocq agent benchmark](https://arxiv.org/abs/2603.20405) 14 proofs used `Admitted` and 6 redefined types while compiling cleanly. [The portable proof workflow](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-assistance.md#acceptance-boundary) therefore enforces statement preservation and assumption audits, while [the prover lock](https://github.com/symbiogenesis/VerifiedOS/blob/main/tools/opam/README.md) records locked-version kernel caveats.

#### Effect Handlers, Sharing and Protocol Logics

Upstream mechanized logics establish proof rules and counterexamples for their own modeled languages (never HoldFast's frames, cells, capabilities, or memory model); [the elaboration comparison](#type-theory-and-elaboration-reuse) tracks type-and-effect work, and the [handler](../extensions/handlers-async.md) and [mutability](../extensions/interior-mutability.md) dossiers own local obligations.

| System | Mechanized contribution | Boundary to retain |
| --- | --- | --- |
| [A Relational Separation Logic for Effect Handlers](https://iris-project.org/pdfs/2026-popl-blaze.pdf), POPL 2026 | Relational bind/frame/concurrency rules in Iris/Rocq relating programs with non-matching effects/handlers (e.g., effect-based async vs true concurrency). | Models an Iris handler calculus, not OCaml/Links/impls; proofs are manual per case study. Copyleft LGPL-3.0 Rocq development. |
| [Iris-WasmFX](https://iris-project.org/pdfs/2026-pldi-iriswasmfx.pdf), PLDI 2026 | Mechanized type soundness over WasmCert plus Iris program logic/logical relation for typed continuations (coroutine/generator case studies). | Tracks an unratified Wasm proposal with no verified engine or compiler; continuations live in a store rather than preassigned immovable frames. |
| [Formal Semantics and Program Logics for a Fragment of OCaml](https://iris-project.org/pdfs/2025-icfp-osiris.pdf), ICFP 2025 | Rocq semantics for OLang (sequential OCaml with refs, exceptions, deep/shallow handlers via operation-tree monad), Horus (pure Hoare logic), and Osiris (Iris separation logic). Nearest handler logic to a shipping language. | Typed-tree-to-OLang translator is trusted; semantics tested on ~900 test lines without compiler equivalence; concurrency, weak memory, and functors omitted. One-shot continuations only (for frame soundness), leaving [multi-shot handlers](#general-handlers-with-resource-safe-resumptions) uncovered. Host refused access during survey; licence unread. |
| [Leaf](https://doi.org/10.1145/3622798), OOPSLA 2023 | Iris/Rocq guarding operator turning propositions into shared versions (RW lock and hash table; temporary-sharing half of VerusBelt). | HeapLang-style model only (no machine code, compiler, allocator, OS). Repo supersedes the published artifact with a simplified core; [arXiv 2309.04851](https://arxiv.org/abs/2309.04851) is the extended non-record version. |
| [Iron](https://iris-project.org/pdfs/2019-popl-iron-final.pdf), POPL 2019 | Fractional resource accounting in concurrent Iris proving no resource leaks (including forked-thread disposal). Closest disposal-obligation precedent. | HeapLang model only, no allocator/OS, and no inference (discharges author-stated obligations). Licence unread during survey; read before incorporation. |
| [Nextgen](https://iris-project.org/pdfs/2025-cpp-nextgen.pdf), CPP 2025 | Modality for non-frame-preserving ghost updates across generations, applied to a separation logic for frame-clearing stack allocation. Shapes revocation/incarnation reuse. | Covers paper's own language, not C/Rust/HoldFast frames, compiler, or machine code. Upstream tree has no licence; archive deposit carries a content licence only, not a code grant. |
| [Mixtris](https://iris-project.org/pdfs/2026-oopsla-mixtris.pdf), OOPSLA 2026 | Rocq/Iris separation logic for mixed-choice multiparty message passing (extending Actris). | Partial correctness in model language only (leader election lacks liveness/termination/deadlock freedom, failures, or compiled code). Frozen archive under content licence with no maintained repo. |

#### Compilation and Executable Models

| System | What it establishes or enables | Consequence for this project |
| --- | --- | --- |
| [Live Verification in an Interactive Proof Assistant](https://doi.org/10.1145/3656439), PLDI 2024 | Incremental low-level programs and proofs inside Coq with symbolic state at cursor. | Closest Rocq-library-first UX precedent; smaller than a new language and runtime. |
| [Rupicola](https://github.com/mit-plv/rupicola) and [Bedrock2](https://github.com/mit-plv/bedrock2) | Relational compilation from functional models to imperative code, plus low-level verified compiler. | M1.6 built the stack and found its verified exit emits base RISC-V with zero capability instructions (violating [purecap-only](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-18-002)), while its C printer has no theorem. Reuse construction techniques; Clight transport needs its own proof. |
| [MetaRocq](https://metarocq.github.io/) | Quotation, verified typechecking, and erasure (2024 OCaml/Malfunction extraction, 2025 consolidated typechecking/erasure). | Useful metaprogramming/proof tools, not native compilation; safe checker assumes strong normalization. [1.5.1](https://github.com/MetaRocq/metarocq/releases/tag/v1.5.1-9.1) adds an unverified unsafe inductive-remapping phase (e.g., `nat` to GMP), so verified-erasure claims must list phases used. [1.5.1-9.2](https://github.com/MetaRocq/metarocq/releases/tag/v1.5.1-9.2) (16 June 2026) constrains [opam files](https://github.com/MetaRocq/metarocq/blob/v1.5.1-9.2/rocq-metarocq-utils.opam) to `rocq-core >= 9.2~ & < 9.3~`, excluding the locked [proof snapshot](../../tools/opam/rocq.lock); no local build claimed. |
| [CertiRocq](https://github.com/CertiRocq/certirocq) | Gallina compilation to Clight and WebAssembly. | Correctness covers selected passes; static-memory CHERI needs its own representation, runtime, and machine proof. |
| [Plinth/Plutus layered certification](https://webspace.science.uu.nl/~swier004/publications/2025-funarch.pdf), FUNARCH 2025 | Compilation traces connect independent passes to Rocq translation relations, decision procedures, and preservation proofs. | Design reference for [staged compiler evidence](../extensions/unified-source-contract.md#optimization-stages-and-evidence). Proves semantic relations only for DCE and nonrecursive-let; other levels check translation relations only or skip checks, supplying no CHERI, leakage, resource, or final-byte proof. |
| [Peregrine](https://types2026.cse.chalmers.se/abstracts/61.pdf), TYPES 2026 | Middle-end on Rocq extraction IR with verified textual deserialization and a Rocq spec of a large CakeML subset. | 4-page contributed abstract (unestablished post-proceedings status); diagram leaves new frontends, CakeML backend, and legacy-extracted middle-end unverified. Org repos lack uniform licensing (one frontend has none). |
| [CakeML](https://cakeml.org/) and [Pancake](https://cakeml.org/pancake.html) | CakeML: proof-producing compilation to machine code. Pancake: GC-free explicit-memory systems layers. | Strong feasibility evidence; different HOL foundation and targets prevent small Rocq adoption. |
| [Cogent](https://github.com/au-ts/cogent) and [Dargent](https://people.eng.unimelb.edu.au/rizkallahc/publications/dargent.pdf), POPL 2023 | Systems code/proof co-generation to C with Isabelle proofs; Dargent generates Isabelle layout proofs for bit-level getters/setters. | Closest high-level-spec + layout-control precedent. Compiler is certifying per-program rather than verified; Isabelle, C parser, AutoCorres, and C compiler stay trusted; bit-fields simulated; foreign C uncertified; no concurrency. Mixed per-file BSD 2-Clause / GPLv2 (compiler is GPLv2 copyleft). |
| [Jasmin](https://jasmin-lang.readthedocs.io/en/latest/) | Executable semantics, low-level control, Rocq-verified crypto compiler to assembly. | Safety analyzer and EasyCrypt proofs stay separate; does not prove linked CHERI bytes or HoldFast leakage. Borrow representation/instruction accountability. |
| [Verifying Peephole Rewriting in SSA Compiler IRs](https://doi.org/10.4230/LIPIcs.ITP.2024.9), ITP 2024 | Generic Lean SSA IR calculus (covering MLIR nested regions) proving once-proved peephole rewrites preserve denotational semantics. | Shows reusable validated-rewrite structure. MLIR/LLVM C++ and language semantics remain unconnected/unverified; each rewrite needs proof; Lean checking fails [translator rules](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020). |
| [CHERIoT Rust](https://github.com/CHERIoT-Platform/cheri-rust/tree/ba6e0e6c9c40593f7b47d5af071a6ccb9d154cf6) | Experimental capability-aware rustc/LLVM fork for CHERIoT (`compiler-builtins`, `core`, `alloc`). | Functional starting point for mandatory Rust producer; [source reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-reuse/languages.md#cheriot-rust-selected-functional-capability-aware-compiler-baseline) records RV32E/ABI differences, missing compartment/device interfaces, separate dependency rights, and certification gap. Adapt to RV64; keep MIR, CHERI-TAL, resource, and final-byte duties. |
| [RustCompCert](https://arxiv.org/abs/2602.07455) | Rust frontend over CompCertO lowering to Clight with Rocq semantics-preservation goals. | Ongoing Feb 2026 preprint: no finished theorem, artifact eval, or review; sequential subset without concurrency/`unsafe`. Adds a frontend atop CompCert rather than targeting Rust; inherits CompCert's non-commercial licence. |

F*/Low* with KaRaMeL, HACL*, Vale, and EverParse show high-performance native code from verified specs, without matching this repository's trust assumptions or runtime duties.

#### Closest Matches to the Complete Workflow

Assessments below read upstream results (no local reproduction); compare theorem subjects and supported components rather than feature lists.

**DeepSEA: the closest systems-language precedent.** [OOPSLA 2019](https://flint.cs.yale.edu/certikos/publications/deepsea19.pdf): integrates imperative code, pure Coq views, explicit representations, and certified abstraction layers via generated Clight refinement proofs and CompCertX (SHA-256, CertiKOS memory manager). Addresses `VerifiedComponents`'s spec/impl/refinement repetition with an implemented language, restricted to static allocation, selected loops, and a simple source type system; bottom-layer primitives still need separate proofs, and its endpoint is not CHERI/Sail. Inspect its representation generator without reproducing the full compiler. Terms restrict use to reading only: the public compiler descendant ships no independent licence beyond CompCert's non-commercial educational/research terms, blocking vendoring against [commercial rebuildability](#licensing-and-commercial-rebuildability). Its [2024 smart-contract work](https://arxiv.org/html/2405.08348v1) targets MiniC/EVM with gas-sensitive simulation, assumes false concrete Keccak injectivity, and leaves eWasm unproved; keep the systems and EVM branches separate.

**Sepref and Isabelle-LLVM:** [Generating Verified LLVM from Isabelle/HOL](https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.22/LIPIcs.ITP.2019.22.pdf) refines abstract algorithms to an LLVM shallow embedding (analogous to `Models`, `Representation`, `Build`), trusting the embedding, codegen, LLVM, and unbounded memory. [Parallel-refinement](https://www21.in.tum.de/~lammich/isabelle_llvm/) adds generic memory-parametric separation logic and scoped array splitting/index combinators (sorting case studies). Reuse the combinator design; porting Isabelle/HOL proofs, concurrency, and LLVM memory into Rocq/CHERI is separate work.

**Verified Dafny through CakeML:** [CPP 2026](https://arxiv.org/abs/2512.05262) ([full text](https://research.chalmers.se/publication/550353/file/550353_Fulltext.pdf), [mechanization](https://github.com/CakeML/cakeml/tree/751ecd45c16b11ee0c3fd1280be7a6d798b5c457/compiler/dafny)) formalizes a Dafny imperative subset (arrays, loops, mutual recursion) in HOL4 with a proved VCG and CakeML compilation (McCarthy 91 end-to-end). Parsing uses an untrusted Dafny S-expression frontend, and CakeML arrays/exceptions do not give HoldFast's static-memory runtime. Useful blueprint for separating frontend, VCG, proofs, and compiler theorem.

**Pancake:** [Verifying Device Drivers with Pancake](https://arxiv.org/html/2501.08249v1) (May 2025 arXiv follow-on to PLOS 2023) combines explicit-memory systems code, CakeML's HOL4 backend, and Viper automation near C speed, while trusting the Pancake-to-Viper translator, Viper/SMT, and linker and leaving driver reentry uncomposed with the compiler theorem (sound HOL4 Hoare logic offers a smaller TCB path). Follow-on [PLOS '26 LionsOS Ethernet driver](https://trustworthy.systems/publications/papers/Tyler_LZSWTH_26.pdf) notes the Rust transpiler remains in the TCB (HOL4 rewrite in progress) and encodes weak-memory assumptions itself. Neither supplies CHERI lowering.

**Fiat-Crypto and Bedrock2/Kami:** [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) emits proved Bedrock2 AST arithmetic; its README keeps language printers (including C) unproved (reuse under [crypto upstreams](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#the-cryptography-upstreams)). [Bedrock2](https://github.com/mit-plv/bedrock2) connects verified code/compiler to a Kami RISC-V processor for an IoT lightbulb—demonstrating full Coq SW/HW composition, though for ordinary RISC-V rather than pinned CHERI/Sail (M1.6's backend gap stands).

**seL4:** [Proof overview](https://sel4.org/Verification/proofs.html) and [assumptions](https://sel4.org/Verification/assumptions.html) document functional, binary, and config-dependent security proofs (hardware, boot/assembly, devices, and timing channels remain outside). Established delivered-artifact comparator at a different [proof-diversity boundary](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-016a), without purecap, HoldFast UX, or TAL.

**MachCSL:** [Kaashoek and Zeldovich's xv6 verification](https://arxiv.org/abs/2609.04043) builds an Iris separation logic over Sail RISC-V for concrete kernel images ([archived Rocq reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-reuse/languages.md#archived-machcsl-a-direct-sail-monad-logic-candidate-blocked-on-source-rights) records `swp`, bind/frame/WP rules, adequacy, and audit target). Active tree is now Lean; Rocq branch is unmaintained with no identified source grant. Useful architectural comparator for Q35, but replaces no machine logic or CHERI/tag/noninterference/timing/robust-preservation obligations.

#### Capability-Aware and Parametric Verification

**Memory-model-parametric symbolic execution:** [Next 700 Memory Models](https://arxiv.org/abs/2508.15576) (OOPSLA 2025; [extended CHERI scope](https://arxiv.org/html/2508.15576v2)) mechanizes generic compositional symbolic execution in Rocq with multiple memory instances. Its CHERI instance is a sequential idealized assembly model with over-approximation soundness (bug-finding under-approximation and Gillian integration are future work, with no CHERI-C or Sail connection). Inspect its memory-action and framing premises under Q2b; adopting its semantics directly still faces the semantic-anchor gate.

**Morello-Cerise:** [PLDI 2025](https://www.cl.cam.ac.uk/~pes20/pldi25-paper646-camera-ready.pdf) combines Cerise's Iris logical relation, Islaris, and T-CHERI to prove strong encapsulation for a sequential Arm Morello component linked with arbitrary untrusted code. Directly relevant to stronger guarantees beyond bounded-buffer functional theorems, though specific to one Morello component rather than CHERI-RISC-V compilers, concurrency, or this processor. Read under Q2b; Q3b owns the slice's evidence.

**RobustDimSum:** [POPL 2026](https://iris-project.org/pdfs/2026-popl-robustdimsum.pdf) compiles Rec (CompCert-style block memory) to Cap (Cerise-style capability machine), proving in Rocq via DimSum back-translation that Reckon-verified components stay safe against arbitrary Cap code. Limited to sequential code, idealized ABI, no Mem2Reg, and first-order ghost state (DimSum clashes with Iris countable step-indexing—a concrete composition risk for HoldFast's Iris logic). Closest mechanized robust-preservation comparator for SECOMP2CHERI, not a CHERI-RISC-V result; artifact licence unread.

**Gillian:** [TACAS 2023 CHERI-C](https://arxiv.org/abs/2211.07511) (Isabelle/HOL memory model + extracted concrete execution) is distinct from the later Rocq foundation. [Gillian-Rust](https://giltho.github.io/publications/Gillian-Rust.pdf) (PLDI 2025) pairs unsafe-Rust symbolic execution with Creusot prophecies; source verdicts are not Rocq certificates or binary proofs. Compare borrow contracts alongside RefinedRust, without replacing Radium.

#### Further Reuse and Emerging Compiler Work

| Project | Demonstrated contribution | Disposition for this proposal |
| --- | --- | --- |
| [Heapster](https://paulhe.com/assets/spec-extraction-oopsla.pdf) in [SAW](https://github.com/GaloisInc/saw-script) | Extracts functional specs from safe LLVM via permission types (Coq/itree soundness covers simplified assembly). | Reverse-direction comparator; extracted models still require independent contract review, LLVM ingestion/source/compilation/effect proofs. No SAW verdict admitted automatically. |
| [Quiver](https://plv.mpi-sws.org/quiver/), PLDI 2024 | Abductively completes C separation-logic spec sketches and emits Rocq/Iris proofs (search outside TCB). | Closest published shape for typed holes: sketch + checked completion. No theorem guarantees intended/strongest spec or completeness, and soundness is over RefinedC's C model rather than binaries. Repo terms unread (only deposit content licence reachable). |
| [Rocqet](https://github.com/rocqetry/rocqet), PLDI 2025 | Nested family polymorphism for extensible definitions/proofs (extensible certified-C compiler case study). | Relevant for refactoring semantic families; documented Rocq/OCaml tuple needs local qualification. Not a CHERI backend; defer until reuse demands it over ordinary modules. |
| [Pyrosome](https://github.com/DIJamner/pyrosome), [2026 thesis](https://www.csail.mit.edu/event/framework-modular-metatheory-and-verified-compilation) | Modular Rocq metatheory and composable verified translation (System F + refs, imperative, linear calculi); *Verified E-Graphs for Automating Compiler Verification* (Jamner, Askerbekov, Chlipala, accepted POPL 2027, [chlipala.net](https://chlipala.net)) adds verified object-language-generic `egglog`-style EqSat directly inside Rocq without post-hoc certificate generation. | Research framework over Pyrosome object languages, not a production CHERI-RISC-V backend or source-correspondence proof; complements HoldFast's untrusted `VersionedEGraph` certificate producer. |
| [Slotted E-Graphs](https://doi.org/10.1145/3729326), PLDI 2025 | First-class bound variables and alpha-equivalence inside equality saturation (Schneider et al.). | Unverified Rust library rather than a Rocq kernel checker; informs extending HoldFast's `VersionedEGraph` to binder-bearing dependent terms and lambdas without capture bugs. |
| [Exo 2](https://doi.org/10.1145/3669940.3707218), ASPLOS 2025 | User-schedulable optimization libraries via typed cursors separating algorithm specification from low-level hardware/SIMD schedules ([arXiv:2411.07211](https://arxiv.org/abs/2411.07211)). | Python-hosted USL with SMT checks, not Rocq/CHERI; informs HoldFast's separation of algorithm contracts from target-specific loop/SIMD/layout schedules. |
| [Crane](https://bloomberg.github.io/crane/), [RocqPL 2026](https://bloomberg.github.io/crane/papers/crane-rocqpl26.pdf) | Extracts Rocq to modern C++ with configurable data mappings. | Integration/ergonomics reference; unverified extractor and runtime mappings do not support static-memory CHERI. Host-integration option only. |
| [Verity](https://github.com/lfglabs-dev/verity) and powdr [Yul-to-EVM](https://github.com/powdr-labs/yul-compiler) | Lean contract/proof construction and verified Yul-to-EVM lowering ([July 2026 theorem](https://powdr.org/blog/yul-compiler) under matching-state/gas premises). | Verity's [trust assumptions](https://github.com/lfglabs-dev/verity/blob/main/TRUST_ASSUMPTIONS.md) retain an IR-to-Yul bridge hypothesis and trusted `solc`. Separate toolchains/targets; neither gives composition nor Rocq/CHERI admission. |

Inspect construction and representation solutions first, capability-law interfaces second, and multi-language framework infrastructure only when needed.

#### Embedded Verification and Certified Synthesis

Evaluate embedded surfaces and proof-producing builders for notation, rules, and certificates without confusing upstream demos for locally reproduced integrations.

**AddressC and MiniC:** [AddressC](https://github.com/koka-lang/AddressC) ([FIP tree report](https://www.microsoft.com/en-us/research/publication/fiptree-tr/), PLDI 2024) provides functions, mutable locals, loops, and struct notation over Iris HeapLang + Diaframe (partial correctness, Coq 8.19.1, MIT licence with separate Iris/Diaframe/std++ trees). Rocq-native authoring comparator alongside LiveVerif, not a C compiler, verified Koka backend, or CHERI representation. Its predecessor [MiniC](https://gitlab.mpi-sws.org/iris/c) (monadic HeapLang embedding with VCG) is explicitly unmaintained; read as historical reference only.

**SuSLik:** [SuSLik](https://github.com/TyGuS/suslik) ([certification](https://github.com/TyGuS/suslik/blob/master/certification.md), [ICFP 2021](https://doi.org/10.1145/3473589)) synthesizes heap programs from separation logic and emits HTT/Iris/VST certificates (search outside TCB). Coverage varies, HTT defaults to `Admitted` pure lemmas unless enabled, advanced cases need manual pure proofs, and the paper's memory model assumes infallible allocation; no CHERI connection. Licences split: synthesizer is BSD 2-Clause, while certification backends declare GPL-3.0 in package metadata without a licence file. Qualify emitted certificates and assumptions strictly.

**CFML and Sisyphus:** [CFML](https://github.com/charguer/cfml) (Coq 8.20, OCaml < 5) translates OCaml to Rocq ASTs with characteristic formulas, ownership, and time credits (frontend/compiler remain separate). [Sisyphus](https://verse-lab.org/sisyphus/) repairs CFML proofs across algorithm edits on 14 OCaml programs (focused maintenance experiment, AGPLv3+ advertised). Read for repair patterns without admitting OCaml runtime/logic.

**Perennial/Goose:** [Perennial](https://github.com/mit-pdos/perennial) builds crash-WP, concurrency, and recovery on Iris (already selected for the Gallina journal/GoJournal work; not a proposal to ship Go). [Goose](https://github.com/goose-lang/goose) trusts Go-to-model translation and underwent a breaking migration; pin edition, crash model, and semantics explicitly.

**FP2 and creditmonad:** [FP2](https://www.microsoft.com/en-us/research/publication/fp2-fully-in-place-functional-programming/) (MSR-TR-2023-19 extended report, distinct from ICFP 2023 Article 198—cite whichever is read) defines an allocation-free, constant-stack linear calculus with pen-and-paper proofs only; Koka implements it via Perceus reference counting (also pen-and-paper, requiring cycle freedom). Investigate static reuse for bounded components without importing RC runtimes. [creditmonad](https://github.com/anfelor/creditmonad) tests amortized persistent-DS costs in Haskell (falsification only, neither universal bounds nor WCET).

**Velvet/Loom and LeetProof:** [Velvet](https://github.com/verse-lab/velvet) on [Loom](https://github.com/verse-lab/loom) ([POPL 2026](https://doi.org/10.1145/3776719), monad-transformer VCG proved sound in Lean; also Veil) pairs Dafny-like syntax, property tests, and Lean tactics or Z3/cvc5 (Lean-Auto/lean-smt; kernel proof depends on reconstruction). Closest interaction comparator, not Rocq/CHERI. [LeetProof](https://arxiv.org/abs/2604.16584) validates contracts before proof effort by testing intended vs deliberately wrong outputs (uniqueness applies only to deterministic contracts; property tests/LLM reviews do not prove intent; testing `sorry` guards stay outside accepted proofs).

**Priority:** read AddressC and SuSLik first (surface/certificate synthesis), Velvet/Loom/LeetProof for workflow/spec testing, Perennial within journal work, CFML/Sisyphus and FP2 as focused references, and creditmonad/MiniC as testing/historical references. None supplies missing CHERI primitive rules.

#### Research That Changes the Experiments

**Optimization reuse (CompCert Chamois):** [Chamois-CompCert](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/) ([JFLA 24](https://www.pepr-cyber-arsene.fr/publications/jfla24.pdf)) provides verified/BTL-validated passes; postpass scheduling is documented for KVX/ARM32/AArch64, while the [RISC-V fork](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-Arsene/index-chamois-riscv.html) (Nov 2024) lists block opts, CSE, loop rotation/unrolling, and CFC without scheduling. M1.3 evaluates reuse inside the retained backend (not a speed-only checker); ordinary CompCert guarantees do not establish CHERI tags, traps, isolation, constant time, or cost bounds, and licence/dependencies must be read directly. [CompCert's overview](https://compcert.org/compcert-C.html) reports ~90% of GCC `-O1` on ARMv8 (weaker on aggressive loop code); measure actual clients rather than extrapolating.

**Representation and primitive contracts:** [VeriFFI](https://www.cs.princeton.edu/~appel/papers/VeriFFI.pdf) generates VST specs from Gallina types/models; reuse requires a compatible VST version and assumption replay.

**Borrowing precision:** [Polonius Alpha](https://blog.rust-lang.org/2026/08/04/enabling-polonius-alpha-on-nightly/) distinguishes branch-returned vs released loans (its conditional loop reborrow goes beyond [synchronous loan rules](../language/core-design.md#loans-and-control-flow)); the [Rust borrow-checker roadmap](https://goals.rust-lang.org/2026/roadmap-borrow-checker-within.html) compares partial borrows and place-named lifetimes. Any reuse needs a checked HoldFast interpretation.

**Lifetimes without annotations (Goose):** van Oortmerssen's [Goose](https://github.com/aardappel/goose) (`master` `49d42ee7`, 2026-09-18; distinct from Perennial's Goose) specializes call graphs per static root variable so references store only inside enclosing root scopes without lifetime syntax, using bump-grown data stacks and hidden return-discriminant `return from` without unwinding. Those premises align with HoldFast platform constraints (whole-program composition, [no runtime allocator](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-010), [static recursion depth](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-116), [bounded recursive data](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-143), [no unwinding](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-100)). UX comparators: per-root specialization admits field-stored loans (absent in [synchronous slice](../language/core-design.md#loans-and-control-flow)) at the cost of code growth ([feature decisions](#feature-decisions)) and indirect-call joins over [typed callee sets](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-114) ([closures/fn-ptrs stay](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-115)); capacity-bounded append as a tail write disjoint from prefix leaves prefix loans alive ([fixed-capacity write rule](../language/core-design.md#dependency-and-joins), [tail view](#flow-sensitive-loans-and-restoration-contracts)); named-ancestor return elaborates to [`Result` propagation](../language/core-design.md#loans-and-control-flow) with per-frame restoration/cleanup and WCET branches. No surface feature is scheduled. Goose's spec gives informal soundness arguments and commodity benchmarks (Apache-2.0 on forge, licence file unread), and three choices are refused here: virtual-memory demand-grown data stacks with guard pages ([R-15-189b](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-15-189b) forbids overcommit), slot-reusing pools allowing stale same-typed access (blocked by [reuse gate R-08-015](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-015) and [pool confidentiality R-08-046](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-046)), and no-shared-concurrency aliasing omissions ([R-05-096a](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-096a) needs exclusive loans across [shared-semantics presets](../extensions/assurance-profiles.md)). Its union dichotomy adds nothing over loan trees.

**Resource inference (RaRust and RaML):** [RaRust](https://arxiv.org/html/2502.19810v1) (OOPSLA 2025) infers linear `tick` bounds for safe Rust via shared/prophecy potentials (pen-and-paper soundness; excludes unsafe, generics, closures, trait objects, nonlinear bounds). [RaML](https://www.raml.co/about/) infers polynomial/expected OCaml bounds via LP (pen-and-paper soundness, unverified implementation, unmaintained 2020 tarball bundling non-commercial CompCert examples alongside BSD 2-Clause files—do not vendor). Untrusted analyzers may suggest bounds for Rocq to prove, never certificates or WCET bounds; no analyzer port is scheduled.

**Time, progress, and schedulability:** Three mechanized donors each leave target timing as a premise: [ParCAS](https://iris-project.org/pdfs/2026-icfp-parcas.pdf) (ICFP 2026) proves explicit-constant work/span bounds in Rocq/Iris over fork-join graphs (not wall-clock processor time; transfers composable branch credit accounting); [Lilo](https://iris-project.org/pdfs/2025-oopsla-lilo.pdf) (OOPSLA 2025) mechanizes termination-sensitive fair refinement in non-Iris Rocq assuming yield-interleaving scheduler fairness (HoldFast's cooperative reaction graph lacks fairness and step-indexing prevents direct Iris composition); [RefinedProsa](https://iris-project.org/pdfs/2025-pldi-refinedprosa.pdf) (PLDI 2025) links RefinedC scheduler trace invariants to Prosa response-time bounds while taking action/callback WCETs, arrival curves, and an axiomatized syscall as assumptions without compiler/hardware proofs (BSD 3-Clause code + deposit content licence).

**Specification coverage:** [Static Coverage](https://www.amazon.science/publications/static-coverage-in-deductive-software-verification) (FMCAD 2025) uses Boogie/Dafny unsat cores to detect vacuity and unconstrained behavior. HoldFast applies the same idea in [the weakening probe](workflow-contract.md#change-and-weakening-probes) (dropping copied-prefix equality from the postcondition so expected-byte checks catch it); neither implies a Boogie-to-Rocq tool nor proves informal intent.

**Proof stability:** [OOPSLA 2025 Dafny study](https://cseweb.ucsd.edu/~mcoblenz/assets/pdf/OOPSLA_2025_Dafny.pdf) documents qualitative debugging/hardening/review costs; Dafny's [optimization guide](https://dafny.org/dafny/VerificationOptimization/VerificationOptimization) contributes obligation isolation, resource inspection, and seed variation. [The workflow contract](workflow-contract.md#measurement-record-and-sampling) tracks diagnostic latency, review effort, and [change probes](workflow-contract.md#change-and-weakening-probes) separately without importing Dafny.

**Certified search:** Offline placement search can feed existing validators under [R-05-066](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-066); infeasibility claims require kernel-replayed proofs binding the concrete instance/encoding under [the alternatives register](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#certified-placement-and-infeasibility-no-new-certificate-machinery).

Adoption depends on version, client theorem, generated-code boundary, transitive assumptions, licence, and measured benefit.

#### 2025–2026 Algorithmic, Complexity, and Proof-Checking Breakthroughs

HoldFast adopts 2025–2026 results only where they improve proof reconstruction, kernel-bypass safety, static-memory data structures, or analysis convergence without enlarging the TCB.

| Discovery | HoldFast integration | Assurance boundary |
| --- | --- | --- |
| Versioned E-Graphs (Cesario et al., PLDI 2026, [DOI 10.1145/3808249](https://doi.org/10.1145/3808249)) | [VersionedEGraph](../../tools/toolchain/proof_certificates.py) and [proof elaboration](../../tools/toolchain/elaborate_proofs.py) share branch equivalences via trail-backed `push_version`/`pop_version` scopes and emit shortest-path `Refl`/`Symm`/`Trans`/`Congr` terms; [VersionedEGraph.saturate_equalizer](../../tools/toolchain/proof_certificates.py), `NatPolyEqualizer`, and `PropositionalPrechecker` add bounded AC/property/reduction saturation, reflective `Nat` polynomial normalization via `holdfast_npoly_sound`, unit propagation, and bounded `bool_match` tableau reconstruction; [Slotted E-Graphs](https://doi.org/10.1145/3729326) (PLDI 2025) and [Verified E-Graphs in Pyrosome](https://chlipala.net) (accepted POPL 2027) inform binder-aware and reflective-kernel extensions. | Untrusted producer checked by Rocq 9.3.0 (`Print Assumptions`, `rocqchk`); ill-typed dependent `Congr` args fall back cleanly. |
| Certificate-producing arithmetic & skeletons (FLEX July 2026; CPC CAV 2026; Ethos & Proof Skeletons IJCAR 2026) | [NatDifferenceProver](../../tools/toolchain/proof_certificates.py), [FixedIntOrderProver](../../tools/toolchain/proof_certificates.py), and [prelude lemmas](../../tools/toolchain/elaborate_types.py) reconstruct `nat` difference-logic chains, fixed-width (`u8`–`i64`, `usize`) order chains, and unreachable-branch contradictions. | Zero solver-trust axioms; every certificate replays in Rocq within search budget. |
| Rocq 9.2–9.3 `SProp` & sort polymorphism ([Rocq 9.3.0 Sorts](https://rocq-prover.org/doc/V9.3.0/refman/language/core/sorts.html)) | Sort polymorphism across `Type`/`Prop`/`SProp`, primitive projections for `SProp`-only records, kernel squashing of irrelevant terms during conversion, and native `SProp` `Scheme` generation (`T_sind`/`T_scase`). | Enables definitional proof irrelevance and faster irrelevant-proof conversion inside locked Rocq 9.3.0 without global UIP or `-allow-rewrite-rules`; retains subsingleton elimination limits. |
| [Trocq modular proof transfer](https://doi.org/10.1145/3737283) (Cohen, Crance, Mahboubi, TOPLAS 2025) | Expanded parametricity-based proof transfer in Rocq *without* univalence or extra axioms. | Candidate for [representation-transfer comparison](workflow-contract.md#representation-transfer-comparison), subject to locked Rocq 9.3.0 compatibility, assumption audit, and package-trial benefit measurement. |
| Guard-checker fixes & bypass auditing (Rocq #22382 / CVE-2026-72705 patched in 9.3.0; arXiv:2603.20405) | [The solver ledger](../../tools/toolchain/solver_ledger.py) strips nested comments and refuses `Parameter`/`Conjecture`/`Admitted`/`admit` and `Unset Guard/Positivity/Universe Checking` or `Set Type in Type`; `check_prover_version` requires Rocq `>= 9.3.0`. | Supplements statement preservation and `Print Assumptions`; does not establish informal-intent adequacy. |
| Funnel & Elastic hashing (Farach-Colton, Krapivin, Kuszmaul, FOCS 2025, disproving Yao's 1985 conjecture) | [FunnelTable](../../tools/rocq/funnel_table.v) mechanizes fixed-capacity funnel layouts in Rocq 9.3.0 (bounds, level disjointness, non-reordering slot immutability, completeness, fail-closed exhaustion, bounded probes). | Targets extreme load ($\delta < 0.05$) in zero-heap immovable storage; linear probing still wins at moderate loads via locality. |
| Reverse-postorder iterative dominators | [Loan CFG validation](../../tools/toolchain/loans.py) computes reachability + RPO in one DFS pass and converges dominators in 1–2 passes on reducible graphs. | Preserves exact dominators and irreducible-cycle refusals; diagnostic engine stays outside target certificates. |

**Evaluated 2025–2026 results not incorporated:**

- **Unreviewed late-2026 AI-assisted complexity/math claims** (Oct 2026 ETH disproofs, Oct 2026 *The Unique Games Theorem*, Nov 2026 $\text{VP} \neq \text{VNP}$, Aaronson–Ambainis formalizations, Millennium claims): unreviewed preprints or non-compiler separations; operational bypass lesson is enforced in [the solver ledger](../../tools/toolchain/solver_ledger.py).
- **Sub-sorting directed shortest paths** (Duan, Mao, Mao, Shu, Yin, STOC 2025, $O(m \log^{2/3} n)$): targets huge sparse graphs; HoldFast's bounded CFGs/proof graphs ($n \le 256$) and difference-logic cycle checks are faster with BFS/Bellman-Ford.
- **Time-in-square-root-space simulation** (Ryan Williams, STOC 2025, $O(\sqrt{t \log t})$ via Cook–Mertz tree eval): algebraic overhead mismatches static-memory CHERI execution.
- **Linear-time planar 4-coloring / near-linear Vizing edge coloring** (Inoue et al., FOCS 2026; STOC 2025): does not replace non-planar interference-graph register allocation in CHERI-CompCert.

### What a Golden Binary Can Mean

An executable binary is not its own correctness oracle. The target is a **proof-carrying executable reference implementation**: exact bytes, interpreted under a named target semantics, proved to refine an independently reviewed contract. For VerifiedOS, that semantics is the pinned Sail term (or a [qualified successor](../extensions/unified-source-contract.md#migration-and-retirement) shared by binary and hardware proofs); other targets need their own interpretation and artifact theorems. An optimized build can then act as a fast oracle; the portable asset is the contract and reusable proof structure, not a universal binary or target-independent timing theorem. Independent specification review and differential tests remain required so a wrong specification cannot agree with itself unnoticed.

The evidence chain separates five judgments:

- Source elaboration preserves authored program and contract meaning.
- Concrete representation implements abstract values and state transitions.
- Compilation, assembly, linking, and image construction preserve behavior.
- Final bytes satisfy admission properties under the pinned Sail model.
- Hardware implements that model at the claimed tier.

Different target binaries may implement one contract via different representations if I/O encodings and permitted observations are explicitly related. Differential comparison on nondeterministic/underspecified contracts must respect allowed behavior rather than require byte-identical traces.

Functional refinement alone does not prove constant-time behavior, WCET, zero hidden allocation, or robust isolation against adversarial linked code—those belong to the [specification](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md) and [admission language](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/typed-assembly-language.md), never closed implicitly by an optimizer or SMT verdict.

### C*: The Useful Idea and the Actual Boundary

[C*: Unifying Programming and Verification in C](https://arxiv.org/html/2504.02246v1), April 2025, unifies executable C, assertions, and programmable proof blocks in C syntax so authors inspect symbolic state, apply proved lemmas, and continue coding in one surface.

Implementation and evaluation limits:

- Proof kernel is HOL Light via a C interface, not Coq/Rocq.
- Symbolic execution engine is trusted; a small LCF kernel does not validate its C semantics.
- Separation logic is axiomatized with integers and pointers conflated, unlike HoldFast's purecap provenance model.
- Prototype manually interleaves symbolic executor runs (live IDE is future work).
- Evaluation covers small examples and buddy-allocator `attach`, not a full allocator or compiler-to-binary theorem.
- Authors retain a weaker allocator spec omitting free-list completeness—a warning on spec adequacy.

**Disposition:** borrow the integrated proof-block workflow and state-transformation libraries inside a Rocq-native workflow over selected logics; do not import HOL Light, trust its symbolic executor, or infer CHERI compilation from C syntax.

### Idris Flexibility Without an Idris Runtime

Idris 2's [quantities](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html) ([v0.8.0](https://github.com/idris-lang/Idris2/releases/tag/v0.8.0)) separate erased, linear (`1`), and unrestricted values—expressing evolving ownership protocols and erased indices—but linear parameter use does not imply unique ownership of reachable storage, stack allocation, GC freedom, or Rust-style temporary lifetime borrows. Its [theorem guide](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html) notes totality-checker limits, and its [backend docs](https://idris2.readthedocs.io/en/latest/backends/index.html) list Scheme and RC-C without verified CHERI compilation. Idris 2 is a design reference only.

The architecture splits into:

- **Specification/proof world:** dependent functions, indexed families, existentials, induction, math, and verified algorithms elaborated into CIC with accepted assumptions only and zero proof holes.
- **Runtime world:** finite representations, machine integers, bounded arrays, regions/handles (CHERI capabilities in VerifiedOS), ownership/borrowing, and static effects; rich types describe values without existing at runtime.
- **Proof automation:** search may time out or fail; only checked proof terms succeed, and tactic nontermination never ships.

HoldFast does not embed Idris 2 unchanged into Rocq: universes, conversion, positivity, equality elimination, and quantitative resource rules require explicit mapping, and `owned` requires a semantic soundness proof in the program logic (exposed initially via predicates and proved combinators). Erasure requires that terms differing only in proof data share relevant behavior; runtime loops read represented lengths or specialized constants, never erased existential lengths.

#### Reading the Graded-Type Claims

Idris 2's fixed quantities reflect one implementation of Atkey and McBride's QTT ([ECOOP 2021](https://arxiv.org/abs/2104.00480)), not extensible grading algebras; distinguish parameterized calculi, fixed-grade prototypes, and extensible production languages.

**Idris 2 libraries:** its [linear IO library](https://github.com/idris-lang/Idris2/blob/v0.8.0/libs/linear/Control/Linear/LIO.idr) (`v0.8.0`) indexes `L` by result usage (`Pure0`, `Pure1`, `PureW`), duplicating definitions due to lacking multiplicity polymorphism (`Usage` does not alter the core algebra). Immediate lesson: build state-indexed ops and proved combinators now rather than waiting for full grade generality.

**Granule:** indexed (non-dependent) graded-language lab ([guide](https://granule-project.github.io/granule.html), [impl](https://github.com/granule-project/granule) to Haskell runtime or experimental LLVM) demonstrating exact-use modalities (e.g., `(a -> b) [n] -> Vec n a -> Vec n b`, multiplicative `twice`), security lattices, and IO effects. These interpretations are distinct (exact callback counts do not fix traversal order), and programmer-customizable modalities remain aspirational. Its [derived distributive combinators](https://arxiv.org/abs/2112.14966) and [grade-directed synthesis](https://doi.org/10.1007/978-3-031-57262-3_4) require [conditional HoldFast qualification](../extensions/graded-foundation.md#conditional-usability-producers) (real client, checked output, measured benefit) and are outside the first release.

**Gerty:** implements GrTT's split of computation use and type use ([ESOP 2021 preprint](https://arxiv.org/html/2010.13163v2), [repo](https://github.com/granule-project/gerty)), e.g., `(a : (.0, .2) Type 0)`, recovering restricted parametricity subject to elimination and modal rules. Strong normalization is pen-and-paper for a two-universe fragment only; the prototype trusts external SMT constraints and is unverified. Its `--tyc-optimise` skips codomain substitution on zero type-use (small fanout benchmarks, sensitive to SMT overhead) without skipping validity checks; first-class grade terms and internal semirings remain future work.

**GraD:** [Usage-Aware Semantics](https://arxiv.org/html/2011.04070v2) uses a partially ordered semiring and heap usage semantics (discarding type-use counts at runtime demand), showing ordinary progress/preservation does not prove resource accounting. Derives irrelevance noninterference and single-pointer properties under extra algebraic laws, with Coq mechanization of selected syntax only and `Type : Type` (unsafe as a proof logic; retain CIC universes). Meaning depends on algebraic structure (e.g., Boolean `1 + 1 = 1` does not give single use), and GraD's heap pointer property is not CHERI capability safety, DMA, or revocation; similarly security lattices need noninterference proofs, privacy budgets need probabilistic sensitivity, and op counts need instruction/WCET bridges.

**Proto-Quipper:** [arXiv:2004.13472](https://arxiv.org/abs/2004.13472) / [LICS 2020](https://doi.org/10.1145/3373718.3394765) / LMCS 2022 separates linear quantum resources from duplicable classical circuit indices and explicit uncomputation/disposal; quantum semantics add no classical systems benefit.

**Abel, Danielsson, and Eriksson (Agda erasure):** [ICFP 2023](https://research.chalmers.se/en/publication/537991) and its [extended version](https://arxiv.org/abs/2603.29716) (revised 30 April 2026, adding unit and graded dependent pairs) formalize consistency, normalization, decidable definitional equality, grade preservation, and extraction soundness in Agda (trusted checker; MIT-licensed shared multi-paper repo requiring tag pinning). Extraction soundness holds only for restricted modalities, `Nat`-typed programs, erasable consistent contexts, and no erased matching on weak pairs, without transferring directly to CIC, mutable state, or handlers.

**Two 2026 Agda erasure results:** Danielsson ([arXiv:2609.08578](https://arxiv.org/abs/2609.08578), 8 Sept 2026) proves transport along erased identity proofs safe without quotients/postulates (or with equality reflection), but incompatible with erased postulated univalence—informing [elaborator-inserted transports](#layered-proof-and-staging). Theocharis and Brady ([arXiv:2605.00655](https://arxiv.org/abs/2605.00655), FSCD 2026) frame erasure as a phase proposition conservative over MLTT with gluing extraction soundness and a toy elaborator (assuming funext, UIP, QIITs), backing HoldFast's separation of [phase/representation](../extensions/graded-foundation.md#dimensions-and-lawful-domains) from computation use. Both target MLTT without impredicative `Prop`, state, or handlers; source terms unread.

**Dependent multiplicities:** Doré ([arXiv:2507.08759](https://arxiv.org/abs/2507.08759), revised 19 May 2026, no venue) embeds index-dependent multiplicities (e.g., leaf-exact tree recursors) into unmodified dependent type theory via supply witnesses, checking type-former lemmas in Agda with hand-built witnesses for value linearity (not cost bounds). Closest precedent for [host-interpreted index grades](../extensions/graded-foundation.md#substitution-and-structural-rules); claims Rocq portability without a build, and anonymous artifact terms are unread.

**Rocq erasure vs erased indices:** Standard extraction and MetaRocq erase only `Prop`/`SProp`, leaving `Type` indices like `fin`'s `Nat` live. Rosain, Sozeau, and Winterhalter's [TYPES 2025 ghost-sort abstract](https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper81.pdf) explores sort-polymorphic elimination in Rocq/MetaRocq, whereas [Rocq 9.3.0](https://rocq-prover.org/doc/V9.3.0/refman/language/core/sorts.html) keeps `SProp`/`Prop`/`Set`/`Type` and HoldFast avoids kernel changes. [DCOIω](https://doi.org/10.1145/3704843) (Liu, Chan, Weirich, POPL 2025) mechanizes consistent, normalizing dependency-tracked irrelevance in Coq; its indistinguishability conversion is absent from CIC, making it a proof-engineering donor for [substitution/erasure debts](../extensions/graded-foundation.md#proof-and-qualification-obligations) rather than an elaboration target (Coq version/terms unread).

**Design consequence:** adopt [graded dependent typing](#graded-dependent-foundation) with separate interpretations for representation, erasure, ownership, protocol state, effects, and quantitative bounds, discharging initial needs via library proofs under [the composition contract](../extensions/full-language-review.md#implementation-obligations).

## Language design and target interfaces

### Target Abstraction and Tooling Evolution

Abstraction hides target details from authors, not from the proof chain: source portability, generic proof reuse, concrete representation, and artifact security remain separate obligations, and a small interface never shrinks target compiler/memory/hardware proofs.

#### Portable Interfaces and Concrete Instances

| Layer | Reusable content | Instance-specific evidence |
| --- | --- | --- |
| Language and editor | Syntax, dependent contracts, proof interaction, source locations, diagnostic protocol | Interpretation of target-sensitive features and profile compatibility |
| Pure specifications | Abstract sequences, algorithm results, format meaning, protocol transitions | Encodings and relationships to represented input/output values |
| Operation and resource interfaces | Ownership, scoped borrows, framing, explicit effects, primitive contracts | Sound implementation of each operation and law in the chosen program logic |
| Program construction | Generic induction and composition over proved primitive rules | Concrete program terms, numeric limits, layout, ABI, and compilation preservation |
| Artifact evidence | Dependency tracking, proof orchestration, explicit theorem subjects | Binary semantics, permitted contexts, linking, observation/leakage model, hardware assumptions |

Schematic bounded-buffer interface:

```text
interface IBufferStorage<Handle> {
    type Index;
    predicate Owns(Handle target, Seq<byte> contents);
    predicate ValidIndex(Index index, Nat length);

    byte Read(in Handle target, Index index);
    void Write(ref Handle target, Index index, byte value);
    void WithElement(ref Handle target, Index index, ...);

    lemma ReadReturnsSelectedElement(Handle target, Seq<byte> contents, Index index) ensures ...;
    lemma WriteUpdatesSelectedElementAndPreservesFrame(Handle target, Seq<byte> contents, Index index, byte value) ensures ...;
    lemma ScopedBorrowRestoresOwnership(Handle target, Seq<byte> contents, Index index) ensures ...;
    lemma OperationsTerminateUnderTheirPreconditions(Handle target, Seq<byte> contents, Index index) ensures ...;
}
```

Concrete rules bind each operation's term, entry/exit representation, arithmetic premises, effects, frame, and interference, with representable index bounds/increments. VerifiedOS discharges generic fill laws over CHERI semantics and transport rather than emulating flat memory. Handles stay opaque (pointer width, integer casts, address equality, provenance, capability tags, bounds compression, endianness, alignment require narrower interfaces).

**Proof-side only (no second machine surface):** under [R-05-023b](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-023b), explicit profile instructions map to one backend primitive surface (mnemonic/operand form taking meaning from pinned Sail) owned by [the two certifying compilers](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-18-014). Concrete laws discharge over that primitive rather than inventing a second machine surface.

Use static specialization, never virtual dispatch; erased parameters/proofs still require layout and codegen inspection. Generic modules are architecture-neutral while the first instance is CHERI-specific; do not build extra target adapters solely for coverage.

#### Required Guarantees, Not Feature Flags

Profiles identify semantic instance, representation/ABI, assumptions, and available theorems; components declare required guarantees rather than querying feature flags, keeping guarantees independent:

| Requirement | What can be shared | What the target must justify |
| --- | --- | --- |
| Bounded storage access | Contents, bounds, and frame contracts | Representation, primitive safety, arithmetic limits, and relevant execution contexts |
| Exclusive mutation | Ownership and borrow-restoration rules | Sound resource interpretation, including any unsafe or external code |
| Isolation from adversarial code | Statement of authority confinement and allowed observations | Hardware enforcement, verified software enforcement, or sufficient restrictions on linked contexts |
| Revocation or freshness | Protocol interfaces and abstract transition requirements | Actual invalidation mechanism, epoch rules, interference assumptions (CHERI alone is no blanket temporal proof) |
| Information flow and constant time | Relational specification and some compositional proof rules | Target observations, instruction behavior, compiler preservation, and applicable hardware leakage model |
| Resource bounds | Abstract accounting and bounded-loop arguments | Mapping to allocation, instruction costs, or timing under the chosen environment |

Unsupported threat-model pairings reject or require a different contract rather than silently weakening guarantees (e.g., source ownership on conventional hardware cannot resist arbitrary unsafe code; CHERI alone proves neither functional correctness, liveness, nor full revocation).

#### Refactoring Without Expanding Trust

The iteration boundary is the semantic interface, not frozen surface syntax:

```text
Editable language, inference, automation, and editor tools
    -> explicit program terms and proof obligations with source correspondence
    -> reusable Rocq component interfaces and generic theorems
    -> concrete semantic instance and proved target laws
    -> target compiler and final-artifact evidence
```

Elaborators, tactics, solvers, and AI tools can evolve freely because outputs are rechecked as Rocq terms over the existing backend, provided they preserve source-to-contract correspondence; new surface meanings still require semantics and proof work.

| Change | Reuse opportunity | Required revalidation |
| --- | --- | --- |
| Editor presentation or lemma search | Same statements, program terms, and target laws | Tool behavior; replay of new proof output, if any |
| New syntax or inference strategy with unchanged meaning | Same generic component and backend theorems | Elaboration and exact source-subject correspondence; invalidate changed source bindings |
| Refactored algorithm preserving a contract | Same client-facing contract and target primitive laws | The changed implementation's proof, termination/effects, and affected binary evidence |
| New storage representation | Same abstract algorithm contract and generic theorem | Representation and primitive laws, layout/ABI, compilation and affected artifacts |
| Changed interface law or observation model | Only results independent of the change | Dependent generic and instance proofs; no reuse based solely on unchanged names |
| Different target or emitted bytes | Applicable abstract contracts and generic lemmas | Target law instantiation and all affected final-artifact bindings and judgments |

Track dependency identities across semantic definitions, statements, representations, assumptions, source closure, and toolchain/artifact inputs: source changes invalidate bindings even when emitted bytes match, caching cannot turn stale flags into authority, and TAL gains no on-device solving, grade rules, or open-term reduction.

### A compositional core

The [core design](../language/core-design.md#judgments-and-interpretations) defines dependent values, resource contexts, and interpreted computations, with [kinded authority](../language/core-design.md#kinded-authority), [loan rules](../language/core-design.md#loans-and-control-flow), and [staging rules](../language/core-design.md#refinement-effects-and-staging); [the composition contract](../extensions/full-language-review.md) extends them to grades, handlers, tasks, and cells.

#### Layered Proof and Staging

Checking order:

1. Kernel-compatible definitional computation and normalization.
2. Flow-sensitive capture and ownership checking with sound resource interpretation.
3. Declared decidable refinement fragment with reconstructable/certificate-producing automation.
4. Domain procedures and stdlib lemmas for finite sequences (`.All`, `.Any`, `.Contains`, `.Take`, `.Skip`, `.Slice`, `.Count`, `.Update`, `.Append`), arrays, frames, and finite arithmetic.
5. Explicit Rocq lemmas and proofs for residual obligations.

The refinement tier targets bounded integer ranges, capacities, alignment, discriminants, initialization, bounded `.Model` sequence predicates/subranges (`.All`, `.Any`, `.Contains`, `.Take`, `.Skip`, `.Slice`, `.Count` with supported element bodies via pre-proved stdlib lemmas rather than open `forall`/`exists`), simple typestate, and nullity checks on nullable types. Sparse prefix/suffix range facts (`slots[0..length)` initialized, `slots[length..capacity)` vacant) stay symbolic in `capacity` without $O(\text{capacity})$ unfolding: [qualification](../language/first-release.md#qualification) checks capacity invariance with identical obligation counts and proof/certificate structure at $N = 4$ and $N = 10^9$ (modulo numeral substitution) within finite replay time/output budgets (reporting host elapsed times alongside structural checks). Arbitrary open quantified math and general nonlinear arithmetic stay outside the decidable tier (Flux/LiquidHaskell/RefinedC are comparators, not accepted solver encodings). SMT facts reconstruct under R-05-017; failures/timeouts leave open goals, and qualification reports obligation counts, discharge rate, latency, edit stability, and manual proof burden without a target percentage.

Equality ergonomics rely on canonical indices, normalization, checked bidirectional transports, and derived decidable equality with local uniqueness. Rocq 9.3.0's native `SProp` and sort polymorphism support definitionally proof-irrelevant erased witnesses inside the existing kernel without global UIP or banned rewrite rules; erasure still needs its own preservation theorem and confers no equality principle on `Prop` or `Type`. [Observational Equality Meets CIC](https://doi.org/10.1145/3719342) (Pujet, Leray, Tabareau, TOPLAS 2025), [AdapTT](https://doi.org/10.1145/3776664) (POPL 2026), and Higher Observational Type Theory (HOTT) chart the horizon for decidable observational/functorial casts; HoldFast keeps elaborator-emitted checked transports today to stay inside stock Rocq 9.3.0 without `-allow-rewrite-rules`.

Staging separates pure spec evaluation, compile-time generation, represented runtime code, and checked proofs under [metaprogramming rules](../extensions/metaprogramming.md#evaluation-and-phase-boundaries): explicit static inputs, kernel-compatible conversion, and checked cross-stage representation (static bounds specialize layouts/loops; discovered packet lengths stay runtime values). Failed generators produce nothing and confer no authority; independent intent review and negative cases remain required (shared evaluators give no independent oracle). Machine evidence retains pinned Sail or a qualified successor.

#### Compositional Leakage Obligations

`ConstantTime` is a relational contract: executions agreeing on public inputs and the entry relation produce equivalent permitted observations (including branches, addresses, and termination where modeled), preserved compositionally across combinators, callee contracts, representation, optimization, ABI, and linkage down to TAL/CIC on final bytes. Profile assumptions exclude hardware caches and speculative execution rather than importing commodity leakage models; physical side channels outside the declared model remain excluded. Jasmin is a comparator only.

#### Type Theory and Elaboration Reuse

Upstream calculi supply complementary rules without automatically composing; qualifications test selected fragments under register admission rules.

| Source | Contribution and disposition |
| --- | --- |
| Dunfield and Krishnaswami, [Bidirectional Typing](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/), 2021; Slattery and Sterling, [Bidirectional Elaborators à la Carte](https://arxiv.org/html/2607.09564v2), July 2026 | Bounded inference via declared interfaces, stable under core equality/substitution. Newer paper's mechanization, universes, holes, implicits, and typeclasses remain future work; design reference only (no extensional metalanguage axioms). |
| [Observational Equality Meets CIC](https://doi.org/10.1145/3719342), TOPLAS 2025; [AdapTT: Functoriality for Dependent Type Casts](https://doi.org/10.1145/3776664), POPL 2026 | Decidable observational equality with indexed inductives (Pujet, Leray, Tabareau) and systematic functorial casts ([arXiv:2507.13774](https://arxiv.org/abs/2507.13774)). Informs HoldFast's checked bidirectional transport generation without enabling Rocq's banned `-allow-rewrite-rules`. |
| Kovács, [Staged Compilation with Two-Level Type Theory](https://doi.org/10.1145/3547641) (ICFP 2022) and [Closure-Free Functional Programming](https://doi.org/10.1145/3674648) (ICFP 2024) | Staging-by-evaluation separating compile-time dependent meta-types from first-order closure-free runtime types (eliminating stream-fusion, monad, and iterator closures at compile time). Informs HoldFast's `const` staging and zero-closure systems lowering while keeping kernel-checked correspondence. |
| [OxCaml Mode Axes & Mode Crossing](https://doi.org/10.1145/3828681), ICFP 2026; [Data Race Freedom à la Mode](https://doi.org/10.1145/3704859), POPL 2025 | Inferred locality/uniqueness/contention axes with modal-kind mode crossing for deeply immutable types. Informs zero-boilerplate mode crossing in HoldFast's graded/resource foundation without weakening exclusive/linear resource guarantees. |
| [Higher-Order Effectful Operations](https://doi.org/10.1145/3776678), POPL 2026; [HMCFA](https://doi.org/10.1145/3828703), ICFP 2026 | Judgmental monadic laws for scoped/higher-order effects (Yang & Wu, [arXiv:2511.05739](https://arxiv.org/abs/2511.05739)) and big-step control-flow analysis for effect handlers (Whiting & Germane). Informs HoldFast's handler specialization, devirtualization, and compositional effect summaries. |
| Ahman, Ghani, Plotkin, [Fibred Effects](https://danel.ahman.ee/papers/fossacs16.pdf), 2016; [dependent CBPV](https://arxiv.org/abs/1603.04298) | Separates stable values from computations for parsers/state transitions without requiring a new authoritative CBPV semantics; richer models do not validate unrestricted mutable-state dependence. |
| [Modal Effect Types](https://arxiv.org/abs/2407.11816), OOPSLA 2025; [Rows & Capabilities as Modal Effects](https://arxiv.org/html/2507.10301v2), POPL 2026 | Reference for higher-order effect inference and row/capability translations (language effect caps ≠ CHERI authority). [METL artifact](https://github.com/thwfhk/met-oopsla25-artifact) parses/checks/interprets, lacking elaboration, effect variables, and low-level codegen. |
| [What's in the Box](https://2025.splashcon.org/details/OOPSLA/133/What-s-in-the-Box-Ergonomic-and-Expressive-Capture-Tracking-over-Generic-Data-Struct), OOPSLA 2025; [System Capybara](https://arxiv.org/abs/2607.09383), July 2026 | Scala 3 capture/reach tracking plus `consume`/freshness/read-only separation (Capless/Capybara mechanized in Lean for scope safety, no UAF/double-free, data-race freedom). Closest design for [transitive generic captures](../language/core-design.md#kinded-authority) and sharing rules; differs by deriving uniqueness from captures and using Lean proofs. |
| [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383), POPL 2024; [Affect](https://iris-project.org/pdfs/2025-popl-affect.pdf), POPL 2025 | [Handler dossier](../extensions/handlers-async.md) draws continuation-linearity rules from Affect (Iris/Rocq over Hazel, including mutable-ref continuations) and POPL 2024 (pen-and-paper + GPL-3.0-or-later Links artifact); requires concrete CHERI interpretation. |
| [Mixed Linear/Graded Logic](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2025.32), CSL 2025; [Same Coeffect, Different Base](https://arxiv.org/abs/2606.28042), ICFP 2026 | Pen-and-paper typing/grade/equation translations between graded-base and linear-base calculi (no full abstraction, artifact, or impl proof); informs simple ownership + resource-contract separation without authorizing on-device grade interpreters. |
| [Autosubst](https://github.com/rocq-community/autosubst) and [Autosubst OCaml](https://github.com/uds-psl/autosubst-ocaml) | Binding/substitution generators if needed (OCaml generator avoids funext, though [v1.1+9.0](https://rocq-prover.org/p/rocq-autosubst-ocaml/1.1%2B9.0) requires `rocq-core >= 9.0 & < 9.1`, excluding [locked snapshot](../../tools/opam/rocq.lock), and lacks modular syntax; [Autosubst2](https://github.com/uds-psl/autosubst2) imports funext). Combinator library needs no AST dependency yet. |

Existing [Equations](https://github.com/rocq-prover/equations) and [Rocq-Elpi](https://github.com/LPCIC/coq-elpi) qualifications govern indexed definitions and elaboration ([Equations tutorial](https://rocq-prover.github.io/platform-docs/equations/tutorial_indexed.html) distinguishes constructive decidable-index UIP from computation-blocking axioms; [Q19b](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-tooling-qualification.md#q19b-dependent-computation-equations-and-equality-principles) verified computation/replay without global UIP and kept handwritten `match` for small clients). Elpi suits narrow HOAS elaboration; MetaRocq keeps quotation/metatheory. None replaces source correspondence, linear resource proofs, or direct licence checks.

Rocq's experimental [`-allow-rewrite-rules`](https://rocq-prover.org/doc/V9.3.0/refman/addendum/rewrite-rules.html) (`Symbol` conversion rules with unchecked confluence/termination and superficial type-preservation warnings) is banned: [kernel recheck](https://github.com/symbiogenesis/VerifiedOS/blob/main/tools/vos/proofaudit.py) requires `Rewrite rules are not allowed`, keeping unresolved grade equalities as explicit proof obligations.

#### Composition acceptance cases

Exercise a positive client that combines the selected mechanisms and
well-formed negative neighbors that reach the intended judgment. The
[workflow cases](workflow-contract.md#selected-composition-and-rejection-cases)
use the callback-shaped borrowing interface. The
[synchronous fixture](../language/core-design.md#composed-qualification-fixture)
exercises flow-sensitive loans and returned views. The
[extension fixture](../extensions/full-language-review.md#composed-client-and-inhabited-entry)
combines graded capture, continuation handling, cancellation and cells.

### Surface examples <a id="an-ideal-surface"></a>

The [language reference](../language/reference.md) describes current syntax and
support. The [authored dependent example](../../examples/dependent.hf) combines
invariants, output loans and proof mode.
The [packet validator](../../examples/first_slice.hf) shows the bounded
systems subset with a concrete destination loan. The snippets below illustrate
designs whose support is governed by the linked contracts.

#### Surface conventions

Type inference, binding mutability and compile-time availability are independent.

| Declaration | Type | Binding | Availability |
| --- | --- | --- | --- |
| `let count = ReadCount();` | Inferred | Immutable | Runtime |
| `var count = ReadCount();` | Inferred | Mutable | Runtime |
| `let usize count = ReadCount();` | Explicit | Immutable | Runtime |
| `var usize count = ReadCount();` | Explicit | Mutable | Runtime |
| `const Nat Limit = 16;` | Explicit | Immutable | Required static |

An immutable binding can hold a loan that authorizes writes to the borrowed
storage. Reassigning a binding requires `var`. Taking a loan or writing
through it requires the corresponding place and authority. See the
[binding reference](../language/reference.md#bindings) and
[loan reference](../language/reference.md#loans-and-parameter-modes).

#### Permanent language exclusions

The [surface grammar](../language/surface-grammar.md#explicit-values-loans-and-absence)
defines explicit conversions, bindings, loans and absence. These constraints
hold across assurance profiles and future extensions.

- No implicit coercions, optional lifting, dereferencing or ownership transfer.
  Context may infer a literal's type, a generic argument or a proof.
- No parse decisions based on name resolution, inferred types or import order.
- No implicit mutation or unrestricted shared mutation. A write requires a
  suitable exclusive loan or a [qualified cell operation](../extensions/interior-mutability.md).
- No implicit nullability or unchecked optional extraction. Use tagged values
  and account for absence on every reachable exit.
- No unchecked authority fabrication. Pointer operations require checked access,
  provenance, bounds, lifetime, initialization, alignment and arithmetic.
- No hidden heap allocation, stack unwinding, garbage collection, or implicit
  scheduler on the bounded runtime path. See the
  [release boundary](../language/first-release.md#release-boundary).

#### Contracts, loops and proof mode

See the [contract reference](../language/reference.md#contracts),
[control-flow rules](../language/reference.md#statements-and-control-flow), and
[proof syntax](../language/reference.md#proof-mode). The
[ownership libraries](../language/first-release.md#ownership-libraries) define
sequence models and bounded iteration.

#### Dependent Results and Place-Named Loans

A parser returns a runtime-discovered length paired with erased evidence, borrowed from its input:

```text
public record PacketView<region 'source>(
    usize Consumed,                          // represented: the bytes the header occupied
    in<'source> Span<byte> Payload,          // a subslice of the source, never outliving it
    ghost PacketFormat.Header Header)        // erased
    invariant PacketFormat.Encodes(Header, Payload.Model);

public Result<PacketView<'input>, ParseError> ParsePrefix(in Span<byte> input)
    effects reads(input)
    ensures result.Model == PacketFormat.ParsePrefix(input.Model);
```

`PacketFormat.ParsePrefix` comes from the reviewed format descriptor (distinct from an exact-input `ParseExact`). `'input` names the parameter's loan so `PacketView` borrows from `input` without an extra region/index parameter (`PacketView` itself declares `'source`), keeping `input` immutable while live; `Span<byte>` carries its own length, errors carry no view, and the runtime tag selects the branch. Candidate surface over [R-05-043](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-043).

The caller's loan ends at the view's last use, branch by branch:

```text
match (ParsePrefix(in frame))
{
    Ok(packet) => {
        Forward(in packet.Payload);          // frame stays shared-borrowed until this last use
    },
    Err(error) => {
        frame.Clear();                       // no view exists on this branch, so frame is writable
        Report(error);
    },
}
```

#### Flow-Sensitive Loans and Restoration Contracts

Restoration is inferred from control flow, and the author writes neither a callback nor a `restore` call. An element loan ends at its last use, and elaboration rebuilds the container from the value the element then holds:

```text
public void SetFirst<ghost Nat count>(ref Span<byte, count> target, byte value)
    requires target.Length > 0
    effects writes(target)
    ensures target.Model == old(target.Model).Update(0, value)
{
    let ref byte first = ref target[0usize];
    first = value;
}
```

A conditional return can transfer a loan on success and restore the owner's
write permission on error. A returned exclusive loan also needs to specify what
the lender receives when the loan ends. In this design, `restores` states that
predicate and `final(slot)` denotes the value the caller leaves in the slot.
[Comparable Rust proof constructs](#what-the-rust-verifiers-contribute)

```text
public Result<ref<'table> Value, TableFull> FindOrInsert<ghost Nat capacity>(
    ref Table<Key, Value, capacity> table, Key key)
    effects writes(table)
    ensures result is Ok(slot) ==> slot == old(table.Model).GetOr(key, Value.Default)
    restores result is Ok(slot) ==> table.Model == old(table.Model).Set(key, final(slot))
    ensures result is Err(_) ==> table.Model == old(table.Model) && table.Model.Count == capacity
{
    if (table.Find(key) is Some(slot))
        return Ok(slot);                           // the loan leaves with the result on this branch only
    return table.TryInsert(key, Value.Default);    // no loan is live here, so the table is writable
}
```

One `restores` clause covers both success paths because `Set` handles both
replacement and insertion. The [synchronous design](../language/core-design.md#loans-and-control-flow)
covers branch-sensitive returns of shared loans. The
[borrowing comparison](../language/loan-analysis.md#conditional-borrowing-comparison)
records which shared return and loop-carried reborrow cases have executable evidence.

A signature can also lend part of a record. `Log` names two views: its initialized entries, and a tail granting a write to the next slot and permission only to increase the length. Appending then needs only the tail, so loans on existing entries survive it. That is the case [Goose's append](#research-that-changes-the-experiments) types as a write at the current length:

```text
public struct Log<T, ghost Nat capacity>
{
    private usize length;
    private Slots<T, capacity> slots;

    public view Entries = slots[0..length];            // lowering length also needs this view
    public view Tail = slots[length], length grows;    // the next slot, and raising length only

    public void Push(ref this.Tail, T item)
        requires this.Length < capacity
        ensures this.Model == old(this.Model).Append(item);
}

public void AddEntry<ghost Nat capacity>(ref Log<Entry, capacity> log, Entry entry)
    requires 0 < log.Length && log.Length < capacity
{
    let first = in log[0usize];      // a shared loan through Entries
    log.Push(entry);                 // needs only Tail, which is disjoint from every Entries loan
    Audit(in first);                 // still live, and its entry unchanged
}
```

Every length-lowering op needs `Entries`, keeping live entry-loan extents below `length` for disjointness (unlike a consume-and-return `Push`, which would end all log loans).

In the bounded library proposal, `SetFirst` lowers to `Build.with_element` (`WithElement(ref target, 0, (scoped ref byte selected) => { selected = value; })`), scoping a fresh loan inside the callback, suspending the parent, and barring loan escape in the result or longer-lived captures. Total callback contracts prove single invocation, termination, and restoration (a once-callable type alone does not); the pilot callback allows returning `Result` (restoring parent before propagation) without non-local return or suspension. The target loan model handles branch-returned loans, loops, and `Result` propagation explicitly without claiming them from callback theorems, and source frontends must prove elaboration rather than merely printing combinator calls. Measure rewrite cost at the same resource boundary in [the conditional borrowing comparison](../language/loan-analysis.md#conditional-borrowing-comparison).

#### Typestate and Protocol Resources

An initialization operation returns a different state rather than letting a caller assert that uninitialized memory is readable:

```text
public Buffer<byte, count, Initialized> Initialize<ghost Nat count>(
    owned Buffer<byte, count, Uninitialized> storage, byte value)
    effects writes(storage)
    ensures result.Model.All(x => x == value);
```

Inside a caller:

```text
let zeroed = Initialize(move storage, 0);   // storage is consumed; only the initialized buffer is readable
```

The runtime length and storage handle remain real data, and for VerifiedOS the handle includes the applicable CHERI capability; the state index and initialization proof are erased. The generic invariant relates initialized storage to readable values, and the instance proves the concrete layout, alignment and applicable capability-tag rules. Initializing byte storage is intentionally narrower than initializing arbitrary capability-bearing records.

When a bounded container maintains multiple coupled field invariants across a multi-step update or bulk relocation, declaration `invariant` clauses can carry explicit clause names and an `open (...) lifts ...` block can selectively lift only the conjuncts that the block temporarily invalidates:

```text
public struct BoundedBuffer<T, ghost Nat capacity>
    invariant LengthBound: Nat(length) <= capacity
    invariant InitializedPrefix: slots.Slice(0, Nat(length)).IsInitialized
    invariant VacantSuffix: slots.Slice(Nat(length), capacity).IsVacant
{
    private usize length;
    private Slots<T, capacity> slots;

    public void RelocatePrefixInto(ref BoundedBuffer<T, capacity> destination)
        requires destination.length == 0usize
        effects writes(this, destination)
        ensures this.length == 0usize
        ensures destination.Model == old(this.Model)
    {
        open (ref this, ref destination) lifts InitializedPrefix, VacantSuffix
        {
            let usize count = this.length;
            CopyRepresentation(in this.slots, ref destination.slots, count);
            TransferType<T>(ref this.slots, ref destination.slots, count);
            destination.length = count;
            this.length = 0usize;
        }
    }
}
```

`open (ref this, ref destination) lifts InitializedPrefix, VacantSuffix` records a linear [`CloseDebt`](../extensions/interior-mutability.md#representation-authority-and-open-invariants) for those two conjuncts while keeping `LengthBound` active until `length` writes (immediately re-discharged via `count <= capacity`). While lifted, early exits (`return`, `break`, `continue`, `?`), `await`, handler capture, and whole-receiver calls are refused; closing re-proves only lifted conjuncts. Inside, `CopyRepresentation` performs a tag-preserving copy of `[0..count)` into logically `Vacant<T>` destination slots (recording revision-bound representation equality without destructors or duplicated ownership), and erased `TransferType<T>` consumes that equality plus initialized source and vacant destination to flip source `[0..count)` to vacant and destination `[0..count)` to live initialized `T` in one $O(1)$ range step.

This generic method requires an element relocation law for `T` (destination invariant preservation and absence/discharge of old-address observers); opaque elements without it and pinned elements with live address observers are refused. See [the ownership library contract](../language/first-release.md#ownership-libraries).

A protocol exposes a different kind of erased evidence, with an explicit result case for each resource state:

```text
public union PublishResult<ghost Identity id>
{
    Success(tracked PublishPermit<id, Published> permit);
    Retry(PublishError error, tracked PublishPermit<id, Populated> permit);
}

public PublishResult<id> TryPublish<ghost Identity id>(
    ref PublicationSlot<id> slot,
    tracked PublishPermit<id, Populated> permit)
    effects writes(slot)
    ensures PublicationProtocol.Step(old(slot.Model), slot.Model, result.Model);
```

`PublicationSlot` is runtime storage and `PublishPermit` is a module-protected protocol token tied to its identity; `TryPublish(ref slot, move permit)` returns a tag-selected case carrying erased state evidence (`Retry` restores `Populated`; partial publication would require a distinct recovery case). Both cases return a linear token (unlike affine discard), and pure `let ghost Seq<byte> before = target.Model` snapshots copy freely when justified without duplicating permission. Sequential example only (no concurrency, eventual publication, crash recovery, or device ordering); split/restore stays inside [the resource-law explanation](../language/first-release.md#ownership-libraries).

#### Captures and Graded Use

A library supplies a grade domain as a sealed record of carrier, operations, admission order, laws and interpretation, which [the graded foundation](../extensions/graded-foundation.md#dimensions-and-lawful-domains) specifies. Its first exact domain reads:

```text
public domain NatExact
{
    carrier Nat;
    zero 0; one 1; add (+); mul (*);
    admits (==);                // demand must equal the allowance: two uses never fit one
    interpret Use.Exact;        // grade q means exactly q uses in the graded value semantics
    laws NatExactLaws;          // semiring, congruence, monotonicity and interpretation proofs
}

public void MapInto<ghost Nat count, captures C>(
    in Span<byte, count> input,
    ref Span<byte, count> output,
    in Fn(byte) -> byte captures C transform @ NatExact(count))
    requires Disjoint(output, C)
    effects reads(input, C), writes(output)
    ensures output.Model == input.Model.Map(transform.Model)
    ensures CallCount(trace, transform) == count;
```

`Fn(byte) -> byte captures C` is a total shared-call function with transitive capture set `C` (as in [Scala 3's capture checker](#type-theory-and-elaboration-reuse)); `Disjoint(output, C)` excludes `output`-overlapping captures, `Fn` rejects consuming/mutable captures, `C` specializes without boxing/dynamic dispatch, and `in` keeps captures alive.

`@ NatExact(count)` enforces exact typing-level demand equality (`NatBound` relaxes to `<=`; idempotent presence `1 + 1 = 1` ignores cardinality). Use grades are not trace laws, termination, or call order—`CallCount` separately bounds erased source-trace invocations (neither counts inlined machine calls), and contents postconditions prove elementwise semantics.

`ghost Nat count` has zero computation use and inferred type use (avoiding [Gerty's](#reading-the-graded-type-claims) `(.0, .2)` syntax); `grade q : NatExact` specializes alongside representation (unspecialized representations need separate proofs). Use counts, capability permissions, and security labels (`effects calls(endpoint)`, `requires Public(index)`) stay distinct, with information flow tracking control and data dependence.

#### Handlers With Accountable Continuations

An effect declares each operation's reply and how many times a handler may resume it. A handler that resumes twice must be able to duplicate everything the continuation retains:

```text
public effect Choose
{
    bool Choose() resumes(0..2);
}

public usize BestScore<captures C, ghost SearchBudget budget>(
    in Fn() -> usize captures C effects(Choose) body)
    requires Duplicable(C)       // a second resumption copies everything the continuation retains
    requires Search.ExpansionFits(body.Model, budget)
    effects reads(C)
    ensures Search.Work(trace) <= budget.Work
    ensures Search.PeakFrames(trace) <= budget.Frames
{
    return handle (body())
    {
        Choose() with k => Max(resume k(false), resume k(true)),   // deep: each resumption reinstalls this handler
        return score => score,                                     // runs once per completed resumption
    };
}
```

Inside a caller:

```text
let header = packet.Header;                              // a value copy, so duplicable
let Fn() -> usize effects(Choose) score = () => Score(header, Choose());
let best = BestScore(in score);
```

`SearchBudget` and `Search` are illustrative library contracts, using ordinary
ghost parameters, `requires` and `ensures`. Their
[compositional summary](../extensions/handlers-async.md#compositional-handler-summaries) bounds
this handler's complete exploration, including nested choices and callback work.
The caller supplies `budget` at specialization or inference obtains it from the
checked summary; an unresolved limit remains a goal. Work is measured in named
source steps and frames in simultaneous live source frames. Their transport to
target costs, reserved storage and available pool capacity remains separate.

The local callable annotation binds `Choose` as a per-call effect capability;
the local capture set is inferred and retains `header` alone. Naming the callback
therefore preserves the effect parameter that `BestScore`'s handler supplies,
rather than capturing an ambient handler capability, and provides a place for the
explicit `in` argument.

A callback using `Score(ref packet, Choose())` is refused by the shared-call or
capture-duplication rules: its exclusive access may require `FnMut` before
`Duplicable(C)` is considered. If an exclusive loan reaches the
[foundation's `Dup` obligation](../extensions/graded-foundation.md#resource-and-computation-interface),
a second resumption cannot duplicate it; no grade repairs that. Every captured
continuation is resumed, disposed or moved into the handler's result, and none is
dropped. `dispose` runs the continuation's declared cleanup:

```text
public effect Reject
{
    never Reject(ParseError error);          // no reply exists, so a handler can only dispose
}
```

Inside a caller:

```text
let checked = handle (Validate(ref packet))
{
    Reject(error) with k => { dispose k; return Err(error); },   // ends k's loans, erases, examines verdicts
    return _ => Ok(()),
};
```

`dispose` ends captured loans (e.g., on `packet`), erases must-erase contents, and eliminates mandatory verdicts (unlike affine drop). `Choose()` in `BestScore`'s closure uses its `effects(Choose)` parameter capability bound by `BestScore`'s handler, while caller-captured capabilities bypass `BestScore` unexecuted. `handle shallow` does not reinstall itself and resumes `k` only inside a same-signature `rehandle` (whose return clause receives the raw result). Nesting, forwarding, and resumptions bound at specialization; capture requires reserved capacity or a `CapacityExhausted` branch; handlers lower to bounded control flow without unwinding under [handler rules](../extensions/handlers-async.md#handler-lookup-capture-and-return).

#### Structured Tasks, Cancellation and Cells

Optional multi-shot/async research example outside the first release (preceded by the concrete service trial), illustrating [the composition review's client](../extensions/full-language-review.md#composed-client-and-inhabited-entry): runtime-length packet, multi-shot handler over a duplicable header copy, and cancellable atomic-counter commit under a unique allowance.

```text
public union Delivery<ghost Nat n>
{
    Accepted(owned Packet<n> packet, Added<n> receipt);
    Cancelled(owned Packet<n> packet);
}

public async Delivery<n> Accept<ghost Nat n>(
    owned Packet<n> packet,
    in CountCell counter,
    tracked AddOnce<counter, n> allowance)
    effects reads(packet), calls(Forward, counter.Add, counter.Retire)
{
    let header = packet.Header;
    let Fn() -> usize effects(Choose) score = () => Score(header, Choose());
    let best = BestScore(in score);
    await Forward(in packet, best);                                    // a checkpoint even when already complete
    let receipt = commit counter.Add(move allowance, packet.Length);   // last checkpoint, then one AMOADD
    return Accepted(move packet, receipt);                             // a later request is answered too_late
}
on cancel                                                              // a request accepted before the commit
{
    counter.Retire(move allowance);                                    // no addition; the allowance retires once
    return Cancelled(move packet);
}

public async Result<TaskOutcome<Delivery<n>>, Busy<n>> Serve<ghost Nat n>(
    ref Frames frames, owned Packet<n> packet,
    in CountCell counter, tracked AddOnce<counter, n> allowance)
{
    scope (ref frames)                                                 // no child outlives this block
    {
        let dormant = Accept(move packet, in counter, move allowance);   // constructed, not yet run
        match (spawn dormant)                                          // binds a declared frame and completion record
        {
            Spawned(task) =>
                return Ok(await task);                                 // transfer the complete terminal outcome after joining
            Full(unstarted, verdict) =>
                return Err(Busy(verdict, move unstarted));             // exhaustion returns every input
        }
    }                                                                  // an early exit cancels, then joins, every child
}
```

`Delivery<n>` declares an empty failure set, and `Forward` returns `Unit` under its cancellation/resource contract. `Serve` keeps `TaskOutcome` intact (`Completed(Accepted(...))` or `Cancelled(...)` from `Accept`'s cleanup), transferring mandatory outcome inspection inside `Ok(...)` to `Serve`'s caller before any returned packet is used.

Calling an `async` function constructs a dormant computation without executing effects; direct `await` runs it sequentially inside the current task without child registration (retaining nested storage, cancellation, and commit obligations). `spawn` binds a preassigned frame from `frames` or returns `Full(unstarted, verdict)` unchanged; spawning after scope cancellation latches marks the child so its first activation records `cancelled` without body execution, and `on cancel` cannot spawn. Every `await` (even ready) checkpoints cancellation: precommit cancellation runs nested helper cleanup then cancels/joins registered children before enclosing cleanup (accounting each resource once), whereas `commit` checkpoints once then executes a bounded no-capture/no-suspend region whose single aligned AMOADD linearizes the commit (later cancellations answer `too_late`). Client wait timeouts stop only the wait; scoped timeouts cancel and join within the declared bound. Lowering emits a bounded reaction graph with syntactic poll sites and no inner scheduler under [async rules](../extensions/handlers-async.md#frames-child-ownership-and-reaction-execution) and [R-12-097](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-12-097).

`Packet<n>` binds represented length to ghost `n` so `AddOnce` (unique protocol token naming counter generation and request, never a grade) agrees with `packet.Length` and conserved outstanding allowances prevent overflow. Only `BestScore`'s multi-shot continuation captures `header` (`packet` and `allowance` stay outside, since capturing `allowance` fails `Duplicable`, and releasing `frames` on `Cancelled` before join fails terminal ownership).

Cells expose only their proved operations:

```text
stats.Update((ref Stats s) => { s.Accepted += 1; });       // local: the view cannot escape, suspend or reenter

if (settings.TryWrite((ref Settings s) => { s.Retries = 3; }) is Err(BorrowConflict))
    Defer();                                                // a live reader is an examined result, not a panic

let seen = counter.Load();                                  // a historical sample, never a current fact
```

An `await` inside `Update` is refused because the invariant would stay open across suspension, and so is a getter that reenters `stats`. A test such as `counter.Load() + n <= U64.Max` cannot replace an allowance, since another child may add between the load and the addition. The shared counter holds only a scalar, never a capability, closure or frame, and the profile admits no compare-and-swap. [The mutability rules](../extensions/interior-mutability.md) own these interfaces.

#### Feature decisions

The [release contract](../language/first-release.md) owns primitive behavior,
packages and the ownership libraries. The [core rules](../language/core-design.md)
define dependency, effects, authority and exit states.
[Assurance profiles](../extensions/assurance-profiles.md) select evidence
obligations over the same operational semantics. The
[extension index](../extensions/README.md) links designs beyond the bounded
synchronous subset.

#### Performance is an artifact claim

Measure code size, stack, memory traffic and execution on the exact final image
with the same target, ABI, inputs and assurance as the baseline. Report proof
construction and replay costs separately. The
[artifact protocol](workflow-contract.md#target-and-production-artifact-protocol)
distinguishes host time, target model cycles and hardware measurements.

## Compiler and evidence obligations

### From the library to bytes

Instantiate the generic component theorem with checked CHERI operation and
representation laws. The [compiler pipeline](#proposed-architecture) requires
evidence connecting that interpretation to the authored source and the final image.

The final functional theorem relates every permitted execution of the exact
image to the reviewed source contract under declared platform assumptions,
valid entry states and the input/output representation relation. Prove
termination or reactive progress where required. The
[artifact endpoint](compiler-route-contract.md#equivalent-artifact-endpoint)
also requires contextual preservation and applicable binary security,
resource and admission results.

#### Retained compiler route

Clight is the decoder-synthesis waypoint under
[R-05-043](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-043).
CHERI-CompCert supplies the compiler route, with capability representation,
provenance, ABI and lowering duties. Machine proofs use the same pinned Sail
definitions as hardware refinement. Explicit profile instructions use the
primitive surface governed by
[R-05-023b](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-023b).
[Compiler route decision](#compiler-route-decision)

#### Compiler amendment obligations

The [compiler route contract](compiler-route-contract.md#conditional-amendment-and-reviewer-requirements)
owns the obligation-by-obligation evidence required before replacing a
representation waypoint, compiler, validation path or semantic anchor.

#### Licensing and Commercial Rebuildability

**An independent direct backend can eliminate the non-commercial CompCert/SECOMP dependency**—affecting commercial builds, compiler redistribution, and independent rebuilding, not just emitted OS images. [The upstream licence reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#compcert-and-secomp) separates the non-commercial compiler grant from its LGPL subset and negotiated commercial rights (shipped compiler binaries require dependency distribution rights). This requires independently authored or suitably licensed compiler/proof sources: changing IR does not relicense copied CompCert/SECOMP/Chamois passes; Clight itself has an LGPL option (so bypassing Clight is neither necessary nor sufficient); and [Rocq's LGPL licence](https://github.com/rocq-prover/rocq/blob/V9.1.1/LICENSE) permits commercial use while keeping redistribution duties.

**Whole-toolchain removal is separate:** it also requires dispositions for [retained compiler duties](#compiler-amendment-obligations), [Velus's non-commercial grant](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#vélus), and [CertiRocq's CompCert dependency](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md) (whose dual-licensed modules still pull the full compiler package).

#### Mechanically Produced Evidence

A qualified frontend produces:

```text
SourcePackage(sourceClosure) = {
    coreProgram;
    elaboration : Elaborates(sourceClosure, coreProgram);
    typing : WellTyped(coreProgram);
    sourceMap : SourceLocations(sourceClosure, coreProgram)
}
```

`Elaborates` covers checked parsing/validation, resolution, implicit insertion, overload/instance selection, and desugaring, bound to exact source, generated inputs, and dependency/config identities (`sourceMap` aids navigation without proving correspondence; MetaRocq checks terms without proving external frontends; typed holes remain outside accepted packages; source/resolution/desugaring edits must invalidate correspondence even if stale core checks).

Linking is a typed proof boundary: generated required/provided contracts specify ABI, preserved registers, stack shape, memory/capability authority, relocations, callbacks/reentrancy, effects, and observations, discharged via existing TAL rules and CIC proofs (no new TAL grade axes, on-device solvers, or unchecked linker assumptions) across verified-C, Rust, and HoldFast modules. Precedent: CompCertO's open-module refinement ([CompCertOC](https://pldi25.sigplan.org/details/pldi-2025-papers/27), PLDI 2025, threading Kripke memory relations across 18 CompCert passes for stack-sharing cooperative threads) supplies no inherited CHERI theorem or implied adoption; HoldFast linkage/preservation work is priced in [shared retained-route allowances](../../PLAN.md#shared-foundation-and-retained-route).

Optimization, typed linkage, and image validation extend `SourcePackage` to the [artifact endpoint](compiler-route-contract.md#equivalent-artifact-endpoint) over the same pinned Sail term (retained and direct capability-IR routes alike). A promoted artifact package binds source, independent contract, elaborated term/correspondence, representation/ABI, functional/resource/observation proofs, solver certificates and exact transitive assumptions, optimization evidence, link contracts/composition, build/layout/byte identities, semantic pin/guarantee theorems, and exact-byte measurements—organizing existing evidence rather than adding a new admission format (semantic dependency edits reopen obligations even if displayed goal IDs match).

## Proof libraries and tool qualification

### Bounded component foundation

A generic buffer proof depends on checked operations, representations,
frame/restoration laws and the matching machine interpretation. Prove the generic
algorithm against that interface and instantiate each law for the actual
target. The [synchronous design](../language/core-design.md) defines the
composition fixture. The [ownership libraries](../language/first-release.md#ownership-libraries)
own the public interfaces, and the
[delivery plan](../../PLAN.md#holdfast-first-release-delivery) names their producers.
Apply the [workflow trial](workflow-contract.md#clients-and-baseline-evidence)
only with executable baselines and checked prerequisites.

#### Existing tooling and implementation owners

The locked batch Rocq workflow is the proof gate. Its external
[qualification record](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-tooling-qualification.md)
covers candidate diagnostics, rendering, libraries and tactics. Candidate proof
tools need independent replay, freshness controls and a demonstrated client
benefit at the same assumption boundary. Check exact dependency terms before
adoption. [Third-party terms](../../THIRD-PARTY.md)

| Use | Current tool or candidate |
| --- | --- |
| Grammar generation and comparison | [Menhir and the checked parser](../tooling/parser.md) |
| Development-test generation and shrinking | Isolated [Hypothesis runner](../tooling/tooling-protocols.md#generated-development-tests). QCheck requires a named OCaml consumer. |
| Proof interaction | Rocq LSP and Pytanque are candidates for provisional goal feedback. The batch gate checks accepted proofs. |
| Domain proof automation | The selected interpretation owns primitive laws. Consider Iris/MoSeL, Diaframe, Actris, or reflective/certificate SMT tools ([SMTCoq](https://github.com/smtcoq/smtcoq), [Sniper](https://github.com/smtcoq/sniper)/Trakt) only where the component's obligations fit their rules, locked Rocq assumptions, and concrete machine subjects. |
| Representation transfer | [CoqEAL](https://github.com/rocq-community/coqeal) and [Trocq](https://github.com/rocq-community/trocq) ([TOPLAS 2025](https://doi.org/10.1145/3737283) axiom-free parametricity transfer) are candidates after the package trial establishes a native Rocq transport baseline. Qualify the selected revision and assumption closure. [Comparison protocol](workflow-contract.md#representation-transfer-comparison) |
| Proof-guided construction | [Lowering precedents](#closest-matches-to-the-complete-workflow) inform representation and construction algorithms. Reuse requires compatibility with the selected logic and target. |
| Mechanized capability laws | [Capability and memory-model precedents](#capability-aware-and-parametric-verification) inform concrete instances. Check their theorem subjects against the pinned CHERI model. |

### Qualification and effort

[PLAN.md](../../PLAN.md#planning-basis-and-scope) owns estimate ranges and
implementation scope. The [workflow contract](workflow-contract.md) owns
baseline independence, weakening probes and measurement. The [route contract](compiler-route-contract.md)
owns artifact comparison, assumption checks and emission-family closure.

#### Where time might be saved

Reuse checked functional, representation and frame laws across clients that
share their premises. Validate the actual theorem, assumptions, license and
toolchain before pricing reuse. Charge adapters, review and maintenance to
the work that needs them. A port to another target can reuse abstract
specifications and algorithms while supplying new representation and
target-security proofs.

The [package trial](workflow-contract.md#representation-transfer-comparison)
measures proof transport under a representation change. The
[compiler inspection API](../tooling/tooling-protocols.md#compiler-inspection-api)
shares checked facts across tooling consumers. Compare setup, shared
maintenance and per-client work at the same evidence endpoint.
[Accounting thresholds](workflow-contract.md#accounting-and-decision-thresholds)

#### Security Gains and Their Limits

Types and annotations improve error locality without automatically strengthening platform guarantees; added guarantees require stronger named contracts, implementation proofs, and binary transport. Target abstraction rejects missing semantic laws and unsupported security requirements without adding hardware isolation—every claim remains conditional on proved interpretation and environment assumptions.

| Checked library property | Defects excluded within semantics | Outside that result |
| --- | --- | --- |
| Initialization and bounds refinement | Uninitialized reads, out-of-range accesses, wrong initialized outputs | Secret scrubbing, stale DMA, properties lost before final artifact |
| Ownership plus borrow restoration | Conflicting mutation, post-loan use, unintended framed-storage writes | Hardware revocation, unproved unsafe/FFI, general concurrent interference |
| Functional codec contract | Wrong interpretation, omitted descriptor checks, inconsistent consumed length | Wrong descriptor, unspecified rejection policy, DoS without termination/resource proofs |
| Indexed protocol refinement | Illegal modeled transitions, duplicated exclusive rights, lost failure ownership | Global liveness, crash recovery, cancellation, freshness unless modeled |
| Semantically interpreted usage budget | Excess modeled calls/events or wrong exact-use accounting | WCET, allocation volume, energy, call order without separate models |
| Information-flow proof with observations | Prohibited modeled explicit/implicit flows | Final-binary timing/leakage, physical side channels, unmodeled declassification |
| Subject binding and assumption auditing | Stale evidence and unaccepted assumptions when enforced by checker | Spec adequacy, mismatched source interpretation, compiler/hardware correctness by metadata |

For example, an ownership theorem prevents double-publishing a single-use token through the verified API, whereas eventual publication also needs termination/progress and failure semantics; grades renaming existing permissions add no strength; shared libraries concentrate risk (requiring independent contract review, negative tests, and satisfiable-entry/non-vacuity audits); and deployment always enforces the stronger VerifiedOS profile.
