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

A public interface distinguishes safety throughout execution, partial
correctness on return, termination of one call and progress of an ongoing
service. A function that might wait forever can still preserve its caller's
memory permissions. Two tasks can hold their own locks safely while each
waits for the other. The [bounded release](../language/first-release.md#release-boundary)
keeps its loop and termination obligations. A proposed runtime that admits
divergence must keep potentially divergent calls out of logical conversion
and account for resources held while they wait.

For a reactive service, state which requests can enter, what counts as a
terminal outcome and which scheduler, peer, device or clock assumptions
ensure it occurs. A deadline additionally needs a time bound in the declared
clock and a bound on each dependency. Name the owner of each premise. An
implementation that withholds admission for every healthy request must fail
an interface that promises admission under available capacity. For a selected
service, qualify one such request through its terminal outcome and an execution
in which its peer stops responding. Check the promised timeout or recovery
if the declared premises still hold. If a required premise fails, withdraw
that progress claim and check the independent safety and ownership claims
that still apply. [Structured async bounds and progress](../extensions/handlers-async.md#bounds-and-progress-premises)

A remote operation can commit and lose its acknowledgement before the caller
retries. An interface promising one durable effect per logical request must
state how request identity survives a restart, how durable state recognizes
or absorbs duplicates, and how long that protection covers retries. Exercise
that failure interval and redeliver the same request after recovery. An
interface that cannot resolve the outcome exposes that uncertainty to its
caller. This obligation applies when a service crosses such a boundary.

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
| [RefinedRust](https://plv.mpi-sws.org/refinedrust/) | Refined ownership types for safe/unsafe Rust in Iris with Rocq-checked proofs; suited to verified code behind safe APIs. | Soundness covers the embedded Rust model; Rust translation and compilation remain separate boundaries. Best Rust proof match for the Radium anchor, not all Rust/rustc. Page covers PLDI 2024 only; traits/closures/iterators are a separate OOPSLA 2026 paper with a largely different author list. |
| [Corten](https://arxiv.org/abs/2609.04372) | Deep embedding of Rust THIR in Rocq with WP calculus and itree denotation via hax plus authors' extension; proves buddy-allocator alloc/dealloc safety. | September 2026 preprint (unfilled template venue) naming no repository, artifact deposit, or code URL—nothing to pin, inspect, licence, or reproduce. Unverified transpiler against rustc, untrusted borrow-checker oracle, single-threaded memory model. Unrelated to Verus-verified Asterinas CortenMM (Zhang et al., SOSP 2025). |
| [Aeneas](https://github.com/AeneasVerif/aeneas) | Charon MIR/LLBC translation to functional code for functional reasoning on Rust. | Qualify exact Rocq translation and Rust subset before reuse; [2024 symbolic borrow-checking](https://arxiv.org/abs/2404.02680) is not a verified rustc backend. Largest reported use—[SymCrypt Rust crypto](https://arxiv.org/abs/2609.15648) (Sept 2026 preprint: 16.7 KLOC Rust via 237 KLOC largely agent-written Lean, Charon/Aeneas still trusted)—is Lean-only; pilot Rocq subset first. |
| [hax](https://hax.cryspen.com/) and [hacspec lineage](https://hax.cryspen.com/publications/) | Rust-to-prover translation and spec-oriented Rust (notably crypto); 2025 hax paper shows multi-prover workflows. | Homepage lists Lean, F*, Rocq; tutorials emphasize Lean and F*. A listed backend does not imply feature parity or machine-code proof. Useful for executable specs; check Rocq per example. |
| [Creusot](https://github.com/creusot-rs/creusot) | Rust contracts and logical models for mutation; translates to Coma in Why3. | Why3/solver route gives no foundational Rocq lowering/compilation proof; interactive prover alone does not validate frontend. Donor for model views and post-borrow specs. Copyleft LGPL-2.1 licence (unlike permissive neighbors); read before reuse. |
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
| [Pyrosome](https://github.com/DIJamner/pyrosome), [2026 thesis](https://www.csail.mit.edu/event/framework-modular-metatheory-and-verified-compilation) | Modular Rocq metatheory and composable verified translation (System F + refs, imperative, linear calculi). | Research reference for extension/linking/pass composition; examples give no production systems compiler or source correspondence. |
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
| Versioned E-Graphs (Cesario et al., PLDI 2026 Distinguished Artifact) | [VersionedEGraph](../../tools/toolchain/proof_certificates.py) and [proof elaboration](../../tools/toolchain/elaborate_proofs.py) share branch equivalences via trail-backed `push_version`/`pop_version` scopes and emit shortest-path `Refl`/`Symm`/`Trans`/`Congr` terms. | Untrusted producer checked by Rocq 9.3.0 (`Print Assumptions`, `rocqchk`); ill-typed dependent `Congr` args fall back cleanly. |
| Certificate-producing arithmetic & skeletons (FLEX July 2026; CPC CAV 2026; Ethos & Proof Skeletons IJCAR 2026) | [NatDifferenceProver](../../tools/toolchain/proof_certificates.py), [FixedIntOrderProver](../../tools/toolchain/proof_certificates.py), and [prelude lemmas](../../tools/toolchain/elaborate_types.py) reconstruct `nat` difference-logic chains, fixed-width (`u8`–`i64`, `usize`) order chains, and unreachable-branch contradictions. | Zero solver-trust axioms; every certificate replays in Rocq within search budget. |
| Guard-checker fixes & bypass auditing (Rocq #22382 / CVE-2026-72705 patched in 9.3.0; arXiv:2603.20405) | [The solver ledger](../../tools/toolchain/solver_ledger.py) strips nested comments and refuses `Parameter`/`Conjecture`/`Admitted`/`admit` and `Unset Guard/Positivity/Universe Checking` or `Set Type in Type`; `check_prover_version` requires Rocq `>= 9.3.0`. | Supplements statement preservation and `Print Assumptions`; does not establish informal-intent adequacy. |
| Funnel & Elastic hashing (Farach-Colton, Krapivin, Kuszmaul, FOCS 2025, disproving Yao's 1985 conjecture) | [FunnelTable](../../tools/rocq/funnel_table.v) mechanizes fixed-capacity funnel layouts in Rocq 9.3.0 (bounds, level disjointness, non-reordering slot immutability, completeness, fail-closed exhaustion, bounded probes). | Targets extreme load ($\delta < 0.05$) in zero-heap immovable storage; linear probing still wins at moderate loads via locality. |
| Reverse-postorder iterative dominators | [Loan CFG validation](../../tools/toolchain/loans.py) computes reachability + RPO in one DFS pass and converges dominators in 1–2 passes on reducible graphs. | Preserves exact dominators and irreducible-cycle refusals; diagnostic engine stays outside target certificates. |

**Evaluated 2025–2026 results not incorporated:**

- **Unreviewed late-2026 AI-assisted complexity/math claims** (Oct 2026 ETH disproofs, Oct 2026 *The Unique Games Theorem*, Nov 2026 $\text{VP} \neq \text{VNP}$, Aaronson–Ambainis formalizations, Millennium claims): unreviewed preprints or non-compiler separations; operational bypass lesson is enforced in [the solver ledger](../../tools/toolchain/solver_ledger.py).
- **Sub-sorting directed shortest paths** (Duan, Mao, Mao, Shu, Yin, STOC 2025, $O(m \log^{2/3} n)$): targets huge sparse graphs; HoldFast's bounded CFGs/proof graphs ($n \le 256$) and difference-logic cycle checks are faster with BFS/Bellman-Ford.
- **Time-in-square-root-space simulation** (Ryan Williams, STOC 2025, $O(\sqrt{t \log t})$ via Cook–Mertz tree eval): algebraic overhead mismatches static-memory CHERI execution.
- **Linear-time planar 4-coloring / near-linear Vizing edge coloring** (Inoue et al., FOCS 2026; STOC 2025): does not replace non-planar interference-graph register allocation in CHERI-CompCert.

### What a Golden Binary Can Mean

A binary is executable, but being executable does not make it a correctness oracle for itself.
The target is a **proof-carrying executable reference implementation**: exact bytes, interpreted by a named target semantics, proved to refine an independently reviewed contract.
For VerifiedOS that semantics is currently the pinned Sail term; a [qualified successor](../extensions/unified-source-contract.md#migration-and-retirement) must become the same shared subject for binary and hardware proofs. A different target needs its own interpretation and artifact theorem.
An optimized implementation can then serve as a fast oracle for other implementations of that contract.
The portable object is the contract and its reusable proof structure, not a universal binary or a target-independent timing theorem.
Independent specification review and differential tests remain necessary because agreement with itself cannot reveal a wrong specification.

The evidence chain separates the following judgments:

- Source elaboration preserves the meaning of the authored program and its contract.
- The concrete representation implements the abstract values and state transitions.
- Compilation, assembly, linking, and image construction preserve the required behavior.
- Final bytes satisfy the required admission properties under the pinned Sail model.
- Hardware implements that model at the tier the platform actually claims.

Different target binaries may implement the same abstract contract through different representations, provided their input/output encodings and permitted observations are related explicitly.
For a nondeterministic or underspecified contract, correct implementations need not produce identical traces; differential comparison must respect the contract rather than assume byte-for-byte output agreement.

Functional refinement alone does not prove constant-time behavior, worst-case execution time, absence of hidden allocation, or robust isolation against adversarial linked code.
Those remain the separately scoped obligations of the [specification](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md) and [admission language](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/typed-assembly-language.md).
Neither an optimizing compiler nor an SMT success verdict closes them by implication.

### C*: The Useful Idea and the Actual Boundary

[C*: Unifying Programming and Verification in C](https://arxiv.org/html/2504.02246v1), April 2025, integrates executable C, assertions, and programmable proof blocks using familiar C syntax.
Its valuable idea is a single development surface: inspect a symbolic program state, transform it with a proved lemma, and continue writing implementation code.
Proof libraries become ordinary reusable programming tools instead of a separate after-the-fact activity.

The paper's implementation and evaluation impose important limits:

- The proof kernel is HOL Light, exposed through a C interface. It is not Coq/Rocq.
- The symbolic execution engine is trusted. A small LCF kernel does not by itself validate the engine's interpretation of C.
- Separation logic is axiomatized, with integers and pointers treated alike in the logical memory model. This is not the project's purecap provenance model.
- The prototype manually interleaves runs of the symbolic executor; the live IDE is future work in this version of the paper.
- The evaluation includes small examples and the buddy allocator's attach operation, not verification of an entire allocator or a compiler-to-binary theorem.
- The authors explicitly retain a weaker allocator specification that does not establish that every free block occurs in the free list. This is a concrete warning about specification adequacy.

**Disposition:** borrow the integrated proof-block workflow and reusable state-transformation libraries.
Do not import HOL Light as an additional admission authority, treat its symbolic executor as foundational, or infer a CHERI-aware verified compilation path from its use of C.
The closest project-compatible implementation of that interaction is a Rocq-native workflow over the program logics already selected here.

### Idris Flexibility Without an Idris Runtime

Idris 2's [quantities](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html) distinguish erased values, values used exactly once, and unrestricted values.
The pinned comparison uses [Idris 2 v0.8.0](https://github.com/idris-lang/Idris2/releases/tag/v0.8.0).
This is more useful than simply adding dependent array lengths: ownership protocols can evolve in types, and the type signature can state which indices are unavailable at runtime.
However, linear use of a parameter is not the same as unique ownership of all reachable storage, and neither guarantees stack allocation or eliminates garbage collection.
Rust borrowing also permits temporary aliases with lifetime constraints; an exact-use multiplicity is not a substitute for that discipline.

The [Idris theorem-proving guide](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html) distinguishes total proofs from partial programs and warns about its totality checker's implementation.
The [backend documentation](https://idris2.readthedocs.io/en/latest/backends/index.html) describes Scheme and reference-counted C among its execution routes.
Neither document supplies a verified optimizing CHERI compilation theorem.
Thus Idris 2 is a design reference here, not an assurance shortcut.

The proposed split is deliberate:

- **Specification/proof world:** dependent functions, indexed families, existential packages, induction, rich mathematical structures, and reusable verified algorithms. Elaborate into CIC; use only its accepted assumptions and reject unresolved proof holes.
- **Runtime world:** explicit finite representations, machine integers, bounded arrays, regions and resource handles, ownership/borrowing, and statically accounted effects. The VerifiedOS instance represents applicable handles with CHERI capabilities. Rich types may describe these values without becoming runtime objects.
- **Proof automation:** arbitrary proof search may time out or fail, on the device or off it. Successful search produces a checked term; nontermination of a tactic never produces a theorem or permission to ship.

This is not a promise to embed all of Idris 2 unchanged in Rocq.
Universe rules, conversion, positivity, equality elimination, and quantitative resource judgments need a specified mapping.
In particular, CIC does not acquire a linear context because a frontend spells `owned`; the ownership discipline needs a semantic soundness proof in the existing program logic.
For the initial library, that discipline is exposed through predicates and proved combinators rather than a new type theory.

Erasure has a concrete test: two terms differing only in proof data must have the same relevant behavior under the erasure relation.
A runtime loop cannot read an erased length. It can read a stored length proved equal to the erased index, or use a compile-time specialized constant.
An existential packet length discovered while parsing therefore remains a runtime integer with an erased proof, not magically compile-time knowledge.

#### Reading the Graded-Type Claims

The fixed quantity set in Idris 2 is a language implementation choice, not a definition of every quantitative type theory.
The theory is Atkey and McBride's, with [Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/abs/2104.00480), ECOOP 2021, describing that language's realization of it; crediting the design to Idris 2 misattributes it, and the paper is not evidence that Idris lets a program replace its grading algebra.
Comparisons below distinguish a calculus parameterized by an algebra, a prototype implementing particular grades, and an extensible production language.
These are different levels of evidence.

**Idris 2 offers useful libraries without arbitrary grades.** Its actual [linear IO library](https://github.com/idris-lang/Idris2/blob/v0.8.0/libs/linear/Control/Linear/LIO.idr), read at that tag, indexes `L` by result usage and supplies `Pure0`, `Pure1`, `PureW`, and corresponding continuation types.
It can require an action's result to be used linearly, which is useful for state-changing resource APIs.
The implementation explicitly repeats definitions because multiplicity polymorphism is absent; its `Usage` datatype does not change the compiler's core quantity algebra.
The immediate lesson is to build state-indexed operations and proved combinators now, not wait for a fully general graded compiler.

**Granule is a working graded-language laboratory, with indexed rather than full dependent types.** Its [language guide](https://granule-project.github.io/granule.html) demonstrates exact-use modalities, security labels, and IO effects.
For example, the essential shape of its vector map signature is `(a -> b) [n] -> Vec n a -> Vec n b`: the callback is available for the vector's number of elements.
Its `twice` example composes usage through multiplication, while security examples reject a private-to-public flow and permit ignoring an unused private input.
These are different interpretations of grading, not interchangeable meanings of the same numeric annotation.
Its [implementation](https://github.com/granule-project/granule) provides an interpreter/checker and a compiler to Haskell with a runtime library; the separate LLVM compiler is described as experimental.
The language guide describes programmer-customizable modalities as a goal. Built-in grades and theoretical parameterization should not be presented as a finished general plugin system.
Exact callback accounting also does not specify map's element order; a functional contract is still needed.
Granule also implements [derived modality-distribution combinators](https://arxiv.org/abs/2112.14966) and [grade-directed program synthesis](https://doi.org/10.1007/978-3-031-57262-3_4). These address composition boilerplate and search, respectively; their [conditional HoldFast qualification](../extensions/graded-foundation.md#conditional-usability-producers) requires a real library client, checked output and measured benefit over existing combinators or proof search. Neither is supplied by general grade syntax or required for the first release.

**Gerty implements GrTT's distinction between computation use and type use.** In [Graded Modal Dependent Type Theory](https://arxiv.org/html/2010.13163v2), the preprint of the ESOP 2021 paper, a dependent function binder carries a pair of grades, with further bookkeeping for dependencies in the typing context.
The [Gerty implementation](https://github.com/granule-project/gerty) illustrates this with the binder `(a : (.0, .2) Type 0)`: no computational use of `a`, but two uses in the remaining type.
That is more precise than tracking runtime erasure alone and can recover restricted parametric reasoning inside a dependent setting.
It is not unrestricted dependence without constraints: elimination rules must respect resource usage, and graded modalities are needed to use parts of compound values differently.
The paper's strong-normalization result is explicitly for a restricted two-universe fragment, not every conceivable extension of the language.
That metatheory is also pen-and-paper: no machine-checked development accompanies it, and the prototype is a research implementation whose constraint solving is a trusted external oracle and which is not verified against the calculus.

Gerty's typechecker optimization is concrete and narrow: for a suitable quantitative semiring, a zero type-use grade lets application checking omit a substitution into a codomain that does not semantically depend on the argument.
It does not erase arbitrary proof obligations or skip checking whether a program is valid.
The paper evaluates small fanout examples, with benefits dependent on whether grade equality uses normalization or SMT; extra solver calls can make the optimization slower.
The implementation exposes `--tyc-optimise`, but this is not evidence of a production-scale or self-optimizing verification compiler.
First-class grade terms and internally defined semiring instances are explicitly future work in the paper. The inspected README does not establish that these extensions are completed.

**GraD supplies a semantic test for what grades actually guarantee.** [A Graded Dependent Type System with a Usage-Aware Semantics](https://arxiv.org/html/2011.04070v2) uses a partially ordered semiring and a heap-based, usage-aware operational semantics.
It tracks runtime demand, checking but discarding irrelevant type-use counts when computing that demand; it does not retain GrTT's separate type-use vector.
Its key point is that ordinary progress and preservation do not prove correct resource accounting: a separate usage-aware soundness theorem is necessary.
The paper derives irrelevance noninterference and a single-pointer property under additional algebraic conditions, and reports Coq mechanization of selected syntactic metatheory, not a fully mechanized native compiler.
Its simplified dependent calculus uses `Type : Type`; it must not be adopted as this project's consistent proof logic.
Use it to guide a resource interpretation inside CIC, retaining Rocq's universes and logic.

Even the meaning of `0` and `1` needs proof: in a Boolean semiring, `1 + 1 = 1`, so grade `1` does not establish single use.
GraD distinguishes the conditions needed for unusability of zero from those needed for linearity and its stronger single-pointer result.
Its single-pointer property concerns the paper's heap graph, not CHERI capabilities, arbitrary imperative aliasing, DMA, or revocation.
The connection from such a grade to a concrete operation must be proved in the existing program semantics.
Likewise, a security lattice needs an observation model and noninterference theorem; a privacy budget needs probabilistic semantics and a sensitivity/composition theorem; an operation count needs an instruction/cost connection before it says anything about WCET.

**Proto-Quipper is a useful boundary case, not a systems backend.** [Linear dependent type theory for quantum programming languages](https://arxiv.org/abs/2004.13472), by Fu, Kishida, and Selinger, is the work corresponding to the [LICS 2020 DOI](https://doi.org/10.1145/3373718.3394765), with an extended LMCS version in 2022.
It combines linear quantum resources with classical parameters indexing circuit families and includes a prototype.
The transferable idea is to distinguish a resource from the duplicable description or shape used to index it.
No-cloning does not mean physical quantum systems can never be discarded; a language's explicit disposal or uncomputation discipline is a separate rule.
Quantum semantics add no direct implementation advantage to the bounded classical components proposed here.

**A mechanized erasure reference complements Gerty.** Abel, Danielsson and Eriksson's [A Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized](https://research.chalmers.se/en/publication/537991), ICFP 2023, reports Agda proofs of consistency, normalization, decidable definitional equality and grade preservation, with extraction soundness for specified modalities and context restrictions. Its dependent pairs and erasure side conditions are a concrete comparison for [the graded foundation](../extensions/graded-foundation.md). These results do not transfer automatically to CIC or to a calculus with mutable state and handlers.

That article is the peer-reviewed half of a pair, and the current development is its [extended version](https://arxiv.org/abs/2603.29716), revised 30 April 2026, which adds unit and graded dependent pair types. Read it for what its extraction theorem actually says: soundness holds for a restricted class of modalities, the value-preservation statement is about natural-number-typed programs, and open programs need every context variable erasable, a consistent context and a ban on erased matching for the weak pair. Nothing is proved about an implementation, and Agda's own checker remains the trusted base. Its Agda development is MIT-licensed and its repository is shared with several other papers, so naming this paper's artifact means pinning the tag that version renders under, not the repository.

**Two 2026 erasure results, both checked in Agda, bear on the same obligations.** Danielsson's [Erased Postulates, Identity Types and Quotients](https://arxiv.org/abs/2609.08578), a preprint of 8 September 2026, adds identity types to the development's extraction guarantee, proved inside the same graded formalization, and shows that transport along erased identity proofs is safe without quotients and postulates, and beside quotients and erased postulates that equality reflection can implement, but that unrestricted transports of this kind are incompatible with erased postulated univalence; that bears on [the transports an elaborator inserts](#layered-proof-and-staging) when a grade erases their proofs. Theocharis and Brady's [Type Theory With Erasure](https://arxiv.org/abs/2605.00655), accepted to FSCD 2026, states erasure as a phase distinction, a proposition that can occur in a context rather than a zero grade, proves it conservative over Martin-Löf type theory in both phases and its extraction correct by gluing, and supplies a toy elaborator; its metatheory assumes function extensionality, UIP and quotient inductive-inductive types. It supports keeping [phase and representation](../extensions/graded-foundation.md#dimensions-and-lawful-domains) a dimension apart from computation use, as the graded foundation does. Both are about Martin-Löf type theory rather than CIC with impredicative `Prop`, neither covers mutable state or handlers, and neither development's terms are read here.

**Dependent multiplicities put index-valued grades inside an unmodified host.** Doré's [Dependent Multiplicities in Dependent Linear Type Theory](https://arxiv.org/abs/2507.08759), a preprint last revised 19 May 2026 with no venue stated, lets a variable's multiplicity depend on other variables, so a binary-tree recursor consumes its leaf case's resources once per leaf, typing branching and recursive programs that other theories cannot type precisely. It embeds linear logic into dependent type theory without changing the host's structural rules, and its Agda prototype represents each linear term as an ordinary host term with a supply witness. The artifact checks the type-former interpretation lemmas, the author builds every linearity witness by hand, and the guarantee is value linearity rather than a cost bound. It is the closest published shape for [grade expressions over stable indices](../extensions/graded-foundation.md#substitution-and-structural-rules) interpreted in the host rather than in a new kernel; the paper says the construction carries over to Rocq but reports no Rocq build, and its anonymous artifact's terms are unread here.

**Rocq's own erasure removes only propositions and types, so an erased index needs HoldFast's own theorem.** Extraction and MetaRocq's certified erasure both rest on the elimination restrictions of `Prop` and `SProp`, so a proof-relevant index in `Type`, such as the natural-number index of `fin`, survives into the extracted program even where no branch inspects it. [A Ghost Sort for Proof-Relevant yet Erased Data in Rocq and MetaRocq](https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper81.pdf), a TYPES 2025 abstract by Rosain, Sozeau and Winterhalter, proposes a new sort for exactly that data. It weighs three elimination rules in Rocq experiments built on sort polymorphism and plans, rather than reports, the MetaRocq erasure proof; [the 9.3.0 manual](https://rocq-prover.org/doc/V9.3.0/refman/language/core/sorts.html) still lists only `SProp`, `Prop`, `Set` and `Type`, and a new sort would be a kernel change outside this design's CIC authority. The nearest same-prover mechanization of tracked irrelevance is Liu, Chan and Weirich's [DCOIω](https://doi.org/10.1145/3704843), POPL 2025, whose Coq proofs show a calculus that tracks dependency to identify run-time and compile-time irrelevance consistent and normalizing, with decidable conversion. That conversion compares terms up to indistinguishability, an equality rule CIC lacks, so it is a proof-engineering donor for [the substitution and erasure debts](../extensions/graded-foundation.md#proof-and-qualification-obligations) rather than an elaboration target, and its artifact's Coq version and terms are unread here.

**Design consequence:** make [graded dependent typing](#graded-dependent-foundation) part of HoldFast's foundation while keeping runtime representation, erasure, permission ownership, protocol state, effects and quantitative bounds separately interpreted. Library-level proofs would qualify the relationships needed by initial clients. The [composition contract](../extensions/full-language-review.md#implementation-obligations) specifies the interaction laws.

## Language design and target interfaces

### Target Abstraction and Tooling Evolution

The framework can hide architecture from ordinary component authors, but cannot remove architecture from the proof chain.
Separate source portability, generic proof reuse, concrete representation correctness, and artifact security.
A component qualifies for a target only when that target supplies the laws and guarantees it requires.
Making the interface small does not make the target's compiler, memory model, or hardware proofs small.

#### Portable Interfaces and Concrete Instances

| Layer | Reusable content | Instance-specific evidence |
| --- | --- | --- |
| Language and editor | Syntax, dependent contracts, proof interaction, source locations, diagnostic protocol | Interpretation of target-sensitive features and profile compatibility |
| Pure specifications | Abstract sequences, algorithm results, format meaning, protocol transitions | Encodings and relationships to represented input/output values |
| Operation and resource interfaces | Ownership, scoped borrows, framing, explicit effects, primitive contracts | Sound implementation of each operation and law in the chosen program logic |
| Program construction | Generic induction and composition over proved primitive rules | Concrete program terms, numeric limits, layout, ABI, and compilation preservation |
| Artifact evidence | Dependency tracking, proof orchestration, explicit theorem subjects | Binary semantics, permitted contexts, linking, observation/leakage model, hardware assumptions |

For the bounded-buffer example, the interface can have this schematic shape:

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

This is an interface sketch, not a new memory semantics or a complete declaration of these proof rules.
The concrete rules must bind the operation's program term, entry and exit representation, arithmetic premises, effects, frame, and permitted interference.
Index conversion and iteration expose a representability bound and proved increment rule; the generic algorithm cannot assume an unbounded machine index.
The generic fill theorem quantifies over these laws. The VerifiedOS instance discharges them over its selected CHERI-aware semantics and transport, rather than asserting a flat-address memory model that CHERI must emulate.
Keep handles opaque: pointer width, integer casts, address equality, provenance, capability tags, bounds compression, endianness, and alignment are not implicit generic facts.
An operation that genuinely needs one of them states that dependency in a narrower interface.

**The interface is a proof-side abstraction and never a second way to reach the machine, which is a register constraint rather than a design preference.**
[A verified component explicitly naming a profile instruction that no ordinary lowering duty reaches uses exactly one surface](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-023b), a backend primitive named by that instruction's own profile mnemonic and operand form and taking its meaning from the pinned Sail clause for it, and that surface is a duty of [the two required certifying compilers](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-18-014) rather than a deliverable standing beside them.
An operation law here is therefore discharged over that primitive and inherits its meaning; a law that introduced a machine operation of its own would be the second surface the register says does not exist.
The constraint binds the instance and not the generic modules, and it is what keeps a target interface from quietly becoming a competing backend.

Use static module instantiation and specialization, not runtime virtual dispatch, for this abstraction.
Logical parameters and law proofs are erased; actual storage handles and required runtime metadata remain.
Inlining, layout, and generated code still need inspection and the selected compilation evidence: a module boundary alone promises neither zero overhead nor good code generation.
The high-level loop invariant can be reused even when the concrete representation and primitive proofs differ.

The first instance is CHERI-specific; the generic modules are not.
In a separate reuse project, an ordinary-architecture implementation could discharge a bounded buffer contract through verified ownership and access operations.
That example would demonstrate portability of this contract, not equivalence to VerifiedOS's isolation model or authorization for a non-CHERI VerifiedOS target.
Do not build a second implementation here merely to fill an adapter roster.

#### Required Guarantees, Not Feature Flags

A target profile identifies the semantic instance, representation and ABI choices, accepted assumptions, and available guarantee theorems.
A component declares required guarantees; acceptance needs checked evidence that the profile supplies them, not a Boolean claiming that the target supports a feature.
Keep useful guarantees independent instead of making every target implement a universal interface:

| Requirement | What can be shared | What the target must justify |
| --- | --- | --- |
| Bounded storage access | Contents, bounds, and frame contracts | Representation, primitive safety, arithmetic limits, and relevant execution contexts |
| Exclusive mutation | Ownership and borrow-restoration rules | Sound resource interpretation, including any unsafe or external code |
| Isolation from adversarial code | Statement of authority confinement and allowed observations | Hardware enforcement, verified software enforcement, or sufficient restrictions on linked contexts |
| Revocation or freshness | Protocol interfaces and abstract transition requirements | The actual invalidation mechanism, epoch rules, and interference assumptions; CHERI alone is not a blanket temporal-safety proof |
| Information flow and constant time | Relational specification and some compositional proof rules | Target observations, instruction behavior, compiler preservation, and applicable hardware leakage model |
| Resource bounds | Abstract accounting and bounded-loop arguments | Mapping to allocation, instruction costs, or timing under the chosen environment |

A target may implement a guarantee differently, with additional runtime cost and proof obligations.
It may also be unable to implement it under the requested threat model.
In that case the tooling rejects the component/profile pairing or the author explicitly selects a different contract; it never silently weakens the guarantee.
Source-level ownership on conventional hardware does not protect against arbitrary unverified code with unrestricted memory access.
Conversely, a CHERI backend does not automatically establish functional correctness, liveness, or every form of revocation.
This preserves stronger optional guarantees without reducing every component to the weakest common target.

#### Refactoring Without Expanding Trust

The iteration boundary is a reviewed semantic interface, not a permanent surface-language design:

```text
Editable language, inference, automation, and editor tools
    -> explicit program terms and proof obligations with source correspondence
    -> reusable Rocq component interfaces and generic theorems
    -> concrete semantic instance and proved target laws
    -> target compiler and final-artifact evidence
```

Frontend elaborators, tactics, solvers, and AI assistants may change frequently because their proposed proofs are rechecked.
Their output must still identify the intended source program and contract; proof-producing does not excuse an incorrect source translation.
Initially these outputs are ordinary Rocq terms over the existing backend, not a newly invented universal intermediate language or trusted checker.
Adding a new meaning for a language construct needs explicit semantics and corresponding proof work, even if its syntax looks like a small edit.

| Change | Reuse opportunity | Required revalidation |
| --- | --- | --- |
| Editor presentation or lemma search | Same statements, program terms, and target laws | Tool behavior; replay of new proof output, if any |
| New syntax or inference strategy with unchanged meaning | Same generic component and backend theorems | Elaboration and exact source-subject correspondence; invalidate changed source bindings |
| Refactored algorithm preserving a contract | Same client-facing contract and target primitive laws | The changed implementation's proof, termination/effects, and affected binary evidence |
| New storage representation | Same abstract algorithm contract and generic theorem | Representation and primitive laws, layout/ABI, compilation and affected artifacts |
| Changed interface law or observation model | Only results independent of the change | Dependent generic and instance proofs; no reuse based solely on unchanged names |
| Different target or emitted bytes | Applicable abstract contracts and generic lemmas | Target law instantiation and all affected final-artifact bindings and judgments |

Use dependency identities covering semantic definitions, theorem statements, representations, assumptions, source closure, and the relevant toolchain/artifact inputs.
Incremental checking can avoid rebuilding unaffected results, but a source change can invalidate its binding even when it emits identical machine code.
Retaining an exact existing binary theorem is distinct from establishing that it corresponds to the newly authored source.
Caching must follow the existing evidence discipline and cannot turn a stale success flag into authority.
No new on-device solving, grade interpretation, or open-term reduction is introduced into VerifiedOS's TAL checker.

This design supports rapid tooling iteration without requiring compatibility with a released language: this is a proposal, not a frozen public API.
The aim is to localize the proof consequences of a change, not prohibit necessary changes to the semantic interface.

### A compositional core

The [core design](../language/core-design.md#judgments-and-interpretations)
defines dependent values, the resource context and the interpreted computation.
Its [kinded authority](../language/core-design.md#kinded-authority),
[loan rules](../language/core-design.md#loans-and-control-flow) and
[staging rules](../language/core-design.md#refinement-effects-and-staging)
keep ownership, captures, effects and representation distinct. The
[composition contract](../extensions/full-language-review.md) extends those
judgments to graded usage, handlers, tasks and cells.

#### Layered Proof and Staging

Routine checking has a defined order:

1. Kernel-compatible definitional computation and normalization.
2. Flow-sensitive capture and ownership checking with a sound resource interpretation.
3. A declared decidable refinement fragment, with reconstructable or certificate-producing automation.
4. Domain procedures and standard-library lemmas for finite sequences (`.All`, `.Any`, `.Contains`, `.Take`, `.Skip`, `.Slice`, `.Count`, `.Update`, `.Append`), arrays, frames and finite arithmetic.
5. Explicit Rocq lemmas and proofs for residual obligations.

The refinement tier targets bounded integer ranges, capacity relationships, alignment, discriminants, initialization, bounded predicates and subrange projections over finite sequences on `.Model`, and simple typestate, with nullity checks only for types that admit a null state. Bounded sequence predicates such as `items.Model.All(x => x > 0)`, `.Any(x => ...)`, `.Contains(x)`, `.Take(n)`, `.Skip(n)`, `.Slice(a, b)` and `.Count` whose element bodies stay in the supported fragment discharge through pre-proved standard-library lemmas in the decidable/domain refinement tier rather than open `forall`/`exists` quantifier instantiation. Sparse prefix/suffix range facts over bounded buffers and vacant-slot arrays (`slots[0..length)` initialized, `slots[length..capacity)` vacant) must remain symbolic in static capacity `capacity`: elaboration, the refinement/domain tier and kernel conversion never enumerate elements proportionally to `capacity`, and [qualification](../language/first-release.md#qualification) enforces a capacity-invariance gate requiring equal obligation counts and proof/certificate structure at tiny ($N = 4$) and large ($N = 10^9$) static capacities after replacing the encoded capacity numeral. The range certificate must stay symbolic and both instances must pass the declared finite replay time and output budgets. Elapsed times vary with host load and numeral conversion; report them alongside the structural checks. Specify the logic and supported arithmetic before calling it decidable: arbitrary open quantified mathematics and arbitrary nonlinear arithmetic are not included by implication. Flux, LiquidHaskell and RefinedC supply design comparisons, not accepted solver encodings. Reconstruction follows R-05-017 where SMT contributes facts; failure or timeout leaves a goal, never an assumed refinement or an extended conversion rule. A qualification of this tier reports the obligation population, discharge rate, latency, stability after edits and manual proof burden without a predicted percentage.

Equality ergonomics first use canonical indices, normalization, bidirectional insertion of checked transports and derived decidable equality with locally proved uniqueness where applicable. Logical proof irrelevance is used only where proved for the particular proposition. Runtime proof erasure needs its own preservation theorem and confers no additional equality principle. Cubical or observational equality is a separately scoped kernel or translation research question, outside this core's CIC authority.

Staging distinguishes pure specification evaluation, compile-time code/evidence
generation, represented runtime computation and checked proof terms. The
[metaprogramming rules](../extensions/metaprogramming.md#evaluation-and-phase-boundaries)
require explicit static inputs, kernel-compatible conversion and checked
cross-stage representation. A static bound can specialize a loop or layout; a
discovered packet length stays represented runtime data. Bounded generator failure
produces no accepted component, and generation grants no theorem or resource
permission. Input/dependency identities, independent intent review and negative
examples remain required: a generator and a host oracle sharing one evaluator
cannot supply independent agreement. Machine evidence retains the canonical
Sail subject or its separately qualified successor.

#### Compositional Leakage Obligations

A source `ConstantTime` requirement denotes a relational contract: executions agreeing on public inputs and the declared entry relation have equivalent permitted observations, including branch, address and termination behavior where the selected observation model includes them. Combinators preserve that relation and callees expose compatible observation contracts; a label or effect flag is not its proof. This exposes secret-dependent control or addressing while the author can still diagnose it locally.

The compiler must preserve the relation through representation, optimization, ABI and linkage to the required TAL or CIC judgment on final bytes. Ordinary functional simulation does not suffice. Target assumptions follow the actual profile: hardware caches and speculative execution are excluded here, so their absence is checked rather than silently replaced by a commodity leakage model. Instruction timing, explicit memory traffic and other declared observations still need their proofs; physical leakage outside that model remains outside the claim. Jasmin is a design comparator, not a new compilation route for this instance.

#### Type Theory and Elaboration Reuse

The relevant research supplies complementary rules and implementation techniques. It does not establish that stacking all the source calculi produces a sound or usable language. A qualification selects one presentation and tests the interactions it actually supports; a new translator or program semantics retains the register's admission conditions.

| Source | Contribution and disposition |
| --- | --- |
| Dunfield and Krishnaswami, [Bidirectional Typing](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/), 2021; Slattery and Sterling, [Bidirectional Elaborators à la Carte](https://arxiv.org/html/2607.09564v2), July 2026 | Use declared interfaces to bound inference, and make elaboration stable under core equality and substitution. The newer paper supplies compositional elaboration laws, but its mechanized implementation, universes, holes, implicit arguments and typeclasses remain future work. It is a design reference, not a Rocq package or a reason to import its extensional metalanguage as axioms. |
| Ahman, Ghani and Plotkin, [Dependent Types and Fibred Computational Effects](https://danel.ahman.ee/papers/fossacs16.pdf), 2016; [dependent call-by-push-value analysis](https://arxiv.org/abs/1603.04298) | Separate stable values from computations, packaging runtime-discovered indices in dependent results. Use this discipline for parsers and state transitions; introducing a separate authoritative CBPV semantics is unnecessary for the library proposal. The papers' richer models do not automatically validate unrestricted dependence on mutable state. |
| [Modal Effect Types](https://arxiv.org/abs/2407.11816), OOPSLA 2025; [Rows and Capabilities as Modal Effects](https://arxiv.org/html/2507.10301v2), POPL 2026 | Compare concise higher-order effect inference and translations between row-based and capability-based presentations before inventing duplicate effect mechanisms. Language effect capabilities are not CHERI hardware authority. The [METL artifact](https://github.com/thwfhk/met-oopsla25-artifact) provides parsing, bidirectional checking and interpretation, but explicitly lacks METL-to-MET elaboration, effect variables and low-level compilation. General modal effects remain beyond the initial footprint summaries. |
| [What's in the Box](https://2025.splashcon.org/details/OOPSLA/133/What-s-in-the-Box-Ergonomic-and-Expressive-Capture-Tracking-over-Generic-Data-Struct), OOPSLA 2025; [System Capybara](https://arxiv.org/abs/2607.09383), July 2026 preprint | Scala 3's capture checker tracks the capabilities a closure or generic container retains, with reach capabilities naming those inside boxed elements, and its new separation checker adds consumption, freshness and read-only tracking over the same capture sets. Capless is mechanized in Lean for type soundness and scope safety, and Capybara's Lean semantic soundness result yields no use-after-free or double free and data-race freedom. It is the closest mechanized design for [transitive captures](../language/core-design.md#kinded-authority) through instantiated type parameters, and its `consume` and read-only mechanics are candidates inside the [mutability dossier's](../extensions/interior-mutability.md) sharing rules. It derives uniqueness from one capture analysis where HoldFast keeps memory loans, hardware capabilities and effect permissions as separately interpreted kinds, and its proofs are Lean's, so it is a design reference. |
| [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383), POPL 2024; [Affect: An Affine Type and Effect System](https://iris-project.org/pdfs/2025-popl-affect.pdf), POPL 2025 | Continuations that discard or duplicate their captured context interact with ownership. Affect provides an affine type/effect system with Iris-based semantic soundness mechanized in Rocq, built over the Hazel handler logic and covering continuations stored in mutable references. The other is pen-and-paper with a Links implementation, so it supplies a calculus and the soundness bug that motivated it rather than a checked development, and its artifact is GPL-3.0-or-later. [The handler dossier](../extensions/handlers-async.md) uses these resource rules for general handlers and suspension; their language and runtime are not the selected CHERI instance, so their use needs a concrete machine interpretation. |
| [A Mixed Linear and Graded Logic](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2025.32), CSL 2025; [Same Coeffect, Different Base](https://arxiv.org/abs/2606.28042), ICFP 2026 | Modal decomposition and translations between graded-base and linear-base presentations help identify when two annotations encode the same information. Keep a simple ownership surface plus separately interpreted resource contracts; these results do not supply the full dependent, mutable frontend or authorize a generic on-device grade interpreter. The translations are pen-and-paper and preserve typing, grades and equations in each direction; they are not full abstraction, no artifact accompanies them, and they establish nothing about any implementation of either lineage. |
| [Autosubst](https://github.com/rocq-community/autosubst) and [Autosubst OCaml](https://github.com/uds-psl/autosubst-ocaml) | If a separately scoped frontend needs binding syntax, inspect generated substitution operations and proofs before hand-authoring them. Autosubst advertises Rocq 9.0+ support. The OCaml generator avoids functional extensionality in its generated lemmas, but its [published package](https://rocq-prover.org/p/rocq-autosubst-ocaml/1.1%2B9.0) constrains `rocq-core` to `>= 9.0 & < 9.1`, which excludes the locked [proof snapshot](../../tools/opam/rocq.lock), and lacks modular syntax. The older [Haskell generator](https://github.com/uds-psl/autosubst2) imports functional extensionality. Qualify the chosen output and tuple; the current combinator library needs no new AST dependency. |

The existing [Equations](https://github.com/rocq-prover/equations) and [Rocq-Elpi](https://github.com/LPCIC/coq-elpi) qualifications cover dependent definitions, checked derivations, quotations and environment interaction. The [Equations indexed-types tutorial](https://rocq-prover.github.io/platform-docs/equations/tutorial_indexed.html) distinguishes constructive uniqueness-of-identity-proofs for decidable indices from a global axiom, and warns that axioms can obstruct computation. [Q19b's trial](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-tooling-qualification.md#q19b-dependent-computation-equations-and-equality-principles) confirmed that a selected indexed definition computes, that its generated equations replay and that decidable-index transport needs no global UIP, and then retained the handwritten match because the small client showed no maintenance gain. Elpi's higher-order abstract syntax can support a narrow elaboration task; MetaRocq retains its quotation/metatheory role. No package choice by itself supplies source correspondence or linear resource interpretation. Each incorporation still reads the chosen artifact's actual licence and dependency notices.

The locked prover also ships [user-declared rewrite rules](https://rocq-prover.org/doc/V9.3.0/refman/addendum/rewrite-rules.html) behind the `-allow-rewrite-rules` flag: `Symbol` constants reduce by rules that extend conversion, the manual calls them highly experimental, confluence and termination go unchecked, and type preservation gets only a superficial check that warns. Declaring grade arithmetic or an observational equality that way would make it compute definitionally, and the route is closed here: the proof gate's [kernel recheck](https://github.com/symbiogenesis/VerifiedOS/blob/main/tools/vos/proofaudit.py) refuses any summary whose theory line is not `Rewrite rules are not allowed`, matching [the equality ergonomics'](#layered-proof-and-staging) exclusion of kernel equality changes. Unresolved grade equalities therefore stay explicit proof obligations.

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

`PacketFormat.ParsePrefix` is the full success and error model supplied by the independently reviewed format descriptor, not a second handwritten specification. The name fixes prefix parsing and its trailing-input policy; an exact-input parser would be a separately named `ParseExact`. `'input` names the parameter's loan, so the signature declares no region or index parameter: the view borrows from `input`, and `Span<byte>` carries its own length. The record declares `region 'source` because it has no parameter to name. The shared loan keeps the input stable while any view is live, which is stronger than read-only access through one variable. An error carries no view, and the retained result tag, not an erased proof, selects the branch. This interface is a candidate surface over the existing [descriptor-to-implementation route](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-043).

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

Every operation that lowers the length needs `Entries`, so while an entry loan lives its extent stays below the length, which is the disjointness `Push`'s footprint needs. A consume-and-return `Push` would instead end every loan on the log.

In the bounded library proposal, `SetFirst`'s update comes from `Build.with_element`, exposed as `WithElement(ref target, 0, (scoped ref byte selected) => { selected = value; })`. Its rule introduces a fresh loan inside the callback contract, suspends the parent while it is active, and forbids placing the loan in the callback's result or a longer-lived capture. Given a total callback contract it proves invocation once, termination and restoration; a once-callable type alone proves none of those facts about its caller. The pilot callback may return a `Result`, restoring the parent before the caller propagates an error, but supports neither a return out of the caller nor suspension. The target loan model must handle each supported exit explicitly, including branch-sensitive returned loans, loop edges and `Result` propagation, and cannot claim them from the callback theorem. A source frontend must prove this elaboration, not merely print the combinator call. Measure rewrite cost at the same resource boundary in the [conditional borrowing comparison](../language/loan-analysis.md#conditional-borrowing-comparison).

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

Opening `open (ref this, ref destination) lifts InitializedPrefix, VacantSuffix` records a linear [`CloseDebt`](../extensions/interior-mutability.md#representation-authority-and-open-invariants) for those two conjuncts while keeping `LengthBound` active until `destination.length` or `this.length` is written, where `count <= capacity` immediately discharges `LengthBound` on the new values. While any invariant conjunct is lifted, early exits (`return`, `break`, `continue`, `?`), suspension (`await`), handler capture and whole-receiver method calls that require the closed invariant are refused; at the closing brace only the lifted conjuncts (`InitializedPrefix` and `VacantSuffix`) must be re-established. Within that scope, two-step bulk relocation over `Slots<T, capacity>` separates physical representation copying from logical ownership transfer: `CopyRepresentation` performs a capability-tag-preserving bulk copy of the `[0..count)` prefix into logically vacant destination slots (`Vacant<T>`), leaving the destination prefix vacant/unowned and recording a revision-bound representation-equality fact without arming destructors or duplicating linear ownership, and the erased proof operation `TransferType<T>` consumes that representation-equality fact together with the initialized source prefix and vacant destination prefix to transition `this.slots[0..count)` to vacant and `destination.slots[0..count)` to live initialized `T` in one capacity-independent range step.

The generic method above requires an element relocation law for `T`. Its
qualification checks preservation of the element invariant at the destination
and exclusion or discharge of all observations of the old address. An opaque
element without that law and a pinned element with a live address observer
must both be refused. The scalar prototype and the intended library interface
are specified in the [ownership library contract](../language/first-release.md#ownership-libraries).

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

`PublicationSlot` supplies runtime storage, and `PublishPermit` is a module-protected protocol resource tied to its stable identity. The caller writes `TryPublish(ref slot, move permit)` and matches the result; the retained runtime tag selects a case, whose erased evidence records the state it establishes. Both cases return a token, an exit obligation stronger than non-duplication that an affine logic's weakening rule does not supply. `Retry` restores the populated state; an operation that can partially publish needs a distinct recovery state and case. Pure snapshots are copyable, as in `let ghost Seq<byte> before = target.Model` where the current resource justifies the observation, but permission evidence cannot be duplicated or manufactured from an identifier. This sequential example claims no concurrency, eventual publication, crash recovery or device ordering. The lower-level split and restore mechanism stays inside the [resource-law explanation](../language/first-release.md#ownership-libraries), so ordinary clients cannot inspect a parent whose permission is suspended.

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

`Fn(byte) -> byte captures C` is a total shared-call function whose whole transitive capture set is `C`, carried in the type as [Scala 3's capture checker](#type-theory-and-elaboration-reuse) carries it. `Disjoint(output, C)` refuses a transform retaining a loan that overlaps the output, and a consuming closure or hidden mutable capture fails the `Fn` mode. `C` and the closure's type specialize, so no boxing or dynamic dispatch is implied, and the `in` loan keeps the captures alive for the call.

`@ NatExact(count)` is a use grade that the typing rules account for: the body uses `transform` exactly `count` times, a demand that depends on the stable ghost index, and a body using it a different number of times fails the allowance's equality. A use grade is not a trace claim. It supplies no per-call event law, termination or order, so the call count is the separate `CallCount` postcondition, which names the invocation role over the erased source trace rather than comparing function pointers; neither counts machine calls surviving inlining. `NatBound`, the same carrier admitted by `<=`, turns the exact grade into a bound, and in an idempotent presence domain `1 + 1 = 1`, so grade one there says nothing about cardinality. The contents postcondition supplies elementwise meaning, and neither it nor the grade proves the other's claim.

`ghost Nat count` has computation use zero and a type use the checker computes, so an author never writes [Gerty's](#reading-the-graded-type-claims) `(.0, .2)` binder annotation. Grade variables are ordinary generic parameters, `grade q : NatExact`, fixed along with representation at specialization, so no grade leaves open whether an argument occupies a register; an unspecialized representation needs its own proved strategy. Use counts, capability permissions and security labels are separate analyses with separate annotations, such as `effects calls(endpoint)` and `requires Public(index)`. An information-flow checker tracks control dependence as well as data dependence; a public return type alone excludes neither secret-dependent branches nor secret-dependent addresses.

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

Disposal ends the captured loan on `packet` before the handler returns, erases must-erase contents and eliminates any mandatory verdict by its named outcome; affine discard would do none of that. `Choose()` in the closure passed to `BestScore` performs through the capability its `effects(Choose)` type receives, which the handler inside `BestScore` binds; an operation the closure performs through a capability captured from its caller passes that handler without running its clause. `handle shallow` does not reinstall itself: its clause may resume `k` only inside a rehandle installing a handler of the same effect signature, whose return clause receives the raw body result. Nesting, forwarding and resumption counts are bounded at specialization, and a capture site either has reserved continuation capacity or a branch receiving `CapacityExhausted`. Handlers lower to explicit bounded control flow with no unwinding, under [the handler rules](../extensions/handlers-async.md#handler-lookup-capture-and-return).

#### Structured Tasks, Cancellation and Cells

This optional multi-shot/async research example is outside the first release. The later concrete service trial precedes it. The child below renders on the surface the combination [the composition review's client](../extensions/full-language-review.md#composed-client-and-inhabited-entry) composes: a packet with a runtime length, a multi-shot handler over a duplicable copy, and a cancellable commit to a shared counter under a unique allowance.

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

This example declares an empty task-failure set. `Forward` returns `Unit` under its declared cancellation/resource contract. `Serve` preserves the joined `TaskOutcome`: normal return is `Completed(Accepted(...))`, while accepted cancellation is `Cancelled` carrying the resource result constructed by `Accept`'s cleanup. The outer `Ok` does not unwrap that outcome or turn cancellation into normal task completion; it transfers the mandatory examination duty to `Serve`'s caller. The caller must explicitly handle the task outcome before using a returned packet.

Calling an async function constructs an owned dormant computation and runs none of it. Direct `await` consumes a dormant helper in the current task's bounded graph, without child registration; nested storage, cancellation and commit duties remain explicit. `spawn` separately binds a preassigned frame from the scope's declared pool, or returns the unchanged computation with a typed capacity verdict. A `spawn` reached after the scope's cancellation request registers its child already marked, so its first activation records `cancelled` without running its body, and `on cancel` spawns nothing. Every `await` is a checkpoint, even on a ready result, so a latched request is never skipped. A request accepted at a checkpoint before `commit` follows the nested helper's cleanup and cancels/joins any registered child before the enclosing cleanup, with each resource accounted once. `commit` performs the last checkpoint and then a bounded region with no suspension, capture or fallible step, whose single aligned AMOADD is the linearization point; a request arriving afterwards is answered `too_late`, and the operation completes normally. A client wait timeout stops only the wait and leaves the task with its scope, while a scoped timeout requests cancellation and joins within the declared bound. The task lowers to a bounded reaction graph with syntactic poll sites and no inner scheduler, under [the async rules](../extensions/handlers-async.md#frames-child-ownership-and-reaction-execution) and [the typed cancellation protocol](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-12-097).

`Packet<n>` keeps its represented length equal to the ghost index `n`, so the allowance and the addition agree. `AddOnce` is a unique protocol resource, not a grade, and it also names the counter's generation and the request. The conserved total of outstanding allowances proves the counter cannot overflow, and the addition publishes nothing else. The only multi-shot continuation, inside `BestScore`, retains `header` alone, while `packet` and `allowance` stay outside it. Capturing `allowance` inside the handled body would fail `Duplicable`, and releasing `frames` on a `Cancelled` acknowledgement rather than at the join would fail the scope's terminal-ownership rule.

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

**An independently implemented direct backend can remove the non-commercial licensing dependency on CompCert/SECOMP.** That benefits commercial builds, compiler redistribution and independent rebuilding, not just the licence on the emitted OS image. The [upstream licence reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#compcert-and-secomp) distinguishes the non-commercial compiler grant from its LGPL-licensed subset and separately negotiated commercial rights. A shipped image containing the compiler needs distribution rights for that compiler and its dependencies.

This benefit requires independently authored or suitably licensed compiler and proof sources. A new IR does not relicense copied or adapted backend passes; CompCert, SECOMP and Chamois reuse needs a selected-file and transitive-dependency audit. Clight itself has an LGPL option, so bypassing Clight is neither necessary nor sufficient to remove non-commercial terms. [Rocq's LGPL licence](https://github.com/rocq-prover/rocq/blob/V9.1.1/LICENSE) permits commercial use but retains redistribution obligations: removing non-commercial dependencies is not removing all copyleft obligations or all Inria-associated software.

**Whole-toolchain removal is a separate claim.** It also needs dispositions for the [retained compiler duties](#compiler-amendment-obligations), [Velus's separate non-commercial grant](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#vélus), and the [CertiRocq oracle's CompCert package dependency](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md). The oracle uses dual-licensed modules, but its package installs the full compiler. A whole-toolchain claim requires approved replacements for the affected duties and a matching dependency closure.

#### Mechanically Produced Evidence

A qualified frontend must produce a package of this form.

```text
SourcePackage(sourceClosure) = {
    coreProgram;
    elaboration : Elaborates(sourceClosure, coreProgram);
    typing : WellTyped(coreProgram);
    sourceMap : SourceLocations(sourceClosure, coreProgram)
}
```

The reviewed elaboration relation covers checked parsing or parse validation, binding and resolution, implicit insertion, overload/instance selection and desugaring. Source maps aid navigation; they are not correspondence proofs. Bind exact source, generated inputs and dependency/configuration identities to the derivations. MetaRocq can help construct and check terms but does not prove an external frontend merely by receiving its output. Typed holes remain outside accepted packages. Source, resolution and desugaring mutations must invalidate or refute correspondence even where a stale core theorem still checks.

Linking is a typed proof boundary. Generated required/provided contracts state calling convention, preserved registers, stack shape, memory/capability authority, relocations, callbacks and reentrancy, effects and observations. Discharge them through existing TAL judgments where applicable and CIC proofs for deeper composition, not new TAL grade axes or an on-device solver. Independently compiled verified-C, Rust and generated components must agree, and their composition must retain required robust properties. An unchecked linker assumption cannot replace that evidence. The compiler-side precedent for composing separately compiled modules is CompCertO's open-module refinement: [CompCertOC](https://pldi25.sigplan.org/details/pldi-2025-papers/27), PLDI 2025, carries threaded Kripke memory relations through 18 CompCert passes, horizontally and vertically composable, for cooperative threads sharing stacks. The selected HoldFast target's linkage and preservation work is priced in the [shared retained-route allowances](../../PLAN.md#shared-foundation-and-retained-route); this precedent supplies no inherited CHERI theorem or implied adoption of CompCertOC.

Optimization, typed linkage and final image validation extend the evidence
chain from the source package to the admitted image. The
[compiler route contract](compiler-route-contract.md#equivalent-artifact-endpoint)
requires both the retained route and any direct capability-IR route to prove
their image claims over the same pinned Sail term.

A promoted artifact's evidence package retains source and independent contract, elaborated program and correspondence, representation and ABI, functional/resource/observation proofs, solver certificates and actual transitive assumptions, optimization evidence, link contracts and composition, source/build/dependency/layout/byte identities, semantic pin and guarantee theorems, and measurements on those exact bytes. This organizes existing evidence rather than introducing a replacement admission format. A semantic dependency change reopens affected obligations even when displayed goal identities remain stable.

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
| Domain proof automation | The selected interpretation owns primitive laws. Consider Iris/MoSeL, Diaframe or Actris only where the component's obligations fit their rules and concrete machine subjects. |
| Representation transfer | [CoqEAL](https://github.com/rocq-community/coqeal) and [Trocq](https://github.com/rocq-community/trocq) are candidates after the package trial establishes a native Rocq transport baseline. Qualify the selected revision and assumption closure. [Comparison protocol](workflow-contract.md#representation-transfer-comparison) |
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

The proposal initially makes existing required guarantees easier to establish; it does not strengthen the platform merely by adding types or annotations.
A genuinely additional guarantee needs a stronger named contract and a proof over the implementation, followed by the required transport to bytes.
Target abstraction adds a useful enforcement boundary when tools reject missing semantic laws and unsupported security requirements.
It does not itself add hardware isolation: each accepted guarantee is conditional on the selected instance's proved interpretation and stated environment assumptions.

| Checked library property | Defects it can exclude within its semantics | What remains outside that result |
| --- | --- | --- |
| Initialization and bounds refinement | Reads of uninitialized cells, out-of-range accesses, incorrectly initialized output contents | Secret scrubbing, stale DMA access, and properties not preserved to the final artifact |
| Ownership plus borrow restoration | Conflicting mutation, use after the modeled loan ends, accidental changes to framed storage | Hardware capability revocation, unsafe/FFI primitives without proofs, general concurrent interference |
| Functional codec contract | Wrong interpretation, omitted validation required by the descriptor, inconsistent consumed length | A wrong descriptor, unspecified rejection policy, denial of service without termination/resource proofs |
| Indexed protocol refinement | Illegal modeled transitions, duplicated exclusive permission, lost ownership on specified failure paths | Global liveness, crash recovery, cancellation, or freshness unless those behaviors are included |
| Semantically interpreted usage budget | Excess modeled calls or events, or incorrect exact-use accounting | WCET, allocation volume, physical energy, or call ordering without their separate models/contracts |
| Information-flow proof with explicit observations | Prohibited modeled explicit and implicit flows | Final-artifact timing/leakage, physical side channels, and declassification rules not included in the proof |
| Subject binding and assumption auditing | Stale evidence and unaccepted assumptions when the existing checker enforces the bindings | Specification adequacy, a mismatched source interpretation, or compiler/hardware correctness by metadata alone |

For a single-use publication permission, for example, an ownership theorem can rule out publishing twice through the verified API.
Proving that publication eventually occurs also needs termination/progress and failure semantics; move-only syntax cannot establish it.
A grade that merely renames an existing permission contributes no stronger guarantee, although it may improve error locality.
Shared libraries also concentrate risk: a weak contract or wrong representation can affect every client, so independent contract review and negative specification tests remain essential even when the implementation theorem checks.
Audit generic laws for vacuous premises and instance representations for satisfiable entry states; a sound implication with an impossible precondition is not a usable component.
For deployment, the stronger VerifiedOS profile remains mandatory even if the same framework serves less demanding projects elsewhere.
