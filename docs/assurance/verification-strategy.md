# Vela verification strategy

The [first-release contract](../language/first-release.md) defines the supported
language and artifact boundary. This document covers how Vela's interpretation,
proofs and compilation fit that boundary. The
[VerifiedOS requirements register](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/requirements-register.md)
governs production obligations. [PLAN.md](../../PLAN.md) tracks implementation
and qualification.

## Language product contract

Vela combines explicit low-level operations and machine-checkable specifications.
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

The same semantic facts support batch diagnostics, editor navigation and
interchange. The [tooling contracts](../tooling/tooling-protocols.md) define
qualified subsets, result identities and independent-client checks.

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
The [Vela delivery plan](../../PLAN.md#vela-first-release-delivery) tracks the
composition of their evidence with Vela's source and artifact receipts.

## Research and semantic boundaries

### Research Landscape

This is a broad, decision-oriented survey of primary papers, project documentation, and implementation repositories, not a claim to enumerate every language or establish the absence of a newer preprint.
It emphasizes developments from 2024 onward, retaining earlier systems where they supply a missing part of the proposed design.
Links in each entry are its evidence; moving documentation describes the snapshot, not a pinned dependency or a reproduced benchmark.
A peer-reviewed theorem, a maintained tool, an archived artifact deposit and a pen-and-paper metatheory are different kinds of evidence, so an entry names the kind it read and never infers mechanization from a venue.
A licence is what the artifact's own licence file says, read at the milestone that would incorporate it and never inferred from an ecosystem, a sibling project or a forge badge; where an entry below records terms as unread, that is a statement about this survey and the reading belongs to the incorporation.
No surveyed toolchain is demonstrated by these sources to deliver the entire requested combination on VerifiedOS's CHERI target.
The project-fit columns assess that initial instance, not the general usefulness of these systems on other architectures.
Architecture independence is also distinct from prover independence: the proposed reusable framework still checks proofs in Rocq.

#### Rust and Low-Level Verification

| System | First-class verification and useful idea | Evidence boundary and project fit |
| --- | --- | --- |
| [Verus](https://verus-lang.github.io/verus/guide/) | Rust executable, specification, and proof modes; contracts, ghost state, inductive lemmas, and SMT automation. Strong reference for an integrated systems-programming workflow. | Its guide explicitly excludes verifying the verifier and Rust/LLVM compilers. A solver verdict is not a Rocq certificate. Borrow its UX and proof/library organization; do not equate source verification with certified bytes. |
| [VerusBelt](https://iris-project.org/pdfs/2026-pldi-verusbelt.pdf), PLDI 2026 | Semantic soundness in Iris/Rocq for a subset of Verus's proof-oriented types: cells, invariants, resource algebras and storage protocols, with full Rust lifetimes, concurrency and mutable borrows, licensing the type-check-then-spec-check discipline Verus performs with a solver. | It narrows the gap the Verus row names without closing it. The paper is explicit that Verus's front end, its verification-condition generation, its ghost-code erasure pass and its solvers stay trusted, and that standard-library specifications, decreases measures and invariant credits are outside the model. It is the grounding [the manual-proof path for HAL-adjacent `unsafe`](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-18-018) names, and that use reads it correctly: the grounding is of the type system's meaning, never of the tool's implementation. Its subject is a simplified modeled language. |
| [RefinedRust](https://plv.mpi-sws.org/refinedrust/) | Refined ownership types for safe and unsafe Rust, interpreted in Iris; generated proofs checked in Rocq. Particularly relevant to verified implementations behind safe APIs. | The foundational theorem concerns the embedded Rust model. Translation from actual Rust and subsequent compilation remain distinct boundaries. Best-aligned Rust proof infrastructure for the existing Radium anchor, not proof of all Rust or rustc. That project page carries the PLDI 2024 work only; its traits, closures and iterators extension is the separate OOPSLA 2026 paper, with a largely different author list. |
| [Corten](https://arxiv.org/abs/2609.04372) | A deep embedding of Rust's THIR in Rocq, with a weakest-precondition calculus and an interaction-tree denotation, ingesting Rust through hax and the authors' own extension; its case study proves memory safety of a buddy allocator's allocation and deallocation. | The fact that decides its disposition is that the paper names no repository, artifact deposit or code URL anywhere, so there is nothing to pin, inspect or licence and no reproduction is possible from it. It is also a plain September 2026 preprint whose template carries an unfilled venue line. The transpiler is unverified against rustc, the borrow checker is used as an untrusted oracle, and the memory model is single-threaded. It shares its name and nothing else with CortenMM, the Asterinas kernel's memory manager verified in Verus (Zhang et al., SOSP 2025), a different project with a different author list, prover and subject. |
| [Aeneas](https://github.com/AeneasVerif/aeneas) | Charon MIR/LLBC translation to functional definitions lets ordinary Rust programs be verified with functional reasoning. | The current README names Lean and HOL4 as its most mature backends, despite also providing Coq and F*. Unsafe and concurrency support are ongoing work. The [2024 symbolic borrow-checking result](https://arxiv.org/abs/2404.02680) is not a verified rustc backend. Its largest reported use, [SymCrypt's Rust cryptography](https://arxiv.org/abs/2609.15648) in a September 2026 preprint, verifies 16.7 KLOC of Rust through a 237 KLOC Lean development whose proofs agents largely wrote and the Lean kernel checks, with the Charon/Aeneas translation still trusted. That scale evidence is Lean-only, so pilot the actual Rocq subset before choosing it. |
| [hax](https://hax.cryspen.com/) and [hacspec lineage](https://hax.cryspen.com/publications/) | Rust-to-prover translation and specification-oriented Rust, especially for cryptography. The 2025 hax paper and protocol applications demonstrate multi-prover workflows. | The homepage names Lean, F*, and Rocq; current tutorials emphasize Lean and F*. A listed backend is not feature parity or proof of final machine code. Useful for executable specifications; Rocq integration needs an example-specific check. |
| [Creusot](https://github.com/creusot-rs/creusot) | Rust contracts and logical models, including reasoning about mutation; translates to Coma within Why3. | Active implementation, but its ordinary Why3/solver route is not a foundational Rocq proof of Rust lowering or compilation. An interactive prover backend alone does not validate the frontend. A useful donor for model views and post-borrow specifications. Its licence is LGPL-2.1, copyleft where the permissive terms of its neighbors here are not, which an incorporation reads before a reuse. |
| [RustHornBelt](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf), PLDI 2022 | The machine-checked foundation under that prophecy encoding: typing judgments carrying first-order specifications built with parametric prophecy variables, proved sound in Rocq over lambda-Rust, with proofs for Vec, IterMut, Cell and Mutex. | It verifies no Rust verification tool. The subject is lambda-Rust, not rustc, not surface Rust and not Creusot's actual translation, and the development's own notes record standard-library APIs still unverified. What transfers is that the borrow-end encoding is a sound proof principle, which is the claim the restoration contracts here rest on. |
| [Flux](https://github.com/flux-rs/flux) | Refinement types integrated into Rust; lightweight value invariants can make bounds and API constraints part of signatures. | A practical refinement-checking candidate, not a general dependent proof assistant or established Rocq-to-binary chain. Borrow predictable inference and concise refinement diagnostics, while measuring the supported fragment. Its soundness theorem is about a core calculus and is conditional on the Stacked Borrows discipline, which is itself a proposed rather than normative aliasing model. [FLEX](https://arxiv.org/abs/2607.12226), a July 2026 preprint from the same group, reimplements the constraint solving as Lean tactics producing kernel-checked proofs for 95.7% of Flux's benchmark constraints; generating those constraints from Rust stays trusted and the kernel is Lean's, so it demonstrates the certificate-producing shape the [refinement tier](#layered-proof-and-staging) needs rather than a route to Rocq. |
| [Thrust](https://www.riec.tohoku.ac.jp/~unno/papers/pldi2025.pdf), PLDI 2025 | Prophecy-based refinement types whose loop and recursion invariants are inferred by reducing refinement inference to constrained Horn clauses, so mutable borrows receive first-order specifications without aliasing reasoning. | Nothing is machine-checked: the CHC and SMT solvers are trusted oracles, as is the translation from Rust, and the reported results are benchmark outcomes. Its repository is effectively unlicensed, promising a dual grant in a README while shipping neither licence file; only the artifact deposit states MIT, over a container that also bundles MPL-2.0 components. Inference is the transferable part, and an inferred bound is a proposal for Rocq to prove. |
| [Ante](https://antelang.org/blog/safe_cyclic_mutability/), 19 October 2026 design | Places, unstable places and mutation effects permit local shared mutation while tracking reference invalidation. | Candidate for [Vela's static invalidation analysis](../extensions/interior-mutability.md#ante-as-a-candidate-for-static-invalidation), not a Rocq soundness or final-code theorem. The [producer disposition](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#ante-place-sensitive-mutation-and-invalidation) is deferred; no rule or compiler is selected. |
| [Evergreen](https://evergreenlang.net/) and [repository](https://github.com/jordan-bonecutter/evergreen) | A proof-oriented systems language with a plane-tree memory/revision model, vacant-slot storage (`T \| shape(T)`), named invariant conjuncts with selective lifting (`update(self) lifts ...`), two-step bulk relocation (`copy_representation` then `transfer_type`), and early shared-reference reservation (`starts_owner`). Its repository includes Lean 4 mechanizations of a 3-state reference-counting conservation invariant (`SharedOwnership.lean`) and an affine-linear arithmetic certificate checker (`Tier1Cert.lean`). | Its Rust frontend and semantic checker (`crates/evg-Semantic`), plane-tree ownership/lifetime rules, and verification-condition generator are unverified, and the Lean 4 proofs cover isolated sub-models rather than the language, compiler or target machine code. Its repository carries no root licence file (only a web-font licence under `web/public/fonts/UFL.txt`), so no code is incorporated. Its unspecified-value integer overflow semantics violates [R-05-144](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-144), its general untagged raw unions `A \| B` cannot preserve CHERI capability tags across arbitrary mixed layouts, and its whole-continuation branch replay with hidden runtime drop flags conflicts with structured control-flow joins. Candidate donor for Vela's named `invariant Clause: ...` conjuncts with selective `open (...) lifts ...` lifting, two-step `CopyRepresentation`/`TransferType` bulk relocation over vacant slots, and the capacity-invariance qualification gate; the [producer disposition](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#evergreen-plane-tree-verification-selective-invariant-lifting-and-two-step-bulk-relocation) declines it as a producer or semantic anchor. |
| [Tree Borrows](https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf), PLDI 2025 | An aliasing model for Rust mechanized in Rocq inside Simuliris, with intraprocedural optimizations proved sound against it, retaining most Stacked Borrows optimizations and enabling read-read reordering. | Not a normative Rust semantics, and neither rustc, LLVM nor the separately written Miri implementation is proved to correspond to the Rocq model. Its headline acceptance figure over published crates is a measurement rather than a theorem. It bounds what an aliasing discipline may assume; it supplies no capability provenance rule for this target. |
| [Prusti](https://github.com/viperproject/prusti-dev) | Contract-annotated Rust through Viper, with panic/overflow checking and an editor workflow. | A useful established comparator, not assumed to track current Rust: the inspected repository retains an older pinned nightly. Viper verification does not itself produce the project's admitted proof evidence. |
| [Kani](https://github.com/model-checking/kani) | Bit-precise model checking, proof harnesses, nondeterministic inputs, and checks for unsafe-code defects. | Excellent complementary counterexample search. Results depend on harness assumptions, supported operations, and sufficient unwinding. [Its function and loop contracts, quantifiers and stubbing](https://arxiv.org/abs/2607.01504), an ASE 2026 industry paper, extend a harness from bounded to unbounded verification and run over 16,000 harnesses per change in the standard-library campaign; an unbounded result is still a CBMC verdict over an unverified MIR translation, not a Rocq certificate. |
| [Verifying the Rust Standard Library](https://arxiv.org/abs/2606.17374), NFM 2026 | A crowdsourced campaign running Kani, Flux, VeriFast, ESBMC and KMIR in continuous integration against challenges on the standard library's `unsafe` code, targeting undefined behavior such as out-of-bounds, dangling and uninitialized accesses. | Evidence about the library under safe Rust rather than about one application, which is where a certificate for safe code still rests on unverified `unsafe`. Its verdicts come from solvers and model checkers with their own frontends, none produces a Rocq proof, and each challenge covers named functions, not the library. Read it as a map of what those tools can establish, not an admitted input. |
| [RefinedC](https://plv.mpi-sws.org/refinedc/) | C ownership/refinement annotations and predictable Lithium automation with foundational Iris/Rocq proofs. | Strong proof-engineering precedent, but its C model is not interchangeable with CHERI-C. Reuse reasoning patterns or proved transport, not a second authoritative memory semantics. |
| [CN](https://doi.org/10.1145/3571194), [VST-A](https://doi.org/10.1145/3632911), and [Iris for CompCert C](https://doi.org/10.1145/3632848) | Respectively separation-logic refinement types for systems C, foundational annotation verification, and integration of CompCert C reasoning with Iris. | Distinct routes, not one toolchain: CN's Cerberus/solver boundary differs from VST-A's Coq proof construction. The CompCert/Iris work is the closest semantic fit for the C path; none establishes the project's CHERI port merely by using C. |
| [C*](https://arxiv.org/abs/2504.02246) | Programmable proofs and symbolic states in the same C development surface. | An important 2025 language-design experiment; the detailed assessment below separates its prototype from its intended interaction model. |

For existing Rust components, evaluate RefinedRust first when foundational ownership reasoning is decisive, and Aeneas when the actual supported safe fragment makes functional translation simpler.
Verus is a strong ergonomics comparator, not a drop-in replacement for the repository's proof authority.
RustBelt supplies semantic foundations for Rust safety; it is not itself a push-button functional verifier for arbitrary crates.
RustHornBelt and VerusBelt extend that lineage, the first to functional specifications of safe APIs implemented with unsafe code, the second to the proof-oriented types a verification tool adds; each proves a model sound, and neither proves a verifier correct.

#### What the Rust Verifiers Contribute

**Verus: proof resources need ownership too.** Its [variable modes](https://verus-lang.github.io/verus/guide/reference-var-modes.html) separate runtime values from `ghost` mathematical values and `tracked` proof resources.
Both ghost and tracked data are erased, but tracked resources retain ownership discipline during verification.
This is a better design reference than treating every erased value as freely duplicable: an immutable sequence snapshot may be copied in reasoning, while permission to mutate a cell must not be duplicated.
Its [interior-mutability libraries](https://verus-lang.github.io/verus/guide/interior_mutability.html) distinguish a cell's identity from its changing contents; an invariant-based cell can expose a predicate on every observed value without promising an immutable snapshot of shared mutable storage.
For `VerifiedComponents`, borrow this separation in the library interface, with resource ownership interpreted in the chosen separation logic, not a new trusted Rust-like checker.

Verus's `spec`/`proof`/`exec` function modes are not merely comments: they separate mathematical computation, reasoning, and deployed execution.
Contracts plus small lemma calls are the everyday surface; quantified reasoning still needs attention to triggers, unfolding, and solver behavior.
Its [assumptions guide](https://verus-lang.github.io/verus/guide/tcb.html) explicitly names `assume`, external proof bodies, and external executable specifications as ways to introduce assumptions.
The proposed equivalent is an inspectable transitive assumptions report, with no silent conversion of an external-body contract into an accepted component theorem.
Ergonomics and mature examples make Verus a serious comparator, but translating arbitrary Verus verification conditions into Rocq would be a separate verification project, not a library wrapper.

**Creusot: specify the end of a borrow.** The current [guide](https://guide.creusot.rs/) describes Rust-to-Coma translation followed by Why3find proof search.
Its [architecture](https://github.com/creusot-rs/creusot/blob/master/ARCHITECTURE.md) explains the RustHorn-inspired representation of a mutable borrow through its current and final values, using a prophecy resolved when the borrow ends.
Pearlite's `*` and `^` notation exposes those values; pure logical values are not subject to the runtime ownership checker.
This makes a container operation returning a mutable element reference specifiable without exposing the whole heap: say what the element initially contains and how its eventual value determines the restored container.
Borrow-end specifications, model views, and a reusable specified standard library are the transferable ideas; adopting Coma or trusting its solver encoding is not required to reproduce that API discipline in Rocq.

**Prusti: make restoration obligations visible at the call site.** Its [pledges](https://viperproject.github.io/prusti-dev/user-guide/verify/pledge.html), including `after_expiry` and `before_expiry`, express what holds after a returned mutable reference expires.
The vector example preserves length, replaces the selected element with the final borrowed value, and preserves the other elements.
That example's wrappers are marked `trusted`: it demonstrates useful contract vocabulary, not foundational verification of those wrappers.
The [verification guide](https://viperproject.github.io/prusti-dev/user-guide/verify/summary.html) also explicitly limits its general guarantee to partial correctness; a terminating result satisfies the contract, but termination is not thereby established.
For this project, implement the restoration lemma itself and discharge termination separately where required.

The practical choice is therefore not a contest between interchangeable Rust verifiers.
Use Verus to evaluate proof authoring and erased permissions, Creusot and Prusti to evaluate borrow contracts, and RefinedRust for a foundational ownership route already aligned with the architecture.
A verifier's convenient annotation syntax does not remove the cost of specifying a primitive, proving its implementation, or connecting its source model to the deployed artifact.

#### Dependent Types, Effects, and Ergonomics

| System | Contribution to the ideal language | Boundary to retain |
| --- | --- | --- |
| [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html) | Full dependent programming, type-directed holes, resource protocols, and explicit erased/linear/reusable arguments through quantitative type theory. | Its compiler and totality implementation are not the Rocq kernel. Its default Scheme and alternative reference-counted C backends do not imply a GC-free, allocation-free, CHERI-verified runtime. |
| [F*, Low*, and Pulse](https://fstar-lang.org/) | Dependent types, indexed effects, ghost computation, SMT/tactics, and low-level programming. Pulse adds an imperative separation-logic surface; [PulseCore](https://fstar-lang.org/papers/pulsecore-indirection-2025.pdf) is a PLDI 2025 foundational result. | The logic is F*, not CIC. Foundational PulseCore does not make every F* verification or extraction step Rocq-checkable. [Pulse is now integrated into F*](https://github.com/FStarLang/pulse); treating the old separate repository as the current tool would misjudge maturity. |
| [Lean 4: mvcgen](https://lean-lang.org/doc/reference/4.34.0/The--mvcgen--tactic/) and [grind](https://lean-lang.org/doc/reference/4.34.0/The--grind--tactic/) | Dependent executable programming with monadic verification-condition generation and proof-producing, SMT-style automation in the same environment. A particularly relevant current convergence of programming and proving. Since [4.33.0](https://lean-lang.org/doc/reference/4.34.0/releases/v4.33.0/) its experimental reimplementation, `vcgen`, carries a resource across a call once its program type registers a frame, and [4.34.0](https://lean-lang.org/doc/reference/4.34.0/releases/v4.34.0/) adds in-code `requires`/`ensures` contracts and loop invariants whose specification theorems `vcgen` proves, the contract-in-code surface [the expected developer experience](#expected-developer-experience) describes. | Ordinary Lean proof terms are checked by Lean, not Rocq. Native compilation and runtime behavior are separate from proving a Lean function's theorem. Borrow the interaction and automation architecture, not a second admission kernel. Both pages are cited at the version path of the 4.34.0 manual, whose release notes are dated 14 September 2026, because the `/latest/` path follows the release train and changes under a citation. mvcgen's own discharge is limited to local assumptions, conjunction splitting and, as configured, the `mvcgen_trivial` and `mleave` tactics, leaving every other condition a goal, and grind's documentation bounds it away from explosive combinatorial search, so neither is general solver-strength automation. The contracts belong to an internal `Std.Internal.Do` notation. [Their merge request](https://github.com/leanprover/lean4/pull/14389) covered `for` loops over lists and ranges and excluded `while` loops and residual-condition discharge, and [#14596](https://github.com/leanprover/lean4/pull/14596), in the same release, extends `for … invariant` to every container whose iteration produces its elements without effects. |
| [Dafny](https://dafny.org/) | Readable contracts, ghost methods, calculational proofs, datatype patterns, and a mature language-server experience. Closest direct syntax/interaction comparator to the requested C# ergonomics. | Distinguish ordinary Dafny's solver/compiler pipeline from the [CPP 2026 verified subset through CakeML](#closest-matches-to-the-complete-workflow), which proves substantially more of the verification/compilation chain in HOL4. Neither supplies this project's Rocq/purecap backend or runtime discipline. |
| [SPARK](https://www.adacore.com/about-spark) | Language-level contracts, explicit data flow, proof of runtime-error freedom, and ownership for pointers in an industrial systems setting. | Serious practical comparator, but Ada/GNAT and its proof tooling are not the chosen Rocq/CHERI path. Source-level proof and tool qualification do not establish the final artifact theorem. |
| [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/) | Refinements and equational proofs expressed as code; useful models for lightweight contracts and reflection. | Haskell's runtime and the solver/compiler trust chain do not satisfy this target merely because the types are precise. |
| [Granule](https://github.com/granule-project/granule) and [Gerty](https://github.com/granule-project/gerty) | Graded, linear, and dependent types for resource use, effects, and permissions. The project lists 2024 fractional-uniqueness work and the ICFP 2026 result relating graded-base and linear-base designs. | Research foundations, not an off-the-shelf systems compiler, and each discharges its grade constraints through an SMT solver that is a trusted oracle in both. General grades belong in source proofs until justified by an existing admission obligation; they do not authorize new TAL grade axes. They are also two repositories with two licences: Granule is BSD 3-Clause, while Gerty carries its own dual file whose MIT half covers parser and syntax files derived from Agda, and the project site states no licence at all. |

Agda and ATS are useful background precedents for dependent programming and, in ATS, erasing proofs while retaining low-level code.
Stainless/Scala and the Spec#/Dafny lineage are additional contract-and-ergonomics comparators.
They are not evaluated here as current deployment candidates; their present backend coverage and integration costs remain unassessed.
Likewise, an effect system such as Koka's or a linear extension to Haskell addresses resource/effect structure, not by itself functional correctness against a specification.

Koka's relevance extends beyond effects: its [fully in-place programming work](#embedded-verification-and-certified-synthesis) supplies a resource-disciplined functional fragment, while AddressC supplies an implemented imperative proof surface. Those are separate contributions and neither requires adopting Koka's runtime.

The most directly relevant recent advances are therefore not a single new universal language: they are foundational Rust verification, live proof-state interaction, imperative dependent verification in Pulse and Lean, and more trustworthy extraction in Rocq.
AI proof synthesis can help in all these workflows, but contributes candidate programs, contracts, and proof scripts only. A generated contract still needs independent review and a generated proof still needs kernel checking. Kernel checking is necessary but not sufficient against search that optimizes for a passing verdict: in 2026 a model shared credit for [a guard-checker defect](https://github.com/rocq-prover/rocq/issues/22382) through which Rocq's kernel and `rocqchk` accept `False` in the reported 9.2.0 release, and in [an agent run on a Rocq benchmark](https://arxiv.org/abs/2603.20405) 14 proofs used `Admitted` and 6 redefined types to bypass the theorem statement, all compiling without error. [The portable proof workflow's acceptance boundary](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-assistance.md#acceptance-boundary) therefore also requires the preserved statement and the exact assumption audit, and [the prover lock's record](https://github.com/symbiogenesis/VerifiedOS/blob/main/tools/opam/README.md) names the kernel inconsistencies the locked version still carries.

#### Effect Handlers, Sharing and Protocol Logics

The handler, sharing and protocol rules the full-language design proposes have mechanized upstream logics, each about its own modeled language. They supply proof rules and the counterexamples that motivated them. [The elaboration comparison](#type-theory-and-elaboration-reuse) retains the type-and-effect sources beside them, and the [handler](../extensions/handlers-async.md) and [mutability](../extensions/interior-mutability.md) dossiers own what the proposed rules must establish locally.

| System | Mechanized contribution | Boundary to retain |
| --- | --- | --- |
| [A Relational Separation Logic for Effect Handlers](https://iris-project.org/pdfs/2026-popl-blaze.pdf), POPL 2026 | Relates two programs with handlers without requiring their effects and handlers to correspond, adding relational bind, frame and concurrency rules, and relating effect-based asynchronous library implementations to genuinely concurrent ones. Soundness is mechanized in Rocq on Iris. | Its subject is an Iris-modeled language with handlers, not OCaml, Links or any implementation, and each equivalence is hand-written per case study rather than decided by a checker. Its Rocq development is LGPL-3.0, a copyleft obligation the permissive entries beside it do not carry. |
| [Iris-WasmFX](https://iris-project.org/pdfs/2026-pldi-iriswasmfx.pdf), PLDI 2026 | Type soundness for typed continuations mechanized over WasmCert, and an Iris program logic and logical relation above it verifying a coroutine library and a generator modularly. The closest mechanized account of stack switching as an explicitly represented resource. | The Wasm extension it tracks is a proposal under revision, not a ratified feature; no engine is proved to implement the semantics and no compiler into it is verified. Its continuations live in a store, not in the preassigned immovable frames this profile requires. |
| [Formal Semantics and Program Logics for a Fragment of OCaml](https://iris-project.org/pdfs/2025-icfp-osiris.pdf), ICFP 2025 | A Rocq semantics for OLang, a sequential OCaml fragment with references, exceptions and deep and shallow handlers, written as a monadic interpreter over a custom monad of operation trees, with Horus, a Hoare logic for pure fragments, and Osiris, an Iris separation logic for arbitrary programs, both proved sound against it. The authors describe Osiris as the first program logic for OCaml's combination of exceptions and handlers; it is the handler logic here nearest a shipping language. | Its translator from the OCaml type checker's typed tree into OLang "is simple, and must be trusted", and the semantics is tested on about 900 lines of tests rather than shown to agree with any compiler; concurrency, weak memory and functors are future work. Continuations are one-shot, following de Vilhena and Pottier's observation that forbidding multi-shot continuations keeps the frame rule valid everywhere, so the multiple-resumption case [the handler commitments](#general-handlers-with-resource-safe-resumptions) admit has no counterpart in it. The development's host refused access during this survey, so its licence is unread. |
| [Leaf](https://doi.org/10.1145/3622798), OOPSLA 2023 | A guarding operator making one proposition a shared version of another, with its rules proved sound inside Iris/Rocq and used for a reader-writer lock and a hash table above it. It is the temporary-sharing half of the combination VerusBelt proves. | A proof library over a HeapLang-style model: no machine code, compiler, allocator or OS claim. Its own repository states that the published artifact is superseded by a simplified core, so the paper text and the current tree do not correspond line for line. The [arXiv item](https://arxiv.org/abs/2309.04851) is that paper's extended version and not the publication of record. |
| [Iron](https://iris-project.org/pdfs/2019-popl-iron-final.pdf), POPL 2019 | Fractional resource accounting in a higher-order concurrent separation logic whose adequacy statement is that a verified program accounts for its resources rather than leaking them, including examples delegating reclamation to a forked thread. The closest precedent for disposal as a proof obligation. | The result is about the logic's model and a HeapLang-style semantics, not a real allocator or an OS, and it infers nothing: it is a discipline for discharging obligations the author states. Its development's licence could not be read during this survey, so its terms are unread and an incorporation opens that file first. |
| [Nextgen](https://iris-project.org/pdfs/2025-cpp-nextgen.pdf), CPP 2025 | A modality for non-frame-preserving ghost-state updates across generations, used to build a separation logic for a language with explicit stack allocation whose return clears whole frames. Generation change is the shape revocation and incarnation reuse take here. | The stack-allocation result is about the paper's own language, not C, Rust or this platform's frames, and nothing is established about a compiler or machine code. Its upstream tree states no terms at all; only an archived snapshot carries a licence, and a content licence on a deposit is not a grant to use the development. |
| [Mixtris](https://iris-project.org/pdfs/2026-oopsla-mixtris.pdf), OOPSLA 2026 | Higher-order separation logic for mixed-choice multiparty message passing mechanized in Rocq/Iris, extending the Actris lineage already deferred in the tooling map to protocols offering non-deterministic choice among concurrent sends and receives. | Partial correctness in its own model language. Leader election is verified as functional correctness and not as liveness, so no termination, progress or deadlock freedom follows, and nothing addresses real distributed execution, failures or compiled code. Its artifact is an archived deposit under a content licence with no maintained repository, so it is a frozen snapshot rather than an upstream to track. |

Each is a theorem about another modeled language with its own trusted base and its own prover edition, so what a reading takes is the rule and its side conditions. None supplies this platform's frames, cells, capabilities or memory model, two of them grant no usable terms at all, and citing one closes no obligation in the dossiers that consume these shapes.

#### Compilation and Executable Models

| System | What it establishes or enables | Consequence for this project |
| --- | --- | --- |
| [Live Verification in an Interactive Proof Assistant](https://doi.org/10.1145/3656439), PLDI 2024 | Incremental construction of low-level programs and their proofs inside Coq, with symbolic state at the cursor. | Closest precedent for the proposed Rocq-library-first UX. Reproducing the interaction is smaller than designing a new language and runtime. |
| [Rupicola](https://github.com/mit-plv/rupicola) and [Bedrock2](https://github.com/mit-plv/bedrock2) | Relational compilation from functional descriptions to imperative code, plus a low-level verified compiler and end-to-end examples. | Directly useful construction techniques, and the one row here this repository has already measured rather than surveyed: M1.6 stood the stack up whole and found its verified exit emitting base-integer RISC-V with no capability instruction anywhere, which is the non-capability compilation target [purecap-only](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-18-002) forbids, while the C-printer exit that does reach a usable target carries no theorem at all. Reuse the construction technique and treat the target as unbuilt; the planned Clight transport needs its own demonstrated connection. |
| [MetaRocq](https://metarocq.github.io/) | Quotation, verified type checking, and erasure; its bibliography includes verified extraction to OCaml/Malfunction in 2024 and the consolidated typechecking/erasure account in 2025. | Useful metaprogramming and proof infrastructure. Erasure is not native compilation; the documented safe checker also states a strong-normalization assumption. Inspect each theorem's assumptions rather than inferring them from the project name. Since [1.5.1](https://github.com/MetaRocq/metarocq/releases/tag/v1.5.1-9.1) the erasure pipeline also offers a phase its release notes call unsafe and unverified, remapping inductive types and their matches to arbitrary constants such as GMP-backed integers for `nat`, so a verified-erasure claim names the phases its run used. That release's [Rocq 9.2 variant](https://github.com/MetaRocq/metarocq/releases/tag/v1.5.1-9.2) of 16 June 2026 declares, in its [opam files](https://github.com/MetaRocq/metarocq/blob/v1.5.1-9.2/rocq-metarocq-utils.opam), a `rocq-core` range of `>= 9.2~ & < 9.3~` excluding the current [proof snapshot](../../tools/opam/rocq.lock); no local build is claimed. |
| [CertiRocq, formerly CertiCoq](https://github.com/CertiRocq/certirocq) | Gallina compilation to Clight and WebAssembly. | The current README says large parts are verified and others remain in progress. General Gallina compilation includes representation/runtime issues; it is not an automatic static-memory CHERI backend. Monitor or use for host tools, not the first on-device route. |
| [Plinth/Plutus layered certification](https://webspace.science.uu.nl/~swier004/publications/2025-funarch.pdf), FUNARCH 2025 | Compilation traces connect independently implemented passes to Rocq translation relations, decision procedures and preservation proofs. | Design reference for [staged compiler evidence](../extensions/unified-source-contract.md#optimization-stages-and-evidence). The paper proves semantic relations for dead-code elimination and nonrecursive-let compilation; other assurance levels check translation relations without semantic-preservation proofs or leave steps unchecked. Those levels cannot satisfy Vela's complete preservation duties, and the demonstrated validator equivalence supplies no CHERI, leakage, resource or final-byte theorem. No backend is selected or imported. |
| [Peregrine](https://types2026.cse.chalmers.se/abstracts/61.pdf), TYPES 2026 | A standalone middle-end on Rocq's extraction intermediate language, adapting the existing verified pipeline, adding verified deserialization of that intermediate from a textual form, and contributing a formal Rocq specification of a large subset of CakeML. | A four-page contributed abstract, so a conference-branded preprint whose post-proceedings status cannot be established. Its own figure draws the new frontends and the CakeML backend as unverified, the CakeML specification is offered as something that may later verify that backend, and the middle-end is itself extracted through the legacy unverified extractor, so the running tool is not bootstrapped through a verified pipeline. Its organization's repositories are not uniformly licensed and one frontend carries no licence file at all. |
| [CakeML](https://cakeml.org/) and [Pancake](https://cakeml.org/pancake.html) | CakeML demonstrates proof-producing translation and compilation to machine code. Pancake pursues explicit-memory systems programming using lower compiler layers without a GC. | Closest architectural evidence that the executable-reference goal is feasible. Their HOL foundation and target models are different; adopting them would not be a small Rocq library change. |
| [Cogent](https://github.com/au-ts/cogent), with [Dargent](https://people.eng.unimelb.edu.au/rizkallahc/publications/dargent.pdf), POPL 2023 | Systems-oriented code/proof co-generation and refinement to C, with Isabelle proofs and file-system case studies. Dargent adds a declarative bit-level layout language whose generated getters and setters ship with generated Isabelle proofs that they realize the declared layout, so the refinement chain survives a custom representation instead of ending at hand-written marshalling. | The closest published result to this document's own promise of high-level specifications with representation control, and the one to read before designing representation glue. The compiler is not verified: each compilation carries its own certificate, so a defect is a failed proof for that program rather than an excluded class. Isabelle, the C parser, AutoCorres and the C compiler are trusted, bit-field semantics are simulated rather than modeled, hand-written foreign C is outside the certificate, and there is no concurrency. The tree has no single licence: it is per-file BSD 2-Clause or GPLv2 by tag, with the compiler itself GPLv2, which is a copyleft obligation for a downstream that vendors rather than reads it. |
| [Jasmin](https://jasmin-lang.readthedocs.io/en/latest/) | Executable formal semantics, precise low-level control, and a Rocq-verified compiler to assembly for cryptographic code. | Distinguish compiler correctness from its trusted safety analyzer and EasyCrypt proof route. Its result is not automatically a proof about linked CHERI bytes or the project's leakage model. Borrow explicit representation and instruction-level accountability. |
| [Verifying Peephole Rewriting in SSA Compiler IRs](https://doi.org/10.4230/LIPIcs.ITP.2024.9), ITP 2024 | A Lean mechanization of a core calculus for SSA IRs, generic over the IR and covering the nested-region scoping MLIR uses, whose central theorem is that applying an already-proved peephole rewrite at a program point preserves the program's denotational semantics. | Evidence that a rewrite family can be proved once and applied many times, which is the shape a validated optimization interface wants. Neither MLIR nor LLVM is verified: the dialect semantics are the authors' own formalization, nothing connects it to the C++ implementation or to the language reference, and each rewrite still needs its own proof. As an admission route it fails [the translator conditions](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020) at the first, checking in Lean rather than Rocq and retiring no interim here. |
| [CHERIoT Rust](https://github.com/CHERIoT-Platform/cheri-rust/tree/ba6e0e6c9c40593f7b47d5af071a6ccb9d154cf6) | Experimental capability-aware rustc/LLVM fork compiling CHERIoT programs, `compiler-builtins`, `core` and `alloc`. | Selected functional starting point for the mandatory Rust producer, replacing fresh CHERI plumbing. The [source reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-reuse/languages.md#cheriot-rust-selected-functional-capability-aware-compiler-baseline) fixes its RV32E/address-space/ABI differences, unimplemented compartment/device interfaces, separate dependency rights and certification gap. Adapt to the frozen RV64 profile; retain the MIR, CHERI-TAL, resource and final-byte duties. |
| [RustCompCert](https://arxiv.org/abs/2602.07455) | A Rust front end layered on CompCertO that lowers to Clight and reuses the existing backend, with Rocq proofs aimed at semantics preservation and at treating borrow checking as verifying compilation. | Self-described ongoing work in a February 2026 preprint: no end-to-end theorem is claimed finished, no artifact evaluation or review has occurred, and the scope is a sequential subset with no concurrency and no unsafe code. It builds a front end above CompCert rather than compiling Rust to it. Decisively for any incorporation, the fork inherits CompCert's non-commercial terms rather than an open-source licence. |

F*/Low* with KaRaMeL, HACL*, Vale, and EverParse provide particularly strong evidence that high-level verified descriptions can yield useful high-performance native components.
Their production use supports feasibility, not equivalence between their trust assumptions and this repository's.
The comparison is about theorem endpoints and runtime obligations, not whether a project uses the word "verified."

#### Closest Matches to the Complete Workflow

Several systems already combine executable models, implementation construction and foundational proofs; some also connect them to machine execution. The useful comparison is the supported component and the theorem's subject, rather than a score for how many language features a project lists. The following assessments are readings of upstream results, not locally reproduced integrations.

**DeepSEA: the closest systems-language precedent.** The [OOPSLA 2019 systems paper](https://flint.cs.yale.edu/certikos/publications/deepsea19.pdf) integrates imperative implementations, pure Coq views, explicit data representation and certified abstraction layers. It generates representation relations and proofs connecting functional views to Clight, then uses CompCertX for compilation to assembly. Its examples include SHA-256 and part of CertiKOS's memory manager. This directly addresses the repeated specification/implementation/refinement work motivating `VerifiedComponents`, with an implemented language rather than proposed notation.

The restrictions matter: objects are statically allocated, loops have selected forms, and the source type system is deliberately simple. Rich correctness properties are proved in Coq; a generated functional view describes the program and still needs an independently chosen correctness theorem. Bottom-layer primitive specifications have separate implementation obligations. Neither the demonstrated representation nor its assembly endpoint is the selected CHERI/Sail instance. Read its representation generator and layered composition before designing equivalents; reproducing its entire compiler would be separately scoped work.

Reading it is the only option its terms allow. The public implementation is a descendant of the paper's compiler rather than a frozen paper artifact, and it carries no licence of its own: the sole licence text in that tree is CompCert's, so its README restricts use to educational, research, personal or evaluation purposes. That is not free software, and it cannot be vendored into a tree whose [commercial rebuildability](#licensing-and-commercial-rebuildability) is a stated deliverable. A design reading of its generator is unaffected.

DeepSEA's [2024 smart-contract work](https://arxiv.org/html/2405.08348v1) develops a different backend, through MiniC to an EVM formalization, with gas-sensitive simulation. This reaches further on that target, but it is not an update establishing a CHERI systems backend. The paper explicitly assumes injectivity of concrete Keccak hashes at the final connection, which is false as an unrestricted mathematical statement; its eWasm route lacks a correctness proof. Those assumptions cannot enter this project's component theorem. Keep the systems and EVM editions distinct when selecting an artifact, and audit the exact source-to-generated-view subject as well as the generated proof.

**Sepref and Isabelle-LLVM: much of the proposed library already has an analogue.** [Generating Verified LLVM from Isabelle/HOL](https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.22/LIPIcs.ITP.2019.22.pdf) combines abstract functional algorithms, concrete imperative data structures, separation logic and automated refinement to a shallow embedding of an LLVM fragment. This is a close comparator for `Models`, `Representation` and `Build`, with generated code and checked refinement rather than annotations alone. Its trusted boundary includes the shallow embedding's interpretation as LLVM, code generation and subsequent LLVM compilation; its model also assumes an unbounded supply of memory. Verification of the embedded fragment is not a theorem about all LLVM optimizations, allocation failure or final bytes.

The [parallel-refinement development](https://www21.in.tum.de/~lammich/isabelle_llvm/) goes beyond the initial sequential pilot: it exposes generic separation-logic rules parameterized over a memory model, array implementations of scoped splitting/index combinators, and verified sorting algorithms. Compare those combinators with the proposed scoped borrow-restoration interface. Reusing their design is immediately possible; transferring their Isabelle/HOL proofs, concurrency model and LLVM memory interpretation into the admitted Rocq/CHERI chain is separate work. They demonstrate that this library architecture is practical, without establishing its local instance or a portable timing guarantee.

**Verified Dafny through CakeML: familiar contracts with a foundational compiler path.** [Verified VCG and Verified Compiler for Dafny](https://arxiv.org/abs/2512.05262), CPP 2026, formalizes an imperative subset with arrays, loops and mutually recursive methods in HOL4. It proves a verification-condition generator and compilation to CakeML, whose verified backend supplies the machine-code path. This is a stronger comparator than ordinary Dafny verification followed by an unverified native compiler.

The [paper's composed example and boundary](https://research.chalmers.se/publication/550353/file/550353_Fulltext.pdf) are precise: the McCarthy 91 example combines proof of the generated verification condition with the verified rules and compiler. Source parsing/elaboration begins with an untrusted Dafny frontend exporting an S-expression, so source correspondence still needs attention. The formal subset does not cover all Dafny, and its CakeML references, arrays and exceptions do not establish the static-memory runtime required here. Compare its separation of frontend, VCG, discharged conditions and compiler theorem when specifying evidence packages. Its [published mechanization](https://github.com/CakeML/cakeml/tree/751ecd45c16b11ee0c3fd1280be7a6d798b5c457/compiler/dafny) is an artifact to inspect, not a new acceptance kernel or scheduled dependency.

**Pancake: a practical systems result with a split proof boundary.** The [Verifying Device Drivers with Pancake](https://arxiv.org/html/2501.08249v1) study combines explicit-memory systems programming, a HOL4-verified compiler using CakeML's backend, and automated Viper verification, with measured performance close to its C comparator. It is an arXiv preprint at its May 2025 revision with no established venue, and it is the follow-on rather than the language's first appearance: Pancake itself was introduced at PLOS 2023. This is useful evidence that a restricted imperative language can support real driver work. The study also explicitly leaves the Pancake-to-Viper translator, Viper/SMT infrastructure and linker trusted, and does not compose the driver's reentry properties and compiler result into one theorem. Its sound HOL4 Hoare logic provides a route toward a smaller boundary. A separate follow-on paper, [the PLOS '26 Pancake-to-Viper verification](https://trustworthy.systems/publications/papers/Tyler_LZSWTH_26.pdf) of a deployable LionsOS Ethernet driver, has a workshop venue; it states that the transpiler "is presently written in Rust and part of the trusted computing base", with a HOL4 rewrite and a Viper semantics in progress, and encodes its weak-memory assumptions itself. Retain the distinction between practical automated verification and the fully composed foundational result; neither supplies CHERI lowering here.

**Fiat-Crypto and Bedrock2/Kami: stronger examples in lineages already selected.** [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) generates specialized arithmetic through proved transformations and supplies a proved translation to the Bedrock2 AST. Its README explicitly separates that from its unproved language printers, including the C printer. Reuse the generator pattern and existing field-arithmetic work under [its current owner](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#the-cryptography-upstreams); the survey does not create another arithmetic generator or claim its printed C has acquired a compiler theorem.

The [Bedrock2 umbrella development](https://github.com/mit-plv/bedrock2) connects a verified program and compiler to a pipelined Kami processor for an IoT-lightbulb example, including a proof connecting its software-facing and hardware-facing RISC-V specifications. That is stronger than a source theorem or even an isolated compiler theorem. It demonstrates that a composed software/hardware result can exist in Coq. Its ordinary RISC-V specifications and processor are different from the pinned Sail term and CHERI target here; M1.6's local backend finding still stands. Q2b can inspect how the interfaces compose without inheriting that example's theorem or replacing this project's machine model.

**seL4: a delivered artifact comparator.** Its [proof overview](https://sel4.org/Verification/proofs.html) documents functional correctness, binary correctness and security properties, with availability depending on configuration. Its [assumptions](https://sel4.org/Verification/assumptions.html) retain hardware, boot/assembly and device obligations, and distinguish modeled information flow from timing channels. This is an established comparison for an executable artifact with substantial assurance, rather than a proposal for a new proof language. The register already records the different proof-authority boundary at [proof diversity](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-016a); seL4's configuration-specific results do not supply this platform's purecap target, source workflow or TAL evidence.

**MachCSL: source-located binary proof machinery over Sail, awaiting source rights.** [Kaashoek and Zeldovich's xv6 verification](https://arxiv.org/abs/2609.04043) builds an Iris concurrent separation logic over the Sail RISC-V model and proves statements about the concrete kernel image. The [archived Rocq source reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-reuse/languages.md#archived-machcsl-a-direct-sail-monad-logic-candidate-blocked-on-source-rights) identifies the Sail-monad `swp`, bind/frame/WP rules, concrete-image adequacy theorem and its assumption-audit target at an immutable edition. The maintained development is now Lean; the Rocq branch is no longer maintained and no source grant covering its proof files was identified. Its direct-over-term architecture is a useful comparison before constructing equivalent interfaces for Q35, but it replaces no selected machine logic or priced agreement obligation until rights, dependencies, exact assumptions and the canonical CHERI-term connection qualify. The theorem concerns another machine and ABI; capability/tag laws, noninterference, timing and robust preservation remain local obligations.

#### Capability-Aware and Parametric Verification

**Memory-model-parametric symbolic execution has a Rocq foundation.** [Compositional Symbolic Execution for the Next 700 Memory Models](https://arxiv.org/abs/2508.15576), OOPSLA 2025, mechanizes a generic compositional symbolic-execution theory and instantiates it with multiple memory models. This is particularly close to the proposed separation between generic reasoning and instance-specific memory laws.

The [CHERI instance and scope limitations](https://arxiv.org/html/2508.15576v2), stated in that publication's extended version, prevent overreading that result. The language is a sequential demonstrator; the CHERI instance is an idealized architecture-independent assembly memory model with a proved over-approximation soundness result for verification. Its under-approximation result for bug finding and implementation in Gillian are future work in this version. The work does not supply a compiled CHERI-C component or a connection to this checkout's Sail term. Inspect its memory-action, resource-production/consumption and framing premises under Q2b before inventing equivalent interfaces. Adopting its separate semantics directly would still face the semantic-anchor gate; a reusable proof pattern or proved connection is the useful output of that comparison.

**Morello-Cerise reaches adversarial-code encapsulation on a full-scale ISA.** [Morello-Cerise](https://www.cl.cam.ac.uk/~pes20/pldi25-paper646-camera-ready.pdf), PLDI 2025, combines Cerise's Iris logical relation, Islaris reasoning about known code, and T-CHERI properties of arbitrary code. It proves strong encapsulation for an example component above the full-scale sequential Arm Morello ISA model in the presence of arbitrary untrusted code. This is directly relevant to the stronger guarantee interfaces proposed here, and goes beyond a bounded-buffer functional theorem. Its subject is a particular Morello component and ISA, not a generic CHERI-RISC-V compiler, all Morello software, concurrent hardware or a theorem about this processor. Q2b's machine comparison should read the actual encapsulation argument; Q3b still owns the selected slice's evidence.

**Robust safety for an unsafe source through capability hardening.** [Endangered by the Language But Saved by the Compiler](https://iris-project.org/pdfs/2026-popl-robustdimsum.pdf), POPL 2026, compiles Rec, an idealized C-like language with a CompCert-style block memory model, to Cap, an idealized capability machine based on Cerise, turning pointers into capabilities so that a component verified in its Reckon separation logic stays safe when linked against arbitrary Cap code. Its semantic back-translation is built on DimSum, and "all our results are mechanized in the Rocq prover". The boundary is explicit: sequential programs only, an idealized calling convention, no Mem2Reg pass, and first-order ghost state because DimSum is incompatible with the countable step-indexing Iris uses. That last point is a concrete composition risk against this platform's Iris-based logic. It is the closest mechanized argument for the robust-preservation duty over a capability target, a comparison for SECOMP2CHERI's proof strategy rather than a result about CHERI-RISC-V; its artifact's licence is unread here.

**Gillian's language instances are different results.** The [TACAS 2023 CHERI-C work](https://arxiv.org/abs/2211.07511) formalizes a memory model in Isabelle/HOL and uses extracted code for concrete execution in Gillian. It must not be conflated with the later Rocq symbolic-execution foundation. [Gillian-Rust](https://giltho.github.io/publications/Gillian-Rust.pdf), PLDI 2025, combines semi-automated unsafe-Rust reasoning with Creusot's safe-Rust workflow through translated contracts. Its lifetime and prophecy reasoning makes it a useful borrow-contract comparator. The hybrid tool's Rust source verification does not become a Rocq certificate or a compiler-to-bytes theorem merely because some of its logical foundations have mechanizations. Keep it as a design comparison alongside RefinedRust, not a replacement for the selected Radium route.

#### Further Reuse and Emerging Compiler Work

| Project | Demonstrated contribution | Disposition for this proposal |
| --- | --- | --- |
| [Heapster](https://paulhe.com/assets/spec-extraction-oopsla.pdf), within [SAW](https://github.com/GaloisInc/saw-script) | Extracts functional specifications from memory-safe imperative LLVM code using a permission type system; the Coq/interaction-tree soundness result concerns a simplified assembly formalization. | Useful reverse-direction comparator for deriving a model from implementation. A generated model still needs an independently reviewed contract; LLVM ingestion, source correspondence, native compilation and the new logic/effect interface need their own justification. No SAW verdict is admitted automatically. |
| [Quiver](https://plv.mpi-sws.org/quiver/), PLDI 2024 | Completes a user-supplied separation-logic specification sketch for C code by abductive inference, and emits a machine-checked Rocq/Iris proof relating the code to the completed specification, so the inference engine itself need not be trusted. | The closest published shape for the proposed typed-hole tier: a sketch plus a checked completion, with the search outside the trust boundary. No theorem says an inferred specification is the intended or the strongest one and there is no completeness guarantee, so a completed sketch can be weaker than a reader assumes, and the result is relative to the RefinedC trust base and its C semantics rather than to a compiled binary. Its repository terms are unread here: only the artifact deposit's content licence was reachable, which is not the code's licence. |
| [Rocqet](https://github.com/rocqetry/rocqet), PLDI 2025 | Nested family polymorphism supports extensible definitions and proofs, with an extensible certified-C-compiler case study. | Directly relevant to refactoring semantic families together. Its documented Rocq/OCaml tuple needs local qualification; it is compiler-proof infrastructure rather than a CHERI backend or a reason to replace ordinary modules before reuse demands it. |
| [Pyrosome](https://github.com/DIJamner/pyrosome), [2026 thesis work](https://www.csail.mit.edu/event/framework-modular-metatheory-and-verified-compilation) | A Rocq framework for modular language metatheory and composable verified translation; examples include System F with references, imperative and linear calculi. | Research reference for language extension, linking and pass composition. The examples do not establish a production systems language, native optimizer or this project's source-correspondence theorem. |
| [Crane](https://bloomberg.github.io/crane/), [RocqPL 2026](https://bloomberg.github.io/crane/papers/crane-rocqpl26.pdf) | Extracts Rocq programs to readable modern C++, with configurable data mappings and a library-oriented adoption model. | Strong integration/ergonomics reference. The authors explicitly prioritize an unverified extractor, and the mappings and runtime support do not imply static-memory CHERI execution. Read it as an alternative for other host integration needs, not a new device exit. |
| [Verity](https://github.com/lfglabs-dev/verity) and powdr's [Yul-to-EVM compiler](https://github.com/powdr-labs/yul-compiler) | Lean-based contract/proof construction and verified lowering are active developments. Powdr's [July 2026 theorem](https://powdr.org/blog/yul-compiler) relates successfully compiled Yul and assembled EVM execution under matching-state and sufficient-gas premises. | Verity's [boundary record](https://github.com/lfglabs-dev/verity/blob/main/TRUST_ASSUMPTIONS.md) retains an explicit IR-to-Yul bridge hypothesis and trusted `solc`. These are separate toolchains: a proposed connection needs matching Yul semantics and a composed theorem over the supported fragments. An EVM result or passing execution tests establishes neither that composition nor Rocq/CHERI admission. |

The practical ordering is to inspect the existing construction and representation solutions first, then the actual capability-law interfaces, and only then consider infrastructure for a larger family of languages. These results strengthen the case for qualified reuse. They do not justify importing every listed tool or treating a missing local connection as a missing result everywhere.

#### Embedded Verification and Certified Synthesis

Small embedded languages and proof-producing tools provide implemented pieces of the proposed workflow, even when they do not provide its machine connection. Evaluate their notation, proof rules and certificate construction before designing a new surface; distinguish an upstream demonstration from an integration this repository has reproduced.

**AddressC: imperative syntax over an existing proof language.** [AddressC](https://github.com/koka-lang/AddressC) defines functions, mutable locals, loops and structure-access notation that yield ordinary Iris HeapLang programs, with Diaframe automation. Its [functional/imperative tree correspondence](https://www.microsoft.com/en-us/research/publication/fiptree-tr/) accompanies the PLDI 2024 work on move-to-root, splay and zip trees: simple functional arguments support proofs about imperative algorithms. This is a concrete Rocq-native authoring reference alongside LiveVerif, not just a syntax sketch. It is neither a C compiler nor a verified Koka backend. The README's reversal specification is partial correctness, conditional on termination; the documented build uses Coq 8.19.1 and older Iris/Diaframe revisions. HeapLang representation, primitive rules and compiled CHERI behavior are distinct obligations, so its frontend cannot be relabeled as a target-independent instance. Its own terms are MIT; the Iris, Diaframe and std++ trees it builds on carry their own, which an incorporation reads separately rather than inheriting.

Its cited predecessor [MiniC](https://gitlab.mpi-sws.org/iris/c) provides a monadic embedding into HeapLang, with proved symbolic execution and verification-condition generation. The repository explicitly says it is unmaintained and will not track current Iris. Read its construction as a reference, not as a preferred new dependency.

**SuSLik: synthesize the program and reconstruct its proof.** [SuSLik](https://github.com/TyGuS/suslik) synthesizes heap-manipulating programs from separation-logic specifications. Its [certification component](https://github.com/TyGuS/suslik/blob/master/certification.md), accompanying [Certifying the Synthesis of Heap-Manipulating Programs](https://doi.org/10.1145/3473589) at ICFP 2021, emits correctness certificates for HTT, Iris or VST. This is directly relevant to the proposed proof-producing builders: the search procedure need not be trusted when the emitted program's certificate is checked. Coverage differs by backend, and the HTT path defaults to leaving pure lemmas `Admitted` unless its proof option is enabled; advanced examples still require manual pure proofs. A generated certificate is therefore a candidate, not evidence of a closed proof. Qualify an actual certificate and its assumptions, preserving the intended contract; neither the existing allocation primitives nor an ordinary VST/HeapLang certificate establishes a CHERI connection. Its terms are not single-valued either: the synthesizer is BSD 2-Clause, while the three certification backends ship no licence file and declare GPL-3.0 only in their package metadata, so the producer and the certificate machinery do not travel together, and the paper's own footnote records that the memory model assumes allocation never fails.

**CFML and Sisyphus: reusable reasoning and proof repair.** [CFML](https://github.com/charguer/cfml) translates OCaml source to a Rocq AST and supplies characteristic formulas, higher-order separation logic and tactics for imperative proofs, including ownership and time-credit examples. Its documented environment uses Coq 8.20 and OCaml before version 5. The frontend/source connection and subsequent compilation remain separate from the proof over the AST. [Sisyphus](https://verse-lab.org/sisyphus/) uses an existing CFML proof to repair verification after a program change, including changes in algorithm structure; its published evaluation covers 14 OCaml programs. It is a focused maintenance experiment, not a general Rocq proof-repair service. Read these for representation and repair patterns; an OCaml runtime, CFML's logic and its dependencies do not become admitted by that reading. Incorporation would also require its own licence review, with Sisyphus advertising AGPLv3+ terms.

**Perennial/Goose: reuse the crash-recovery work already selected.** [Perennial](https://github.com/mit-pdos/perennial) builds concurrency, crash weakest preconditions, recovery and crash-refinement reasoning on Iris; its Grove extension handles distributed systems. The implementation checklist already selects the Perennial/GoJournal journal design for Gallina, so this is an existing source to consult at that work, not a new proposal to ship Go. [Goose](https://github.com/goose-lang/goose) explicitly trusts its Go-to-model translation and semantics, and Perennial documents a backwards-incompatible migration to new Goose. A selected edition, its crash model and the connection to this project's semantics must be explicit. Reusable Iris lemmas are not an automatic transfer of a Goose program theorem.

**Fully in-place programming: functional descriptions with a resource theorem.** [FP2](https://www.microsoft.com/en-us/research/publication/fp2-fully-in-place-functional-programming/), by Lorenzen, Leijen and Swierstra, identifies a linear functional calculus whose programs can execute without allocation or deallocation and with constant stack space, under its restrictions. The document that link serves is the extended Microsoft Research technical report MSR-TR-2023-19, not the ICFP 2023 proceedings paper, which is the separate PACMPL 7(ICFP) Article 198; an audited citation names whichever is read. Nothing in it is mechanized: its theorems are pen-and-paper appendices, and the report itself says only that the key proof may suit mechanization, so in this corpus it is a design reference rather than a checked result. It discusses static uniqueness and dynamic reference-counting embeddings; the implemented Koka route uses the latter, and that route's own Perceus result is likewise pen-and-paper and conditions its garbage-free claim on cycle freedom. This is a stronger resource-design reference than an effect annotation alone, but it does not make arbitrary Koka programs allocation-free or supply a verified CHERI compiler. Investigate static reuse laws for bounded components without importing a reference-counting runtime. [creditmonad](https://github.com/anfelor/creditmonad) is a separate Haskell DSL for testing amortized costs in persistent data structures. Its executable tests can falsify a proposed accounting argument; they neither prove a universal client bound nor connect that bound to target WCET.

**Velvet/Loom and LeetProof: an implemented integrated workflow.** [Velvet](https://github.com/verse-lab/velvet), built on [Loom](https://github.com/verse-lab/loom), combines a Dafny-like imperative surface, specification and invariant annotations, property testing, automated proof discharge and interactive fallback in Lean. Loom's paper of record, [Foundational Multi-Modal Program Verifiers](https://doi.org/10.1145/3776719), POPL 2026, derives each verifier's condition generator from monad transformer algebras with a soundness proof in Lean, and names Velvet and the distributed-protocol verifier Veil as its two instances. Its conditions go to Lean's tactics or, through the Lean-Auto and lean-smt toolkits, to Z3 and cvc5, so whether an automatically discharged condition carries a kernel-checked term depends on that toolkit's reconstruction. Partial correctness and termination can be proved separately and combined. It is a close design comparator for Vela's desired interaction, not a Rocq library or a CHERI deployment route. [LeetProof](https://arxiv.org/abs/2604.16584) stages specification validation, program/invariant synthesis and final proof construction around that verifier. Its most transferable step tests that intended outputs satisfy a contract and that deliberately wrong outputs do not, before spending effort on implementation proofs. Output uniqueness is appropriate only for a deterministic contract; a nondeterministic contract must permit its whole intended result set. Property tests and LLM reviews cannot establish correspondence to informal intent. The paper explicitly separates testing guards that may contain `sorry` from final correctness certificates; this project's analogous guards remain outside accepted proof dependencies.

**Priority:** read AddressC and SuSLik first for proof-surface and construction reuse, compare Velvet/Loom/LeetProof for workflow and specification testing, and consult Perennial within the journal work already selected. CFML/Sisyphus and FP2 are focused design references; creditmonad and MiniC are testing and historical references respectively. None removes the missing CHERI primitive rules, and none warrants a new compiler or semantic anchor merely to reproduce its demonstration.

#### Research That Changes the Experiments

**Optimization reuse: CompCert Chamois.** Its [current development](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/) and [authors' overview](https://www.pepr-cyber-arsene.fr/publications/jfla24.pdf) provide verified or validated transformations, including loop and block optimizations. Postpass scheduling is documented for the KVX, ARM32 and AArch64 backends; the [RISC-V fork's page](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-Arsene/index-chamois-riscv.html), dated November 2024, lists block optimizations, CSE, loop rotation and unrolling and control-flow checking but no scheduling pass, so that source does not establish scheduling for this target. Its BTL approach validates proposals from untrusted optimization machinery. M1.3 compares an applicable mechanism before authoring equivalent passes. Ordinary CompCert memory and target premises do not establish capability-tag preservation, trapping behavior, isolation, constant-time behavior or this platform's cost bounds. This is reuse within the already required backend, not a new speed-only checker. The selected fork's actual licence and dependency terms still need reading before incorporation; a forge classifier is insufficient.

The performance gap cannot be settled by compiler lineage: [CompCert's own description](https://compcert.org/compcert-C.html) reports approximately 90% of GCC `-O1` performance on ARMv8 and weaker results on workloads needing aggressive loop optimization. Those upstream observations neither establish parity with Rust/LLVM nor predict this custom target. Compare the selected backend on actual clients, retain valid transformations that help under the platform's constraints, and state the remaining gap.

**Representation and primitive contracts: VeriFFI.** [A Verified Foreign Function Interface between Coq and C](https://www.cs.princeton.edu/~appel/papers/VeriFFI.pdf), POPL 2025, generates VST function specifications from Gallina types and functional models, connecting high-level clients to proved C primitives with concrete representations. The checklist already names VeriFFI in its host-side checker fallback; Q2b additionally inspects its contract-generation mechanism alongside DeepSEA before inventing representation glue, and the frozen Q19c protocol reuses that comparison. The paper does not demonstrate the complete CertiCoq end-to-end theorem. More immediately, [the existing third-party audit](../../THIRD-PARTY.md) records a VST version and transitive-assumption mismatch with this repository. A design comparison is useful now; direct incorporation requires resolving those concrete blockers and reading the selected artifact's licence, not weakening the assumption audit.

**Borrowing precision: Polonius Alpha.** The Rust project's post [Enabling the next iteration of the borrow checker on nightly](https://blog.rust-lang.org/2026/08/04/enabling-polonius-alpha-on-nightly/), August 2026, enables a flow-sensitive borrow analysis by default on nightly. A loan returned on one branch need not prevent mutation on the branch where it is absent. This is an appropriate ownership-UX comparator for returned loans and reborrowing, with a pinned version and the announcement's unsupported cases recorded. It is an announcement rather than a design document: its evidence is a test suite and a crate run, it claims no formal model or soundness proof, it is not stabilized, and Alpha is narrower than the original Polonius, with the post itself naming programs the earlier implementation accepted and this one does not. The post aims to stabilize before the end of 2026 and reports no known issue in the Alpha subset, while the project's [2026 goal](https://goals.rust-lang.org/2026/polonius.html) still lists a soundness issue with the liveness of captured regions for opaque types and commits to a model in a-mir-formality validated against rustc, not a proof-assistant mechanization. The program the post shows Alpha rejecting, `conditional()`, reborrows conditionally inside a loop over a linked list, which is the loop-carried loan [the synchronous slice excludes](../language/core-design.md#loans-and-control-flow), so that restriction matches what Rust intends to stabilize. The [2026 borrow-checker roadmap](https://goals.rust-lang.org/2026/roadmap-borrow-checker-within.html) takes the next ergonomic steps as goals rather than features: a view-types experiment for partial borrows in signatures, place-named lifetimes such as `'map` and `'self.text`, and internal references formalized only for simplified Rust. The first two bear on [region naming](#surface-conventions) and on lending part of a record through a public signature, which the slice carries only as a loan record's footprint under an explicit call contract; the illustrative surface proposes [named views](#flow-sensitive-loans-and-restoration-contracts) as its spelling. The library proposal's lexical scoped combinators are a bounded mechanism, not the eventual expressiveness ceiling, and the awkward rewrites their restrictions cause remain unmeasured, since the canceled Q20b trial would have recorded them; importing rustc's analysis would still require a sound interpretation over the admitted semantics.

**Lifetimes without annotations: Goose.** [Goose](https://github.com/aardappel/goose), van Oortmerssen's 2026 language, is read at `master` revision `49d42ee7` of 2026-09-18 as a repository specification and implementation notes, with no paper; it is distinct from Perennial's Goose translator in [the tooling map](#existing-tooling-and-implementation-owners). It compiles a whole program in call-graph order and specializes each function per distinct root, the variable bounding a reference's target, so every root is statically known and one decidable rule replaces lifetime syntax: a reference may be stored only where its root's scope contains the destination root's scope. There is no heap, each resizable value topping a compiler-assigned data stack so that growth is a bump and nothing moves, and a named-ancestor `return from` elaborates to a hidden return discriminant each intermediate frame checks, with no unwinder, tables or destructors. Its premises are ones this platform already pays for at platform level, whole-program composition, [no runtime allocator](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-010), [recursion depth as a static fact](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-116), [bounded recursive data](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-143) and [no unwinding](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-100), so it is evidence that those constraints yield an annotation-free lifetime discipline and not only a memory plan. Three mechanisms are ownership-UX comparators for the loan rules. Static roots under specialization admit a loan stored in a field, which [the synchronous slice](../language/core-design.md#loans-and-control-flow) excludes and Rust prices with lifetime parameters; the price here is per-root code growth, which [the feature decisions](#feature-decisions) already gate for generic specialization, and a join over [the typed callee set](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-114) at indirect calls, since [closures and function pointers stay](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-115) where Goose forbids them. Append within capacity typed as a write at the current length, disjoint from the prefix, rather than a consume-and-return of the owner lets prefix loans survive a push; [the fixed-capacity write rule](../language/core-design.md#dependency-and-joins) can already express it, and the illustrative surface names it as [a tail view](#flow-sensitive-loans-and-restoration-contracts). Named-ancestor return is an elaboration into [the existing `Result` propagation exit](../language/core-design.md#loans-and-control-flow), where every intermediate frame still owes its restoration and cleanup predicate and each site adds a branch to the WCET path. No surface feature is scheduled by this reading.

**Goose's boundary is stated on the register's terms rather than inferred from its claims.** Its specification calls itself a working specification with informal soundness arguments and commodity-hardware benchmarks; the forge reports Apache-2.0 and the licence file is unread here. Three of its choices are refused. Its data stacks are large virtual reservations committed on page fault, with guard pages aborting on overflow, which [no overcommit or demand growth](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-15-189b) excludes, so only its capacity-limited array class exists here and its no-heap claim is weaker than the platform's. Its pools call a stale reference reading a freed-then-reused slot's next same-typed tenant type-safe reuse, which is the event [the reuse gate](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-015) closes and, under a pool's [confidentiality label](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-046), a cross-tenant disclosure. Its absence of aliasing rules rests on no shared-memory concurrency, only reference-free values crossing its threads, where [the exclusive-access theorem](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-096a) and restoration contracts need exclusive loans, and [presets share construct meaning](../extensions/assurance-profiles.md), so no Safe-only relaxation is available. Its union dichotomy, replaceable in place or interior-referenceable but never both, adds no safety over the loan tree, which refuses variant replacement while a payload loan is live.

**Resource inference: RaRust.** [Automatic Linear Resource Bound Analysis for Rust via Prophecy Potentials](https://arxiv.org/html/2502.19810v1), OOPSLA 2025, infers symbolic linear bounds for a safe Rust fragment using shared and prophecy potentials for borrowing. Its soundness is proved on paper against its resource-aware borrow calculus, with no mechanization and with costs assigned by explicit `tick` events. The stated limitations include unsafe code, generics, closures, trait objects and nonlinear bounds. This is a closer inference reference for a future named resource obligation than inventing a general grade engine first. An untrusted analyzer may suggest potentials and bounds for Rocq to prove; its printed answer supplies neither a certificate nor a target WCET bound. Source events, peak memory and machine time retain distinct interpretations. No analyzer port is scheduled by this reading.

**The precedent behind that inference is RaML.** [Resource Aware ML](https://www.raml.co/about/) infers polynomial bounds for a subset of OCaml by reducing potential-annotated typing to linear programming, covering higher-order and polymorphic code, user-defined inductive types, side effects and, in its current release, expected cost for probabilistic programs. It is the older and broader instrument, and it is also the limiting case of this kind of evidence: its soundness is pen-and-paper for the core calculi, no proof assistant accompanies the tool, and nothing connects the implementation to those theorems, so a printed bound is again a proposal rather than a certificate. Two facts decide how it can be used rather than read. Its newest release is a 2020 source tarball distributed from the project site rather than a version-controlled repository, so pinning it means pinning an archive nobody is maintaining. And while RaML's own files are BSD 2-Clause, that tarball bundles an OCaml compiler under other terms and a CompCert-derived example tree under the non-commercial licence, so vendoring it as it ships would import a restriction the deliverable that removes such restrictions exists to avoid.

**Time, progress and schedulability have three separate mechanized donors, each admitting its timing as a premise.** [A Separation Logic for Parallel Time Complexity with Work and Span Credits](https://iris-project.org/pdfs/2026-icfp-parcas.pdf), ICFP 2026, proves in Rocq/Iris that a fork-join program verified with given work and span credits is safe and that both quantities bound every execution, with span credits duplicated at fork and tagged so that only the admitted task may spend them. Its bounds are over computation graphs and not wall-clock time on a given number of processors, which needs a scheduler argument outside the mechanization, and it is worst-case with explicit constants rather than asymptotic. This profile has no fork-join parallelism; what transfers is the credit discipline for a cost that must compose across a branch. [Lilo](https://iris-project.org/pdfs/2025-oopsla-lilo.pdf), OOPSLA 2025, mechanizes termination-sensitive fair refinement in Rocq using progress credits, obligations and promises, and is worth reading precisely for the premise it needs: its liveness holds under scheduler fairness over an interleaving semantics with explicit yields, and this platform's cooperative reaction graph grants no fairness assumption at all, so a bound here comes from admitted activations rather than from that theorem. It is also not an Iris development, deliberately avoiding the step-indexing Iris rests on, so its rules do not compose with Iris ones by assumption. [RefinedProsa](https://iris-project.org/pdfs/2025-pldi-refinedprosa.pdf), PLDI 2025, is the closest published shape for the seam this platform's schedule obligation needs: RefinedC proves the C of a fixed-priority non-preemptive scheduler emits only traces satisfying a protocol invariant, and Prosa's analysis turns that trace into a machine-checked response-time bound. Its boundary is exactly where timing enters, and it enters as an assumption: worst-case execution times for every basic action and client callback are parameters to be obtained elsewhere, the arrival curve is assumed, one system call is axiomatized, and nothing is proved about compiled code, the compiler, the architecture or caches. Its artifact also states two different licences, a BSD 3-Clause file over the code and a content licence on the deposit record, which is the ordinary case for an archived artifact and is read before use rather than after.

**Specification coverage: check what the theorem constrains.** [Static Coverage in Deductive Software Verification](https://www.amazon.science/publications/static-coverage-in-deductive-software-verification), FMCAD 2025, uses unsatisfiable cores in the Boogie/Dafny setting to help expose vacuity, unconstrained behavior and redundant specifications. This complements the register's existing inhabitation witnesses and the implementation mutants the frozen Q19c protocol specifies. [The workflow contract's weakening probe](workflow-contract.md#change-and-weakening-probes) takes the same shape: it removes the exact copied-prefix equality from the held-out client's postcondition while retaining bounds, initialization, frame and status, and requires the independent expected-byte check to expose the loss. A non-vacuous theorem may still ignore the field that matters. Reuse that testing idea with existing instruments; a general Boogie-to-Rocq coverage tool is not implied, and even complete formal coverage would not prove the informal intent correct.

**Proof stability: measure development rather than successful proof counts.** [On the Impact of Formal Verification on Software Development](https://cseweb.ucsd.edu/~mcoblenz/assets/pdf/OOPSLA_2025_Dafny.pdf), OOPSLA 2025, reports interviews with experienced Dafny users identifying debugging, proof hardening and review as important costs. This is qualitative evidence, not a productivity multiplier. Dafny's [verification-optimization guide](https://dafny.org/dafny/VerificationOptimization/VerificationOptimization) gives transferable methods: isolate obligations, inspect resource use and vary search seeds to find fragile automation. [The workflow contract](workflow-contract.md#measurement-record-and-sampling) records diagnostic latency and review effort as separate series, and [its change probes](workflow-contract.md#change-and-weakening-probes) separate proof rediscovery after semantics-preserving edits from replay of already checked terms; [Q19a's trials](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-tooling-qualification.md) measured only machine latency, not review effort. The relevant practice can be reused without importing Dafny as an acceptance tool.

**Certified search and proof-logging machinery is read against standing rules rather than adopted, and [the alternatives register](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/background/architectural-alternatives.md#certified-placement-and-infeasibility-no-new-certificate-machinery) takes its disposition.** Constraint and pseudo-Boolean solvers now emit proofs and checkers exist for those formats, so an offline search returning a certificate is an available shape; [the proof inventory](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/assurance/proof-reuse/foundations.md#certified-search-and-the-registers-standing-refusals) records the candidates' provers, trusted bases and terms. An untrusted producer whose output the *existing* checks re-validate is admissible and free to be as aggressive as it likes: [the rule behind the CryptOpt deletion](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-066) states that it is aimed at minting a checker and not at that asymmetric-trust pattern, so an offline search proposing a placement the checks already in the toolchain re-validate needs no certificate-checking import at all. Importing one of these systems as a shipped certificate checker is refused: it mints a checker, several of the candidates check in Lean or HOL4 rather than Rocq and so fail [the translator conditions](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020) at the first, none retires an interim, and where the only yield is a smaller span over a plan that is already sound, [the no-tightening rule](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-105) refuses it on its own terms. A checked infeasibility certificate has a different yield, turning a search that found no placement into a proof that none exists, so the no-tightening rule does not reach it. Its imported form fails instead on [R-05-016](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-016)'s exclusion of acceptance on a non-Coq checker's verdict. A proof-producing route whose instance-specific term the kernel re-checks is not refused by that rule, but it is declined on present evidence: the local certificate model leaves its encoding seams unbridged, R-05-020's non-duplication and interim-retirement arguments are unmade, and no composition decision is shown to need the verdict. The alternatives register states the composition case and scoped contract a reopening must supply.

These additions qualify mechanisms against existing owners. Pinning another repository alone closes no integration gap. The current tuple, client theorem, generated-code boundary, transitive assumptions, actual licence and measured benefit decide adoption. A blocked package can still inform a design; it cannot be described as an installed or proved part of the stack.

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
That page is a rolling `latest` build of the tutorial rather than a versioned artifact, so an audited citation pins a release tag, currently [v0.8.0](https://github.com/idris-lang/Idris2/releases/tag/v0.8.0) of 31 October 2025.
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
Granule also implements [derived modality-distribution combinators](https://arxiv.org/abs/2112.14966) and [grade-directed program synthesis](https://doi.org/10.1007/978-3-031-57262-3_4). These address composition boilerplate and search, respectively; their [conditional Vela qualification](../extensions/graded-foundation.md#conditional-usability-producers) requires a real library client, checked output and measured benefit over existing combinators or proof search. Neither is supplied by general grade syntax or required for the first release.

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

**Rocq's own erasure removes only propositions and types, so an erased index needs Vela's own theorem.** Extraction and MetaRocq's certified erasure both rest on the elimination restrictions of `Prop` and `SProp`, so a proof-relevant index in `Type`, such as the natural-number index of `fin`, survives into the extracted program even where no branch inspects it. [A Ghost Sort for Proof-Relevant yet Erased Data in Rocq and MetaRocq](https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper81.pdf), a TYPES 2025 abstract by Rosain, Sozeau and Winterhalter, proposes a new sort for exactly that data. It weighs three elimination rules in Rocq experiments built on sort polymorphism and plans, rather than reports, the MetaRocq erasure proof; [the 9.3.0 manual](https://rocq-prover.org/doc/V9.3.0/refman/language/core/sorts.html) still lists only `SProp`, `Prop`, `Set` and `Type`, and a new sort would be a kernel change outside this design's CIC authority. The nearest same-prover mechanization of tracked irrelevance is Liu, Chan and Weirich's [DCOIω](https://doi.org/10.1145/3704843), POPL 2025, whose Coq proofs show a calculus that tracks dependency to identify run-time and compile-time irrelevance consistent and normalizing, with decidable conversion. That conversion compares terms up to indistinguishability, an equality rule CIC lacks, so it is a proof-engineering donor for [the substitution and erasure debts](../extensions/graded-foundation.md#proof-and-qualification-obligations) rather than an elaboration target, and its artifact's Coq version and terms are unread here.

**Design consequence:** make [graded dependent typing](#graded-dependent-foundation) part of Vela's foundation while keeping runtime representation, erasure, permission ownership, protocol state, effects and quantitative bounds separately interpreted. Library-level proofs would qualify the relationships needed by initial clients. [The graded foundation](../extensions/graded-foundation.md) specifies general grades, and Q25d's review prices their combined metatheory; the library proposal's narrow budget does not set the full language's scope.

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
interface BufferStorage {
    type Handle;
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
| [What's in the Box](https://2025.splashcon.org/details/OOPSLA/133/What-s-in-the-Box-Ergonomic-and-Expressive-Capture-Tracking-over-Generic-Data-Struct), OOPSLA 2025; [System Capybara](https://arxiv.org/abs/2607.09383), July 2026 preprint | Scala 3's capture checker tracks the capabilities a closure or generic container retains, with reach capabilities naming those inside boxed elements, and its new separation checker adds consumption, freshness and read-only tracking over the same capture sets. Capless is mechanized in Lean for type soundness and scope safety, and Capybara's Lean semantic soundness result yields no use-after-free or double free and data-race freedom. It is the closest mechanized design for [transitive captures](../language/core-design.md#kinded-authority) through instantiated type parameters, and its `consume` and read-only mechanics are candidates inside the [mutability dossier's](../extensions/interior-mutability.md) sharing rules. It derives uniqueness from one capture analysis where Vela keeps memory loans, hardware capabilities and effect permissions as separately interpreted kinds, and its proofs are Lean's, so it is a design reference. |
| [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383), POPL 2024; [Affect: An Affine Type and Effect System](https://iris-project.org/pdfs/2025-popl-affect.pdf), POPL 2025 | Continuations that discard or duplicate their captured context interact with ownership. Affect provides an affine type/effect system with Iris-based semantic soundness mechanized in Rocq, built over the Hazel handler logic and covering continuations stored in mutable references. The other is pen-and-paper with a Links implementation, so it supplies a calculus and the soundness bug that motivated it rather than a checked development, and its artifact is GPL-3.0-or-later. [The handler dossier](../extensions/handlers-async.md) uses these resource rules for general handlers and suspension; their language and runtime are not the selected CHERI instance, and the synchronous Q21a slice supplies no qualification of them. |
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
support. The [authored dependent example](../../examples/dependent.vela) combines
invariants, output loans and proof mode.
The [packet validator](../../examples/first_slice.vela) shows the bounded
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

A loan returned on one branch leaves the owner writable on the other, the conditional return [Polonius Alpha](#research-that-changes-the-experiments) accepts on nightly. A returned exclusive loan also needs a contract for the moment it ends, which [Creusot writes with a prophecy and Prusti with a pledge](#what-the-rust-verifiers-contribute). Vela states it with `restores`, where `final(slot)` is the value the caller leaves in the slot:

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

One `restores` clause covers both ways to succeed, since `Set` replaces a found value and adds an inserted one. The [synchronous slice](../language/core-design.md#loans-and-control-flow) admits only the shared form of this return, and it excludes the loop-carried variant, a conditional reborrow inside a loop, which is also the program the Polonius Alpha announcement shows it rejecting.

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

In the bounded library proposal, `SetFirst`'s update comes from `Build.with_element`, exposed as `WithElement(ref target, 0, (scoped ref byte selected) => { selected = value; })`. Its rule introduces a fresh loan inside the callback contract, suspends the parent while it is active, and forbids placing the loan in the callback's result or a longer-lived capture. Given a total callback contract it proves invocation once, termination and restoration; a once-callable type alone proves none of those facts about its caller. The pilot callback may return a `Result`, restoring the parent before the caller propagates an error, but supports neither a return out of the caller nor suspension. The target loan model must handle each supported exit explicitly, including branch-sensitive returned loans, loop edges and `Result` propagation, and cannot claim them from the callback theorem. A source frontend must prove this elaboration, not merely print the combinator call. Whether inferred restoration removes the pilot's rewriting cost without weakening the resource contract is what the canceled Q20b trial and Q21a's declined qualification would have answered; both questions remain open.

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
    where Duplicable(C)          // a second resumption copies everything the continuation retains
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
representation laws. The [compiler pipeline](#proposed-architecture) binds
that checked interpretation to the authored source through the final image.

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

**An independently implemented direct backend can remove the non-commercial licensing dependency on CompCert/SECOMP.** That benefits commercial builds, compiler redistribution and independent rebuilding, not just the licence on the emitted OS image. The [upstream licence reading](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#compcert-and-secomp) distinguishes the non-commercial compiler grant from its LGPL-licensed subset and separately negotiated commercial rights. Keeping the compiler unpublished never removed a restriction on commercial use, and it is no longer even available as a containment: R-13-027 makes the toolchain software the device runs and R-18-004e ships it in the first release, so a shipped image carrying a CompCert-derived backend is distribution, and this deliverable is the route that makes that image licensable rather than an optimization of one that already is.

This benefit requires independently authored or suitably licensed compiler and proof sources. A new IR does not relicense copied or adapted backend passes; CompCert, SECOMP and Chamois reuse needs a selected-file and transitive-dependency audit. Clight itself has an LGPL option, so bypassing Clight is neither necessary nor sufficient to remove non-commercial terms. [Rocq's LGPL licence](https://github.com/rocq-prover/rocq/blob/V9.1.1/LICENSE) permits commercial use but retains redistribution obligations: removing non-commercial dependencies is not removing all copyleft obligations or all Inria-associated software.

**Whole-toolchain removal is a separate claim.** It also needs dispositions for the [retained compiler duties](#compiler-amendment-obligations), [Velus's separate non-commercial grant](https://github.com/symbiogenesis/VerifiedOS/blob/main/THIRD-PARTY.md#vélus), and the [CertiRocq oracle's CompCert package dependency](../../THIRD-PARTY.md#development-tools-contained-by-use). The oracle uses dual-licensed modules, but its package installs the full compiler. Q21b records route-local removal and residual toolchain dependencies separately; complete removal is credited only after the affected duties have accepted replacements and the selected dependency closure supports the claim. This comparison authorizes no such replacements.

#### Mechanically Produced Evidence

The eventual frontend's mandatory output has this schematic shape:

```text
SourcePackage(sourceClosure) = {
    coreProgram;
    elaboration : Elaborates(sourceClosure, coreProgram);
    typing : WellTyped(coreProgram);
    sourceMap : SourceLocations(sourceClosure, coreProgram)
}
```

The reviewed elaboration relation covers checked parsing or parse validation, binding and resolution, implicit insertion, overload/instance selection and desugaring. Source maps aid navigation; they are not correspondence proofs. Bind exact source, generated inputs and dependency/configuration identities to the derivations. MetaRocq can help construct and check terms but does not prove an external frontend merely by receiving its output. Typed holes remain outside accepted packages. Source, resolution and desugaring mutations must invalidate or refute correspondence even where a stale core theorem still checks.

Linking is a typed proof boundary. Generated required/provided contracts state calling convention, preserved registers, stack shape, memory/capability authority, relocations, callbacks and reentrancy, effects and observations. Discharge them through existing TAL judgments where applicable and CIC proofs for deeper composition, not new TAL grade axes or an on-device solver. Independently compiled verified-C, Rust and generated components must agree, and their composition must retain required robust properties. An unchecked linker assumption cannot replace that evidence. The compiler-side precedent for composing separately compiled modules is CompCertO's open-module refinement: [CompCertOC](https://pldi25.sigplan.org/details/pldi-2025-papers/27), PLDI 2025, carries threaded Kripke memory relations through 18 CompCert passes, horizontally and vertically composable, for cooperative threads sharing stacks. The selected Vela target's linkage and preservation work is priced in the [shared retained-route allowances](../../PLAN.md#shared-foundation-and-retained-route); this precedent supplies no inherited CHERI theorem or implied adoption of CompCertOC.

The [proposed pipeline](#proposed-architecture) binds these packages through optimization, typed linkage and final image validation. The decoder's required route goes through Clight; a direct explicit-memory capability-IR branch is conditional. Both must terminate at the same pinned Sail term, never a machine semantics generated by the compiler.

A promoted artifact's evidence package retains source and independent contract, elaborated program and correspondence, representation and ABI, functional/resource/observation proofs, solver certificates and actual transitive assumptions, optimization evidence, link contracts and composition, source/build/dependency/layout/byte identities, semantic pin and guarantee theorems, and measurements on those exact bytes. This organizes existing evidence rather than introducing a replacement admission format. A semantic dependency change reopens affected obligations even when displayed goal identities remain stable.

## Proof libraries and tool qualification

### Bounded component foundation

A generic buffer proof depends on checked operations, representations,
frame/restoration laws and the matching machine interpretation. Prove the generic
algorithm against that interface and instantiate each law for the actual
target. The [synchronous design](../language/core-design.md) defines the
composition fixture. The [ownership libraries](../language/first-release.md#ownership-libraries)
own the public interfaces, and the
[delivery plan](../../PLAN.md#vela-first-release-delivery) names their producers.
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
| Representation transfer | [CoqEAL](https://github.com/rocq-community/coqeal) and [Trocq](https://github.com/Trocq/trocq) are candidates after the package trial establishes a native Rocq transport baseline. Qualify the selected revision and assumption closure. [Comparison protocol](workflow-contract.md#representation-transfer-comparison) |
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
