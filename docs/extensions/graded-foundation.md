# Graded dependent foundation

> Rules for [first-release graded typing](../language/first-release.md#default-graded-checking)
> and extensions to its domains and resource interpretation.

## Scope and research boundary

General domains extend the fixed ownership modes and runtime/erased phases of
the [synchronous core](../language/core-design.md#judgments-and-interpretations).
The [resource interface](#resource-and-computation-interface) supplies the common
premises for [handlers](handlers-async.md) and [mutable cells](interior-mutability.md).
The [composition contract](full-language-review.md) specifies combined cases.

The judgments below construct evidence about the elaborated image. Substitution,
structural rules, preservation and erasure are theorems over the selected
CIC and resource interpretation. The frontend must connect the exact source to
that image. [Frontend admission](full-language-review.md#frontend-admission)

The [graded research comparison](../assurance/verification-strategy.md#reading-the-graded-type-claims)
describes the roles and limits of GrTT, GraD and the Agda erasure development.
The [source replay](../tooling/elaboration-prototype.md#pure-graded-source-replay)
checks a pure fragment with `NatExact`, `NatBound`, general modal semirings and
Boolean `Presence`, including graded boxes, indexed sums, type-grade variables
and dependent records. On the Rocq kernel side, dedicated closed-assumption developments mechanize the
GrTT structural and substitution metatheory (`weakening`, `exchange`,
simultaneous value and type-variable substitution, and the explicit `(s, r)` core
calculus), symbolic semiring polymorphism, CBV erasure with non-interference,
verified zero-type-use substitution skipping, and the unified `GradedCore` /
`JoinDomain` calculus (`core_weakening`, `core_exchange`,
`core_value_substitution`, `core_subgrade_admissible`,
`core_grade_substitution`, `core_zero_type_use_irrelevance`, and
`core_type_substitution`) with
frontend `domain`/`inductive`/`<grade q : D>`
elaboration, Rocq-replayed constraint inference, derived modality combinators,
and bounded grade-directed synthesis.
[GrTT metatheory](../../tools/rocq/graded_metatheory.v) ·
[Unified graded core](../../tools/rocq/graded_core.v) ·
[Unified core metatheory](../../tools/rocq/graded_core_metatheory.v) ·
[Unified core type substitution](../../tools/rocq/graded_core_type_subst.v) ·
[Symbolic semiring polymorphism](../../tools/rocq/graded_semiring.v) ·
[CBV erasure and skipping](../../tools/rocq/graded_erasure.v) ·
[Grade inference](../../tools/toolchain/graded_inference.py) ·
[Derived combinators](../../tools/toolchain/graded_combinators.py) ·
[Grade-directed synthesis](../../tools/toolchain/graded_synthesis.py)

## Extension selection and qualification

[First-release default graded checking](../language/first-release.md#default-graded-checking) selects natural computation grades and separate type-use accounting. Qualify that selection and any broader grading extension against fixed use modes using a concrete client's independently frozen behavior/resource/representation contract, evidence endpoint, toolchain, positives, and semantic refusals.

| Candidate | Comparison and admission evidence |
| --- | --- |
| Fixed use modes and checked library contracts | Baseline: state-indexed operations and natural exact/bounded trace judgments under existing ownership/phase rules, keeping actual proof/maintenance obligations. |
| `NatExact`/`NatBound` with separate type use | Qualify boxes, dependent data, and arithmetic with checked domain laws, usage-aware CBV interpretation, and exact-source correspondence; link demand to trace properties, compare dependency rows against the simplest sound account, and show dependency/parametricity/authoring benefit. |
| General domains | Show an analysis natural domains cannot express cleanly and prove its interpretation and composition laws. |

Before a trial, freeze benefit thresholds and budgets for annotations, proof/review/repair effort, diagnostics, checking time, and memory. Separate demand reconstruction, constraint search, and certificate/kernel replay; track fresh vs changed-input runs, open goals, and budget refusals under unchanged behavior, preconditions, and endpoint (accounting setup/maintenance separately from recurring benefit) via [the validation handoff](../../AGENTS.md#tool-execution-and-validation). Missing laws or exhausted budgets keep claims open; separate unsupported inputs from semantic refusals; domain extensions also require measured benefit.

To qualify [GrTT's distinction](../assurance/verification-strategy.md#reading-the-graded-type-claims), replay an index unused computationally that contributes to later declarations and result types, testing both an allowance-violating computation edit and a computation-preserving type-dependency edit across callable and locked module boundaries, naming affected bindings and retained telescope rows.

Gerty's [substitution-skipping optimization](../assurance/verification-strategy.md#reading-the-graded-type-claims) is separate and optional (requiring proved zero-type-use irrelevance, agreement with ordinary substitution, and net checking speedup including solver cost inside an already justified graded build—never commissioning a speed-only tool or relying on donor timings). Pure `NatExact` proves zero-type-demand substitution preserves inferred types and counts; [CBV erasure and skipping](../../tools/rocq/graded_erasure.v) proves `apply_nat_skip_agrees`, `apply_type_skip_agrees`, `let_nat_skip_agrees` (with a 40-binder deep-telescope check), `erasure_simulation`, `closed_erasure_sound`, `zero_computation_irrelevance`, and `zero_var_non_interference` under closed assumptions, and `tools/toolchain/elaborate.py` integrates checked zero-type-use `substitute()` short-circuiting with exact-equality and multi-binder benchmark checks (`_q25cb_zero_type_use_skip_and_benchmark`). [Irrelevance theorem](../../tools/rocq/graded_type_irrelevance.v) · [Metatheory audit](../../tools/tests/test_holdfast_graded_metatheory.py) · [Frontend skip benchmark](../../tools/tests/test_holdfast_graded.py#_q25cb_zero_type_use_skip_and_benchmark)

### Audio routing candidate

`StereoRoute` specializes a pure router (`(period + 1) + (period + 1)` stereo length, plus channel-label count). The ungraded baseline checks a pointwise Rocq result equation; graded replay checks the dependent signature and demands:

| Binder | Computation | Type | Type dependencies |
| --- | --- | --- | --- |
| `period` | 0 | 4 | Twice in the stereo input and twice in the result |
| `labelCount` | 0 | 1 | Once in the channel-label input |
| `stereo` | 1 | 0 | n/a |
| `channelLabels` | 0 | 0 | n/a |

Both checkers reject specializing to the old period; graded checking also rejects a zero computation allowance on returned samples. Since the baseline already checks dependent shape and behavior, selection trials need a client obligation that benefits from exact counts at one shared evidence endpoint. [Source fixture](../../tools/tests/fixtures/graded-audio-route.hf) · [Paired replay](../../tools/tests/test_holdfast_graded_client.py)

### Conditional usability producers

Granule's [derived distributive combinators](https://arxiv.org/abs/2112.14966) and [grade-directed synthesis](https://doi.org/10.1007/978-3-031-57262-3_4) produce ordinary checked terms (no HoldFast compatibility/correctness evidence or donor code is incorporated). The prototype modules `tools/toolchain/graded_combinators.py` (`derive-combinator`) and `tools/toolchain/graded_synthesis.py` (`synthesize-graded`) implement structure-checked distributive combinator derivation and resource-pruned bounded synthesis with behavioral oracle rejection, zero-axiom Rocq replay, and negative controls; wider client-benefit adoption still requires a named client with repetitive conversions or bounded synthesis vs proved combinators/existing proof search: fixing constructors/direction/premises for derivation (not assuming `Box_q (F A) <-> F (Box_q A)`), fixing grammar/components/behavior/budget for synthesis (failed search proves no impossibility), preserving captures/ownership/phase/effects and assumption audits, and testing valid clients, invalid `Dup`/domain premises, changed bindings, well-typed wrong candidates, and bounded failure while measuring recurring benefit vs total checking cost. Derived combinators follow [the generation contract](metaprogramming.md#qualification). [Extension plan](../../PLAN.md#language-extensions)

## Dimensions and lawful domains

Judgments fix `S` (definitions, universes, grade identities, primitive contracts, logic, representation, observation model) and name the elaborated term checked under CIC `Type i : Type (i+1)` cumulativity (no `Type : Type`, conversion extensions, global UIP, proof irrelevance, or extensionality axioms; transports need accepted terms and assumption audits). Rocq 9.3.0's native `SProp` and sort polymorphism provide an opt-in representation for strictly proof-irrelevant erased witnesses (`ghost` propositions whose elimination never drives runtime control flow) without global UIP or banned `-allow-rewrite-rules`, keeping `Prop`/`Type` separation intact.

| Dimension | Meaning | Evidence it cannot replace |
| --- | --- | --- |
| Computation use `u` | Demand on stable values in the selected graded value semantics | Invocation counts, physical copies, exclusive permission or WCET |
| Type use `v` and dependency rows `M` | Demand in the result type and in every declaration's type | Runtime availability of an erased index |
| Phase and representation `p, rho` | Runtime, specification or proof; represented or erased at the selected ABI | Protocol disposal or secret zeroization |
| Resource context `Delta` | Live ownership, loans, restoration and other kinded authority under the selected logic | A generic numeric, effect or security annotation |
| Effects `E` | Allowed operation footprints, including transitive calls and captures | Permission to perform those operations |
| Trace contract `T` | Named source events, their order and exact counts or upper bounds | Surviving machine calls or instruction timing |
| Target bound `W` | The existing final-CFG cost judgment against pinned Sail timing | A source use or event count without its transport theorem |

In the extensible proposal, domains are sealed CIC records (never runtime plugins or client-swappable dictionaries behind signatures; first release excludes arbitrary domains and general domain inference):

```text
q ::= 0_D | 1_D | named_constant_D | alpha_D | q +_D q | q *_D q
    | certified_domain_operation_D(q, ...)

Domain D:
  carrier Q : Type i; equivalence =D; preorder <=D
  additive commutative monoid (+,0); multiplicative commutative monoid (*,1)
  left/right distributivity; multiplicative zero annihilation
  congruence and monotonicity of both operations
  admissible weakening/contraction/scaling relations with proved meanings
  InterpretUse, InterpretTypeUse, CheckCertificate and soundness obligations
```

`q <=D q'` admits demand `q` under allowance `q'` (exact-use requires equality; promotion/motive scaling assumes commutative `*`, while noncommutative domains need `GF-domain` ordered actions; custom ops need composition laws; incomparable branches need proved bounds or result-indexed contracts; products need compatible subject/trace interpretations). `NatExact` uses `(`+`, `*`, `=`)`; `NatBound` uses `<=`; Boolean presence uses `(`or`, `and`)` (`1+1=1`). [Rocq domain trial](../../tools/rocq/graded_domains.v) verifies these three ordered semiring records alongside `JoinDomain` (`NatExactJoin`, `NatBoundJoin`, `PresenceJoin`, `LinearDomain`, `AffineDomain`, `SecurityLoHi`), symbolic `GradeExpr` polynomial normalization, row certificates, and substitution across exact-to-bound and bound-to-presence maps; [proof/qualification obligations](#proof-and-qualification-obligations) govern source use. Zero-use erasure requires excluding relevant observations (nontriviality/positivity/no-zero-divisors alone are insufficient); exact cardinality needs faithful counts without relaxing zero/two to one; uniqueness needs spatial exclusivity; security needs relational observation laws (idempotent `1` gives none).

## Stable telescope and dependency bookkeeping

`J(M; u; v; Gamma |- t:A)` (implicit `S`) elaborates `t`, `A`, and demand interpretation to checked terms and image theorems. `Gamma` is an ordered telescope of stable values/types, immutable snapshots, and logical identities (runtime handles are descriptors; permissions live in `Delta`; stability grants no copy rights and indices never evaluate unsynchronized mutable reads). `M[i]` records prior declarations' use in `Gamma[i]`'s type; `u` and `v` have one entry per declaration for `t` and `A` (`v` is not a sum of `M` rows; zero-padded to the same telescope):

```text
CTX-EXT: J(M; a; 0; Gamma |- A : Type i)
         implies WF(M appended with a; Gamma, x:A).

VAR:     WF(M; Gamma), Gamma[i] = x:A
         implies J(M; unit_vector(i); padded(M[i]); Gamma |- x:A).

UNIV:    WF(M; Gamma)
         implies J(M; 0; 0; Gamma |- Type i : Type (i+1)).
```

Runtime variables require represented bindings in `rho` (spec variables cannot become runtime operands; tracked resources never enter `Gamma` via embedded record propositions—only their identities may index predicates).

### Functions and application

For `Pi x:(s,r) A. B` (body use `s`, codomain use `r`, domain demand `a`, codomain demand `(b,r)` under `Gamma,x:A`):

```text
PI:  J(M; a; 0; Gamma |- A : Type i)
     J(M,a; (b,r); 0; Gamma,x:A |- B : Type j)
     ---------------------------------------------------------
     J(M; a+b; 0; Gamma |- Pi x:(s,r) A.B : Type max(i,j))

LAM: J(M,a; (w,s); (b,r); Gamma,x:A |- t:B), with PI premises
     ---------------------------------------------------------
     J(M; w; a+b; Gamma |- lambda x.t : Pi x:(s,r) A.B)

APP: J(M; w; a+b; Gamma |- f : Pi x:(s,r) A.B)
     J(M; z; a; Gamma |- v:A), with PI premises
     ---------------------------------------------------------
     J(M; w+s*z; b+r*z; Gamma |- f v : B[v/x])
```

Application type use is `b+r*z` from substituting `v` for `x` in `B` (reconstructed under conversion rules; [substitution/resource obligations](#proof-and-qualification-obligations) cover closure envs and call modes). HoldFast evaluates left-to-right by value: effectful arguments elaborate as `bind x <- c; call f x` (evaluating `c` once for its trace/effects/exit before applying `x`, so zero use never erases effects/failures/verdicts and two uses never re-evaluate `c`; reordering across handlers/mutation/checkpoints requires proof).

The Rocq CBV trial connects exact/bounded natural-lambda grades to an instrumented state/event model (exact vs bounded argument-value reads; prefix preservation on first failure; [execution model](../../tools/rocq/graded_cbv.v)); the scoped-span trial instantiates argument transitions on `Span<byte>` proving descriptor preservation and untouched-byte framing ([scoped argument model](../../tools/rocq/graded_cbv_span.v), [`GF-cbv`](#proof-and-qualification-obligations)); the dependent box model ties checked elimination to arithmetic and specialized vector identities ([dependent box interpretation](../../tools/rocq/graded_modal_cbv.v)). Torczon et al. ([OOPSLA 2024](https://doi.org/10.1145/3689750), [extended](https://arxiv.org/abs/2311.11795v2)) mechanize CBPV clock-effect/coeffect soundness preserving unused-result effects (`GF-cbv` and `GF-control-mutation` remain HoldFast's dependent/mutable/handler debts; artifact unread); Lorenzen et al. ([ICFP 2024, §5.1](https://antonlorenzen.de/papers/oxidizing-ocaml-modal-memory-management.pdf)) forbid promoting a repeatedly callable opener's returned handle without value-only promotion (`Box_q` likewise promotes evaluated pure values only, never dropping acquisition/cleanup/effects or forging `Dup`).

### Substitution and structural rules

For `Gamma, x:A, Xi |- t:B` and `Gamma |- v:A` (`v` having subject demand `z`), each demand row `d=(d_G,d_x,d_X)` after `x` updates as:

```text
substDemand(d,x,z) = (d_G + d_x*z, d_X)
Gamma, x:A, Xi   becomes   Gamma, Xi[v/x]
u               becomes   substDemand(u,x,z)
v_type          becomes   substDemand(v_type,x,z)
each later M row becomes   substDemand(that row,x,z)
```

Earlier rows stay unchanged and `x`'s row drops; capture-avoiding substitution also updates types, motives, index-dependent grades, captures, and exit predicates across the whole telescope (`GF-substitution` requires simultaneous typing/WF and image-agreement proofs, never unchecked solver rewrites or computed indices).

| Structural operation | Admissibility condition |
| --- | --- |
| Extend an unused declaration | Construct type row, zero-pad subsequent rows and demand vectors; preserve prior dependencies. |
| Remove a declaration | Zero demand in term, result type, and all retained declaration rows, or substitute a checked stable witness (`u[x]=0` alone is insufficient). |
| Exchange declarations | Dependency-preserving permutation renaming rows/identities/captures (forbidden across an actual dependency). |
| Contract pure descriptors | Add demands and reindex telescope with checked equality (operations still need live spatial permission). |
| Weaken an advertised bound | Supply domain order proof (exact-use allows equality only; no implicit coercion to approximate domains). |
| Drop, duplicate or scale a resource | Supply `Dispose`, `Dup`, or repeated-use protocol (no generic telescope rule transforms `Delta`). |

### Dependent data and elimination

`Sigma x:^r A. B` uses `PI`'s `a,b,r` premises; pair introduction takes component demands `z,w` with second-component type demand `b+r*z`, yielding `(z+w, a+b)`. Tensor dependent elimination requires an explicit motive `C(p)` (opaque pairs cannot split field demands arbitrarily):

```text
p : Sigma x:^r A.B                  subject demand z
C(p) : Type k under Gamma,p         demand (c,kappa)
body : C((x,y)) under Gamma,x:A,y:B  subject (w,s,s)
                                    type (c,kappa,kappa)
----------------------------------------------------------------
match p as (x,y) in body : C(p)      subject w+s*z
                                    type c+kappa*z
```

Requires the full WF telescope (including `y`'s `r`-dependency on `x`) and checked motive substitution; asymmetric field allowances need graded modalities or a proved eliminator; erased weak pairs give no runtime witness/tag/projection (runtime matching requires a represented scrutinee, barred under security-lattice zero). [Dependent pair replay](../tooling/elaboration-prototype.md#graded-dependent-pair-replay) tests length-indexed vectors sharing computation allowance with exact motive rows.

`Box_q A` scales subject vector by `q` at introduction (fixing type vector) and eliminates with body demand `q` (type demand `q*kappa` for motive box-use `kappa`), adding `z` to body subject and `kappa*z` to body type demand without hiding effects or forging `Dup` (representations/erasure explicit in `rho`; [graded box replay](../tooling/elaboration-prototype.md#graded-box-source-replay)). Finite sums check branches under one advertised demand (substituting constructor dependencies; unequal branch counts stay result-indexed or bounded, never summed); bounded iteration uses inductive invariant, grade recurrence, and termination measure; general inductive eliminators need checked constructor/motive resource rules.

## Resource and computation interface

```text
S; M; Gamma; Delta_in |- c : Exit(A,Q)
  [use u; type-use v; captures C; effects E; trace T;
   phase p; representation rho; exit duties O]

Q(tag,value) = Delta_out for that represented exit
```

Generated theorems relate entry, elaborated execution, and every exit in the anchor (`Delta` holds ownership, loans/restoration, protocols, effect/security rights; `Own(id,shape,snapshot)` is an interface predicate rather than a CHERI primitive; identity grants no authority; `Q` carries transferred captures and branch discriminants until joined/restored; first release uses fixed synchronous modes, while `Suspend`, concurrent `Share`, and multi-shot `Dup` enter only in commissioned extensions):

| Interface obligation | Required evidence |
| --- | --- |
| `Capture(C,Delta)` | Complete transitive retained env (handlers, tasks, stored continuations, cell fields) with kinded resources, lifetimes, effects, and representation (evaluation-only uses tracked separately). |
| `Dup(C,Delta)` | Semantic split supporting both uses under interference, lifetime, and protocol laws (immutable snapshots qualify by representation; exclusive owners/loans/single-use tokens have no default instance). |
| `Dispose(Delta,exit)` | Explicit resource-returning/terminal transition (affine permission drop does not discharge protocols, must-erase data, or mandatory examined verdicts). |
| `Suspend(C,Delta,rho,O)` | Stable represented storage, live loan ancestry, closed invariants, bounded checkpoint restoration/cleanup, and no escaping refs into moved frames. |
| `Transfer(domain,Delta)` | Cross-domain permission/representation transport preserving exclusivity, lifetime, publication order, and manifest join. |
| `Share(protocol,Delta)` | Concurrent ops preserve invariant under interference and pinned memory model (shared handles grant only declared ops). |

`Dispose` is an explicit effectful/write transition (erasure does not zero registers/spills); mandatory verdict elimination obeys [R-05-097–R-05-100](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-097) and source ownership connects to [R-05-096a](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-096a) (grades never derive overlapping permissions). Sequencing composes transitions, concatenates traces, and unions effects; repeated callbacks/resumptions require repeatability contracts, separated `Delta_i`, and per-call trace laws (grades prove neither trace counts, order, termination, nor machine call counts; multi-shot capture needs `Dup` for the entire context even on pure arguments). Mutation updates owner snapshots (shape changes consume old owners; historical copies stay stale until re-related; open-cell suspension needs stronger protocols; grades authorize no shared mutable capabilities or unsupported atomics).

## Schematic derivations and invalid neighbors

Hand derivations for the extensible proposal (not executed checker outputs; negatives preserve valid representations/resources and fail at the named premise rather than syntax errors):

### Pure dependent identity

In `NatExact`, `Gamma = a:Type i, x:a`, `M=((),(1))`: `VAR` gives `u=(0,1), v=(1,0)` for `x:a`; `LAM` over `x` gives `Pi x:(1,0) a.a` (`a` subject 0, type `1+1=2`); abstracting `a` yields:

```text
id : Pi a:(0,2) Type i. Pi x:(1,0) a.a
id = lambda a. lambda x. x
```

Instantiating `a=Byte, x=7` erases `a` and keeps `7`; changing `a`'s type grade to 1 fails `2=1`, and changing `x`'s subject grade to 0 or 2 fails `1=0` / `1=2` (scalars imply no byte-storage ownership). For `(2,cons 7 (cons 9 nil)) : Sigma k:Nat.Vec Byte k` (with constructors `nil:Vec Byte 0`, `cons:Byte -> Vec Byte k -> Vec Byte (k+1)`), substituting `2` matches `Vec Byte 2`, while packing under `3` fails `2=3` (`GF-elimination` owns recursor/constructor laws).

### Runtime-dependent packet

With `N=4`, immutable `n=2`, buffer `[7,9,0,0]`, entry `Own(r,4,[7,9,0,0])`, and checked descriptor `h:Handle(r,n)` (capacity/narrowing determined by contract): in `Gamma=r:Identity,n:Nat,h:Handle(r,n)`, `h` depends on `r,n`; `(n,h):Sigma k:Nat.Handle(r,k)` uses `(n=1,h=1)` in subject, retains `n` physically, and attaches `n<=N` as erased evidence. Matching `(k,p)` once (`s=1`) repacks `(k,p)` retaining `r` and loan/restoration duties; bounded readers use their own recurrence rather than inheriting `s=1` (`GF-resource` owns read/view/restoration lemmas). Negatives: erasing `n` fails reader's phase premise; packing `Handle(r,2)` under `3` fails without transport; deleting `n` despite zero computation use breaks `h`'s WF telescope; resizing while keeping stale length fails the output predicate.

### Graded callback and shared service join

A pure callback over an immutable 2-byte snapshot runs twice in order (`CallCount=1+1=2`, `NatExact(2)` on callable, `Dup` on env; allowance `1` fails `2=1`; single-call branches must return an indexed count or bound). In [the combined client](full-language-review.md#composed-client-and-inhabited-entry), packet/frame owners and `AddOnce(request,n)` stay in `Delta` outside the handler (`n` represented, overflow bound erased); multi-shot resumptions cannot reuse `AddOnce`, callbacks capturing owners via cells fail `Dup`, Boolean presence `1+1=1` cannot contract `AddOnce`'s spatial split, and dropping verdicts or must-erase data fails `Dispose`.

## Inference, specialization and admission

[The staging contract](metaprogramming.md#evaluation-and-phase-boundaries) keeps compile-time availability independent of `u,v,p,rho`: zero grades/ghosts do not make runtime values static; materialized constants and generated syntax undergo all `Dup`/`Dispose`/ownership checks. First release uses bidirectional checking with fixed modes and bounded refinements; the extensible proposal adds domain IDs and grade variables/constraints (rules propose demands; checked CIC terms prove equalities/orders without promising principal grades or completeness across symbolic multiplication/recursors). Constraint results bind proposition, dictionary, substitutions, and replayable proof (timeouts/unknowns/failed reconstruction leave open goals without weakening exacts to bounds; grade-polymorphic defs check explicit constraints at every public call; runtime indices stay represented and cannot select layout retroactively).

**Derived mode crossing:** following OxCaml's [Data Race Freedom à la Mode](https://doi.org/10.1145/3704859) (POPL 2025) and [Mode Crossing](https://doi.org/10.1145/3828681) (ICFP 2026) (see [the research survey](../assurance/verification-strategy.md#dependent-types-effects-and-ergonomics)), types with checked deeply immutable, authority-free representations (scalars, closed non-dependent pure records, unions, tuples, and immutable snapshots) cross locality, duplication (`Dup`), bulk relocation, and read-sharing modes automatically via structural fixed-point derivation. Authority-bearing handles, exclusive loans, mutable cells, unconstrained generics, and linear tokens never cross modes silently, and every crossing rule remains backed by a checked representation and resource theorem.

Specialization fixes phase, ABI, layout, and erasure pre-emission (mixed represented/erased instantiations need separate ABIs or uniform-erasure theorems; devices carry no runtime grade dictionaries or open-term normalization; source specialization never authorizes composition-time singleton cloning). `SourcePackage` binds source/generated inputs, domain impls/laws, constraints, proofs, implicits/transports, representation, and exact core term (stale core proofs must fail on changed source; erasure preserves results, control, effects, resources, and observations across proof-differing instances). Project applicable source duties into admitted [R-05-132 TAL attributes](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-132) and carry remaining general-domain/dependent-normalization obligations as CIC terms via [the compiler route](../assurance/compiler-route-contract.md).

<a id="q25d-debts-and-acceptance-boundary"></a>

## Proof and qualification obligations

Applies to the selected graded feature over its elaborated image; [the extension plan](../../PLAN.md#language-extensions) owns implementation.

| Obligation | Required artifact and refusal predicate |
| --- | --- |
| `GF-domain` | Domain records, certificate interpreters, cross-domain laws with reconstructable certificates; reject Boolean-to-exact/ownership coercions and unsound order relaxation. |
| `GF-substitution` | Mechanize telescope WF, simultaneous substitution, vector updates, grade substitution, and structural rules over elaborated images; reject stale unsubstituted indices (no independent source reduction premise). |
| `GF-elimination` | Dependent functions, pairs, boxes, sums, and recursors preserve grades and WF motives; include positive asymmetric-field examples with modalities; refuse erased runtime discriminants. |
| `GF-cbv` | Connect demand interpretation to sequenced CBV images, captures, and outcome-indexed exits; prove zero demand preserves effects/failures/verdicts and repeated demand reuses once-evaluated values. |
| `GF-resource` | Instantiate spatial ownership, views, restoration, and kinded authority on the CHERI logic/representation with inhabited packet entry states. |
| `GF-control-mutation` | Compose Capture/Dup/Dispose/Suspend/Transfer/Share with handlers and cells (repeated continuations, hidden cell captures, snapshots, cancellation, fresh `Delta_i`); prove [synchronous conservativity](full-language-review.md#conservative-connection-to-the-synchronous-slice); reject cross-resumption resource reuse. |
| `GF-erasure-source` | Prove phase separation, representation erasure (related behavior across proof-differing instances), and source correspondence under R-05-164/R-05-163; qualify inference diagnostics and stale-source rejection. |
| `GF-target` | Connect source representation, event projections, and obligations through the compiler route to TAL/Sail artifacts (source counts never substitute for final cost or arbitrary-context preservation). |
