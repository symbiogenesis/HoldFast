# HoldFast mathematical elaboration prototype

## Elaboration boundary

The mathematical elaborator consumes schema-2 syntax from the
[Menhir surface parser](parser.md) and translates its supported fragment to
Gallina. Its source terms are interpreted by that translation. The source
digest binds exact input bytes. Kernel replay checks the generated term.
[Source and machine correspondence](../extensions/unified-source-contract.md)

The prototype supports type-valued parameters, definitional reduction and
compositional constants. General descriptor reflection and generated
declarations are part of the [metaprogramming design](../extensions/metaprogramming.md).

## Default grade checking

Ordinary `holdfast-parser elaborate` and locked mathematical builds replay
explicit natural-grade annotations before emitting the checked module. A pure
definition can use `NatExact` or `NatBound` across its graded dependency
closure. The replay checks annotated dependent functions, type-valued
polymorphic definitions over predicative `Type` / `Type<n>` universes,
applications of earlier named definitions, natural indices, natural `let`
bindings and indexed records in the supported fragment. A canonical `Box` can be constructed, opened, and passed or returned across
graded callable and public locked-module interfaces. Its grade and payload
remain distinct in the checked source, and callers of definitions that accept
or return a graded `Box` must themselves be grade-checked.
A grade unsupported by replay produces a located refusal before publication.

Each graded declaration contributes a receipt digest binding the source,
certificate and Rocq support. The locked build also binds the support sources
in its producer identity. The `check-grades` command reports the separate demand
rows and certificate for inspection. A pure graded caller can apply a public
first-order, type-polymorphic, graded-box or higher-order definition imported
under its name, module alias or selected alias, and pass imported graded
definitions as callback values. Replay checks all arguments in the provider's
grade domain. Definitions that accept a graded callback or use a graded `Box`
interface require a grade-checked caller. The caller's receipt binds each
reached provider's locked identity and grade receipt, including providers reached
through a private helper in another module. General grade domains require
further qualification.
[First-release contract](../language/first-release.md#default-graded-checking)

## Pure graded source replay

Run `python tools/run.py holdfast-parser check-grades tools/tests/fixtures/graded-dependent.hf Specialize`
to check a definition and its same-module dependencies in the
[pure graded calculus](../../tools/rocq/graded_pure.v). This investigation accepts
lambdas with typed parameters and pure `Fn` telescopes over `Type`, `Type<n>`,
type variables, `Nat` and `Vec<Nat, n>` with explicit
`@ NatExact(n)` computation allowances. Dependent application indices use
variables, decimal literals and addition. Type arguments use `type ...` or a
bound type variable and enforce predicative universe levels. Applications to
vectors and checked local function values use positional arguments and check the
argument's type, including its grades, up to renaming of binders. This value
rule requires a codomain well formed without the applied binder. The checker
computes type use separately from the computation demand and checks the
specialized codomain.
[Application fixture](../../tools/tests/fixtures/graded-application.hf) ·
[Type-identity fixture](../../tools/tests/fixtures/graded-type-identity.hf)

A natural `let` accepts a stable initializer formed from names, natural
literals and addition. The checking rule counts that initializer once, checks
the local's computation allowance against body demand and substitutes the
initializer into the result type and its type-use row. The rule covers a local
with zero computation use whose value still determines a later vector extent.
[Natural let fixture](../../tools/tests/fixtures/graded-let.hf)

The report binds the source digest and declaration span to the generated Rocq
replay and the digests of its support files. It gives each binder's exact
computation and type demand, the dependencies in its annotation and the
dependencies in the final result type. The replay proves equality with the
reported rows. In `Specialize`, the argument `n + n` contributes zero
computation uses and four type uses of `n`, with two in the returned parameter
type and two in the returned result type.
[Source fixture](../../tools/tests/fixtures/graded-dependent.hf) ·
[Core source replay predicate](../../tools/rocq/graded_core_source.v)

### Bounded natural grades

Run `python tools/run.py holdfast-parser check-grades tools/tests/fixtures/graded-bounded.hf Specialize --domain NatBound`
to replay the same fragment with the checked [`NatBound` admission order](../extensions/graded-foundation.md#dimensions-and-lawful-domains).
Each binder in the selected definition and its dependencies carries an explicit
`@ NatBound(n)` allowance. Rocq checks that the reconstructed computation demand
is at most that allowance. The report's `domain` identifies the order and each
binder's `computation` entry gives its advertised allowance. Application scales
computation demand by the callee's advertised bound. Type-use counts and
telescope dependency rows remain exact under either natural domain.

In `Specialize`, `n` has a zero computation bound and four type uses. The
returned function advertises two uses of `values` and its implementation uses
the argument once. The replay rejects a third use against that bound and catches
changed type-demand rows through its row equality certificate.
[Bounded source fixture](../../tools/tests/fixtures/graded-bounded.hf) ·
[Core source replay predicate](../../tools/rocq/graded_core_source.v)

### Graded box source replay

Run `python tools/run.py holdfast-parser check-grades tools/tests/fixtures/graded-modal.hf PromoteAndOpen`
to replay promotion and an explicitly motivated match over a natural-valued
box. The input declares the ordinary `Box<T, grade q : NatExact>` record with
one `T Value @ q` field. The replay checks that declaration shape. Construction
uses `Box<Nat, q>(value)` with a literal grade and a pure natural index.
Elimination uses `match (box) as whole : TYPE { Box(value) => BODY, }`.
Type indices can observe `whole.Value` or the value of a promoted index.
Pair results let an example expose both a computation and a dependent type.
[Dependent elimination](../extensions/graded-foundation.md#dependent-data-and-elimination)

The checker specializes the motive for both the branch and the actual
scrutinee. It checks the grade of the branch binder and both resulting type
demand rows. The report records the exact source bytes by digest, the box record
dependency, the declaration and binder spans, and the telescope demand rows.
`PromoteAndOpen` uses its input `n` four times in computation and eight times in
the result type. `KeepShape` uses its box only in the next parameter's type and
the result type, with one use in each row.
[Modal source fixture](../../tools/tests/fixtures/graded-modal.hf) ·
[Core source replay predicate](../../tools/rocq/graded_core_source.v)

#### Bounded graded box replay

Run `python tools/run.py holdfast-parser check-grades tools/tests/fixtures/graded-modal-bounded.hf OpenBounded --domain NatBound`
to check the same modal fragment with `record Box<T, grade q : NatBound>` and
explicit `@ NatBound(n)` computation allowances. Rocq checks bounds at the
definition parameters, lambda binders and the match payload. The
`computation` field gives the declared allowance. Motive specialization and
telescope and result type demand retain their exact natural counts.

`OpenBounded` uses its box once with allowance two, reads the payload twice
with allowance three and returns a function that uses its argument once with
allowance two. The result type uses the box twice. `PromoteBounded` scales the
computation demand of `n + n` by the box grade to six and records twelve uses
of `n` in the result type. An over-budget branch, an inconsistent motive or
an altered type-demand row fails replay.
[Bounded modal fixture](../../tools/tests/fixtures/graded-modal-bounded.hf)

### Graded dependent pair replay

Run `python tools/run.py holdfast-parser check-grades tools/tests/fixtures/graded-dependent-pair.hf OpenIndexed`
to check a match on `record Indexed(Nat Length, Vec<Nat, (Length)> Payload)`.
The replay accepts named records with a `Nat` field followed by a natural
vector. The vector extent can use the first field, natural literals and
addition. Construction checks the vector against the extent instantiated at the
first argument. Matching checks the record identity and binds the vector at the
extent instantiated at the first pattern binder. An explicit motive can
project the record's first field. The checker specializes the motive at both
the pattern and the scrutinee and checks the two type-use rows.

One computation grade governs both fields. Under `NatExact` the field counts
must agree. Under `NatBound` the checker uses the least common upper bound
of the two natural counts. This grade scales the scrutinee's computation
row. The motive scales its type-use row independently. `OpenIndexed` checks
two computation uses and two type uses of `packed`. `BuildAndOpen` keeps
the length and payload in the result type with zero computation demand.
Use `OpenBounded --domain NatBound` with the same fixture to replay
an asymmetric body under a shared bound. `OpenStereo` constructs and opens a
record whose vector has extent `Ticks + Ticks + 1`. The extent contributes
two type uses in the vector parameter's annotation, and the specialized motive
contributes two more uses of the index without any computation demand.
[Dependent pair fixture](../../tools/tests/fixtures/graded-dependent-pair.hf) ·
[Elimination rules](../../tools/rocq/graded_modal.v)

### General modal domains, sums and type-grade replay

`holdfast-parser check-grades` (`tools/toolchain/graded_source.py`),
`tools/toolchain/elaborate_graded.py`, and the unified Rocq core
(`tools/rocq/graded_domains.v`, `tools/rocq/graded_core.v`,
`tools/rocq/graded_core_source.v`, `tools/rocq/graded_core_metatheory.v`)
support `JoinDomain` ordered semiring records (`NatExactJoin`, `NatBoundJoin`,
`PresenceJoin`, `LinearDomain`, `AffineDomain`, `SecurityLoHi`, and custom
`domain` declarations) with symbolic `GradeExpr` polynomials, unified `(s, r)`
binder checking enforced inside Rocq across functions, lambdas, `let`
bindings, dependent `Box` / `Sigma` / `Sum` / n-field records, `inductive`
families, `<grade q : D>` grade polymorphism, dependent motives, `Type`/`Type<n>`
universes combined with modal forms, and structured `grade_error` source-span
diagnostics. `holdfast-parser` also exposes `--infer-grades`, `derive-combinator`,
and `synthesize-graded` backed by `graded_inference.py`, `graded_combinators.py`,
and `graded_synthesis.py`, while `elaborate.py` integrates `Q25cb`
zero-type-use `substitute()` skipping and CBV erasure verification alongside
the `graded_metatheory.v`, `graded_semiring.v`, `graded_erasure.v`, and
`graded_cbv_erasure.v` suites.
[Unified graded replay](../../tools/tests/test_holdfast_graded.py#_domains_and_grade_polymorphism) ·
[Q25cb skipping benchmark](../../tools/tests/test_holdfast_graded.py#_q25cb_zero_type_use_skip_and_benchmark) ·
[General modal replay](../../tools/tests/test_holdfast_graded_modal.py#_general_modal_source_replay) ·
[Sums and presence replay](../../tools/tests/test_holdfast_graded_modal.py#_sums_and_presence_modal_replay) ·
[GrTT metatheory suite](../../tools/tests/test_holdfast_graded_metatheory.py) ·
[Protocol client replay](../../tools/tests/test_holdfast_graded_client.py) ·
[CBV erasure replay](../../tools/tests/test_holdfast_graded_cbv.py) ·
[Grade inference replay](../../tools/tests/test_holdfast_graded_inference.py) ·
[Derived combinators replay](../../tools/tests/test_holdfast_graded_combinators.py) ·
[Grade-directed synthesis replay](../../tools/tests/test_holdfast_graded_synthesis.py)

These trials establish demand checking for the projected pure terms. The
[extension qualification](../extensions/graded-foundation.md#extension-selection-and-qualification)
owns source correspondence, evaluation, erasure and domain generalization.

## Client upgrade replay

`python tools/run.py holdfast-parser check-upgrade old.hf new.hf --client client.hf`
compares two revisions of the same named module. Supply additional
`--client` and `--dependency` files as needed. Each client must transitively
import the module under review. A successful replay records the SHA-256 of
both revisions and every fixed source. An elaboration failure identifies the
baseline or candidate, the affected module, and the source position.
Imported executable function bodies and their post-state computations are opaque
to clients. A public mathematical `definition` exports its defining equation;
a `const` function also commits to its static computation. A client may rely
on those computations or an exported proof without acquiring a dependency on
the private body of an ordinary function.

For nested calls to imported functions, the checker can pass the proof of an
inner call's public postcondition to the outer call's guarantee theorem. It
matches instantiated premises against the client's proof context and the
guarantees of calls in the goal, within the ordinary elaboration work budget.
For example, a provider that promises a positive result can feed a function
that requires and preserves positivity. The client proof uses both exported
theorems and can replay with both function bodies opaque. For a function
that returns another function, its contract applies to the original call.
Each proof premise still needs a witness when the client applies the result.

The result covers the supplied clients in this mathematical fragment. The
[release contract](../language/first-release.md#public-api-evolution) also
accounts for separately compiled consumers, ABI, and replayed kernel evidence.

## Supported mathematical increment

Uses the [surface grammar](../language/surface-grammar.md) and supports:

- Generic type and ghost-value telescopes (rigid inside declarations; explicit or fresh inferred instantiation; executable bodies forbid erased values and spec-only ops; math `definition`s may compute with ghost indices).
- Predicative `Type` / `Type<n>` (`0..8`), dependent `Fn` telescopes, type-valued params, and computed types (capture-avoiding substitution; refuses self-typing universes and escaping metas; exact universe match without symbolic universes, implicit cumulativity, or universe inference; `<P : Prop>` for proof polymorphism).
- Bidirectional inference for apps, immutable locals, products, and HOFs (expected types constrain lambdas and omitted generics; `_` requests inference, never axioms; ambiguous/unresolved metas fail; no implicit coercions).
- Calls with positional prefix + optional declaration-order labeled suffix (incl. named `Fn` params; unnamed callable params refuse labels; no reordering, omission, or defaults; sequential dependent instantiation; checks preconditions incl. quantifiers; plain `Fn` args must satisfy preconditions for arbitrary inputs unless wrapped; keeps ownership/loan modes; callers may drop stronger postconditions). Unary contracted callbacks (`Fn(Nat x) -> Nat effects(none) with { requires x <= 5; ensures result == x; } f`) accept effect-free named functions or contracted params whose domain/guarantees imply the contract; contracted aliases, captures, and nonempty effects need the broader callable checker.
- Mathematical `Nat`, `bool`, `char`, `Unit`, products, structural `==`/`!=` (`Nat`, `bool`, `char`, `Unit`, fixed-width ints, tuples, `Vec<T, n>`, `Seq<T>`, non-dependent nominal records/unions), propositional `==`, existentials (`exists (T x, ...) => P(x)`), proof blocks (`assert`, `calc { ... }`, inductive `match`, `by` expr/multi-fact `(h1, h2, ...)` tuple/block using WHNF congruence/symmetry/transitivity, bounded algebraic property/reduction saturation in `saturate_equalizer`, reflective `Nat` semiring polynomial normalization via `NatPolyEqualizer`, propositional forward-chaining/bounded `bool_match` tableau via `PropositionalPrechecker`, and `@Corelib.Init.Logic.ex_intro`), `requires`, and multiple `ensures` on `theorem`/`lemma` (indexed vectors/fins give length-preserving lookup).
- Regular and raw (`"""..."""`) UTF-8 byte strings (`Vec<Nat, n>`, `<= 256` bytes, `ByteLength`, `At`), plus `TextBuilder<capacity>`, `EmptyBuilder`, `Format.Write(ref builder, $"...")`, `Fits`, `Written`, `WrittenBytes` (Menhir parses holes with original span + separate `:x2`/`:x4`/`:x8`/`:d`/`:b` specifiers; supports `Nat`, `bool`, concrete/ASCII `char`, `Vec<Nat, n>` requiring `ValidUtf8(bytes.Model)`; left-to-right once-only eval under builder loan before capacity check; exhaustion sets `Fits` false and preserves prior bytes across subsequent writes).
- Structural recursion on `Nat` (`definition`, `function`, `lemma`, `theorem`) lowering to `fix` with optional `decreases param` on `definition`/`function` (invariant generics + smaller `Succ(...)` binder; non-decreasing, polymorphic-recursive, or unapplied self-refs rejected). Packet C backend erases math/type/unbounded-`Nat` defs and admits acyclic represented calls (recursive code needs stack bounds and lowering rules).
- Exhaustive `match` expressions/statements over `Nat`, `bool`, `char`, `Unit`, `Vec<Nat, n>`, products, and nominal records/unions with `_`, vars, `()`, bool/char/string literals, nested tuples, bounded decimal `Nat`, `Succ(...)`, record/union patterns (with declaration-order `label: pattern`), `as name : Type` motives, and irrefutable `let (a, b)` / `let RecordName(...)` destructuring (subsumed arms refused; lowercase constructor lookalikes flagged; uppercase constructors vs lowercase/`_` binders; bare nullary constructors).
- `if (cond) a else b` (`if_expression`), `expr is Pattern`, flow-refined `if (expr is Pattern)` (binding across `&&` and `then`), block/`assert ... by { ... }` `let Pattern = expr else { return ...; }` (`let_else`), and postfix `expr?` on 2-variant `Option<T>` (`None`, `Some(v)`) / `Result<T, E>` (`Err(e)`, `Ok(v)`) (recorded per resolved type/alias; checked arithmetic uses built-in `Result`; right-hand `&&`/`||` propagation stays guarded: `Some(false && absent?) == Some(false)` and `Some(true || absent?) == Some(true)`; earlier sibling calls/moves/blocks must be extracted to locals first; `if (value is Some(n) && Update(ref count, n))` threads `ref` loans; compound pattern guards in bool/cond values require read-only calls; implication antecedents short-circuit and expose bindings to consequent contracts per [surface scope rules](../language/surface-grammar.md#pattern-test-scope)).
- File-private or locked-package `internal` nonrecursive top-level functions may omit `effects` when all direct user calls have closed footprints (`internal` imports only within same package; tracks transient writes and conservative borrowed reads; closed write bounds preserve untouched `ref` values across opaque modules; `calls` tracks resolved identities across imports/aliases; transparent `definition`s propagate callback positions discharged by empty-effect functions or capture-free lambdas; explicit bounds cover named callback params and higher-order callees; indirect/record/interface/returned-callable calls need explicit bounds; exports and `const` runtime functions keep published bounds; unannotated prototype functions outside the inferred subset remain untracked; [release contract](../language/first-release.md#package-effect-contracts) governs exports).
- Executable bodies forbid bare expression statements discarding `Result<T, E>` (path-sensitive tracking across by-value params, locals, aliases, overwrites, branches, `?`, returns, fields/tuples, exhaustive matches; proof assertions give no runtime handling credit; generic ability constraints and cross-crate accounting remain release duties).
- Nominal `record Name(T1 Field1, ...)` (non-dependent -> `prod`, dependent -> `sigT`/`existT`/`projT1`/`projT2`), zero-cost `distinct Name = T` nominal wrappers (transparent `Definition Name := T.` carrier with identity `.From`/`.Underlying`/`.Value`, optional `invariant`, properties/methods, derived mode crossing, and foreign-interface coherence), and `union Name { ... }`, total read-only `public T Prop => expr;` properties, record methods (implicit `this`, field/property scope, contracts), `.Field`/`.Property`/`.Method(...)` (incl. field paths in dependent types), and `base with { Field = expr, ... }` in declaration order (refusing partial updates that omit dependent fields). Raw carrier supports intermediate `open` states; theorems/postconditions over direct records bind declared invariants as premises (concrete args must establish validity; `out` params gain invariants on init).
- Unicode scalar `char` (`[0, 0x10FFFF]` minus `[0xD800, 0xDFFF]`, escapes `\n`/`\r`/`\t`/`\0`/`\\`/`\'`/`\"`/`\xNN`/`\u{...}`, `<`/`<=`/`>`/`>=`, `Nat(c)`, `u32.From(c)`, `char.From(b)`, `char.TryFrom(x)`), fixed-width ints (`u8`–`u64`, `usize`, `i8`–`i64`, `byte = u8`, `HoldFast.Numerics` aliases `int`/`uint`/`long`/`ulong`, `.Min`/`.Max`/`.Bits`, dec/`0x`/`0b` literals with `_`, contextual literals, negative literals incl. `T.Min`). Partial ops (`+`, `-`, `*`, `/`, `%`, unary `-`, `ShiftLeft`, `ShiftRight`, `WrappingShiftLeft`) discharge preconditions from bounds, `&` masks, widenings, branch guards, and `requires`; total `Wrapping*`, `Saturating*`, `Checked*` (`Result<T, ArithmeticError>`), `Nat(x)`, `T.From(x)`, and `T.TryFrom(x)` reduce on closed values (emitted carriers carry width-indexed words and scalar proofs, incl. open params/quantifiers).
- Explicit-placeholder pipelines `lhs |> rhs` elaborating to single-evaluation call-by-value `let` bindings of `$` (supporting calls, labeled args, expressions, `move $`, and `in $`), plus `using (let|var h = init) { ... }` resource scopes invoking `IDispose<T>.Dispose(in h) -> Unit` in LIFO order across fallthrough, early `return`, and `?` propagation (skipping `Dispose` when `?` exits from `init`, and rejecting escaping borrows, moves/returns of managed handles, and `break`/`continue` across `using` boundaries).
- `holdfast-parser check-arithmetic SOURCE` emits and replays per-site theorems proving checked primitives return `Ok` of the ordinary op (`WrappingShiftLeft` checks count). Closed operands cover all widths; single symbolic bytes check all 256 cases; wider/two-symbolic-operand structural lemmas cover unsigned/signed `+`/`-`, signed `-`, unsigned/signed `/` & `%` (checking nonzero divisor and signed `MIN / -1`), right shift, and `WrappingShiftLeft` under word/literal order/equality guards (two's-complement sign/no-overflow proofs for signed `+`/`-`; equality/inequality for other signed ops; native qualification checks against independent statements, `Print Assumptions`, and `rocqchk`; compound/unsupported operands receive no verdict).
- Suffix framing tracks writes/fills/restored slices across branches (proving offset + max-count fits below suffix via one capacity-invariant binary-int theorem at e.g. $N=4$ and $N=10^9$).
- Typed `const` (`Nat`, `bool`, `char`, `Unit`, target words, [frozen tables](#frozen-static-tables)) at module/local scope per [required-static contract](../language/surface-grammar.md#required-static-constants) (earlier constants + total pure calls on static args/params; dead-branch outer runtime/unmarked ghost/generic refs refused pre-reduction; no runtime fallback; `Limit` indexes `Vec<Nat, Limit>`, `Limit()` rejected; machine types keep target prerequisites). `const` functions remain runtime-callable; `const` params enforce static args across telescopes, partial apps, and HOFs (closed instantiations reduce within bounded budget; logical templates give no backend storage/erasure proof).
- Type aliases, definitions, returning pure functions, theorems/lemmas, and immutable proof locals (`==` is Boolean in expressions vs propositional in theorems; equality proofs are first-class).
- `Span<byte>` carrier (`in`/`ref`, `.Base`, `.Length`, `.Tag`, `.PermRead`, `.PermWrite`, `.CanRead`, `.CanWrite`, `Span.AllocZeroed`/`Read`/`Write`/`Fill`/`Slice`/`ReadOnly`/`Invalidate`/`Disjoint`/`CopyPrefix`/`Restore`), `requires`, `ensures` (`result`), and `restores param` (bare param checks return descriptor preservation; general `restores` predicates report unsupported; immediate post-state uses `ensures`). [First-slice qualification](../language/first-release.md#first-slice-qualification)
- Pure sequences (`Seq<T>`, `Seq.Empty`, `Seq.Singleton`, `.Count`, `.At`, `.Update`, `.Append`, `.Take`, `.Skip`, `.Slice`, `.Contains`, `.All`, `.Any`), `.Model` on `Vec`/`Span`/`Slots`/`Seq`, `expr[idx]`, and `old(...)` (proved indices into nonempty `Vec` lower to `Fin`/total `At`; `Fin<n>` indexes symbolic `Vec`; sequence/slot reads work on nonempty models; unavailable witnesses fail at source site).
- Mutable locals (`var`, `var` patterns, `var ... else`), assignments (`=`, `+=`, `-=`, `*=`, `/=`, `%=`) to vars, fields, and `target[idx]`, non-terminal `if` state threading, and bounded `foreach (let i in start..end)`, `foreach (let | in | ref x in coll)`, and `while (cond)` with `invariant`, `decreases`, `break`, `continue`, and freeze checks (symbolic ranges use Gallina folds/exact counters/contiguous fills; symbolic `while` uses single decreasing bound as fuel; unsupported symbolic early exits/writebacks need explicit control flow).
- Named/unnamed `record` invariants (`invariant [Clause:] expr`) checked on construction/`with`/field writes, plus `open (ref target, ...) lifts Clause, ... { ... }` barring escape/early exit until restored.
- Vacant-slot `Slots<T, capacity>` (`AllocVacant`, `Write`, `Read`, `Disjoint`, `RepEqual`, `LivePrefix`, `VacantRange`, `VacantSuffix`, `PrefixModel`) and two-step relocation (`CopyRepresentation` + `TransferType<T>`) with $O(1)$ capacity-independent region checks (`LivePrefix` -> read/count/length; `VacantRange` -> write/bounds; readable-source relocation also needs write permission; publishing live destination prefix needs read permission; cross-capacity move checks liveness, both vacancies, and prefix equality).
- `out var name` in standalone `Unit` calls introduces fresh mutable locals typed/valued from callee updates (abstract interface outputs need concrete updates).
- `out T` parameters and `out target` call args with path-sensitive init tracking (`if`/`else`, `match`, `let_else`/`var_else`, loops), barring pre-init reads, partial mutation, `old(...)`, and early returns/`?`, binding `ensures` to final value.
- Local `let r = in/ref target` (locals + disjoint fields `target.Field`), `in`/`ref T` value loans, `owned T` (`move expr`, `move base with { ... }`), closed `effects` (`reads`, `writes`, `calls`, `effects none`), named `effect Name = ... [canceled by ...];` sets/unions, negative `!` prohibitions, and local `effects (...) { ... }` confinement blocks connected to [`loans.py`](../../tools/toolchain/loans.py) and [borrow promotion](../language/core-design.md#borrow-analysis-promotion) (suspending overlapping parent/field access until last use while permitting disjoint sibling fields; requiring `move` for `owned` and rejecting `use-after-owner-move`, `partial-owner-move-unsupported`, `move-through-loan-unsupported`; invalidating mutable-place facts while keeping immutable `let snap = ...`, `old(...)`, and disjoint-field facts).
- [Two-phase borrowing](../language/core-design.md#two-phase-receiver-borrows) for implicit `ref` interface receivers and `slots.Write(...)` (permitting reads during arg eval, checking retained overlaps at activation; explicit `ref`/`out` keep ordinary timing).
- Explicit nonoverlapping `interface` / `impl` with `requires`/`ensures` and abstract `lemma`/`theorem` laws, unification coherence/overlap refusal, blanket/computed-head refusal, Liskov checks, law proof checks, Gallina emission, `where T : ISized<T>` dictionary passing, and `T.Size(in value)` / `value.Size()` dispatch. [Interface resolution](../language/first-release.md#interface-constraints-and-dispatch)
- Multi-module `import Module.Path;` (`elaborate(..., imports=...)`, `elaborate_package(modules)`) with topological sort, cycle refusal, `public`/`private` enforcement, underscore-safe module names (`A.B` -> `HoldFast_A_B`, `A_B` -> `HoldFastEncoded_415f42`), defining-module provenance across private transitive helpers, and plain/aliased/selective imports.

Callables keep explicit arity (`Fn() -> Unit` ≠ `Fn(Unit) -> Unit`). Inference uses bounded structural unification (with occurs/scope checks) and bounded conversion; residual obligations need explicit proofs, and exhaustion/unsupported constructs/unfinished proofs fail at source sites.

Implementation spans [`elaborate.py`](../../tools/toolchain/elaborate.py) and submodules [`elaborate_types.py`](../../tools/toolchain/elaborate_types.py), [`elaborate_protocol.py`](../../tools/toolchain/elaborate_protocol.py), [`elaborate_strings.py`](../../tools/toolchain/elaborate_strings.py), [`elaborate_whnf.py`](../../tools/toolchain/elaborate_whnf.py), [`elaborate_intrinsics.py`](../../tools/toolchain/elaborate_intrinsics.py), [`elaborate_solver.py`](../../tools/toolchain/elaborate_solver.py), [`elaborate_proofs.py`](../../tools/toolchain/elaborate_proofs.py), [`elaborate_patterns.py`](../../tools/toolchain/elaborate_patterns.py), [`elaborate_statements.py`](../../tools/toolchain/elaborate_statements.py), and [`elaborate_declarations.py`](../../tools/toolchain/elaborate_declarations.py), enforcing finite source/depth/work/reduction/output limits, pre-emission schema/digest/span/identifier validation, hygienic naming, and zero raw-Gallina/axiom/hole escapes.

## Natural arithmetic

Checks [Nat requirements](../language/reference.md#expressions-and-operators) at `-`, `/`, `%` (incl. `(-)(a, b)`) using closed values, branch guards, and `requires` (e.g., `requires used <= total` for `total - used`), stopping on unproved premises (`Nat.SaturatingSub(a, b)` is total). Unconstrained function values wrap in a body-checking lambda.

## Frozen static tables

Mathematical `const` supports length-indexed static scalar/nested vectors and UTF-8 string `Vec<Nat, n>` (`"é"` -> `[195, 169]`; target `usize` is 64-bit). Initializers require empty transitive effects (incl. helpers, receivers, both conditional branches, and HOF callbacks), budget <= 64 vector slots across all dimensions (two 31-element rows = 64; empty = 0), and symbolic deferral until closed specialization. Emits `_freeze` equality (checked by Rocq conversion) plus `holdfast_freeze_observe` transport; [locked builds](#locked-mathematical-packages) bind frontend, parser, target, and transitive sources.

## Commands and acceptance

[Playground console](playground.md#dependent-mathematics-increment) uses the bounded closed-expression evaluator. `holdfast-parser elaborate SOURCE` parses/elaborates via guest dispatch (`--output FILE` publishes atomically after validation, refusing aliases and preserving targets on error; `--help` lists limits).

`holdfast-parser elaborate-qualify` builds the pinned parser, elaborates examples + independent positives/negatives, compiles with locked Rocq, and runs `rocqchk`, binding source/elaborator/parser/local-checker/auditor/Python/version digests (late input edits withdraw receipts; assumption audits accept only recognized closed-context output; negatives must fail semantically, not at parse/tooling).

Each `assert` (incl. `calc` and `by` steps) emits a span-indexed Gallina definition audited for assumptions even if unused later. The `Nat` bound checker weakens local/branch comparisons (`if (n < 5)` -> `n <= 4` true, `n > 3` false), joins transitivity (`n < m` + false `k < m` -> `n < k`), preserves strict/non-strict bounds under common addends via Rocq monotonicity proofs, and cancels common addends (`base + used < base + limit` -> `used < limit` true, `limit <= used` false) up to 256 candidate joins per assertion (exhaustion reports outstanding proposition at source, provable with `by`). Equality and propositional goals additionally run `VersionedEGraph.saturate_equalizer`, reflective `NatPolyEqualizer`, and `PropositionalPrechecker`, while multi-fact `by (h1, h2, ...)` discharges goals using the supplied facts, all emitting axiom-free Rocq terms.

Host tests cover polymorphism, inference, dependent substitution, vector lengths/`At`, HOF constraints, proof composition, conversion, determinism, hygiene, negatives (unequal indices, wrong domains, false proofs, non-propositions, universes, occurs/scope, ambiguous holes, missing bodies, stale/bad protocol, unsupported syntax, limits), and atomic CLI behavior; native qualification runs real parser + kernel replay.

## Named goals

Native checking reports `?name` sites (`assert n == 4 by ?bound;` -> `Eq(Nat, n, 4)`) with expected type, locals, branch facts, local loans, and return type (checked via fresh metas for missing values; any goal blocks compilation, eval, and package builds; siblings can unify types or report unavailable; earlier blocking errors leave partial inspection up to 128 sites and 65,536 UTF-8 bytes). [Playground reports](playground.md#browser-behavior) follow active buffers; copy/cleanup/returned-view judgments keep their [resource obligations](../language/core-design.md#typed-holes-and-invalidation).

## Locked mathematical packages

Batch builds compose `math-2` packages on `rocq-gallina` ([import rules](../language/first-release.md#modules-and-packages)) from `<name>/<revision>/holdfast-package.toml` (names, edition, target, relative `modules`/`dependencies`/`inputs`; [example](../../examples/packages/scale/v1/holdfast-package.toml)):

```console
python tools/run.py holdfast-parser lock-package examples/packages scale v1 --output scale.lock
python tools/run.py holdfast-parser build-package examples/packages scale.lock --output scale.json
```

Locks bind manifests, file digests, modules, revisions, dependencies (single revision per diamond; imports restricted to self, direct deps, and `HoldFast.Numerics`), parser/elaborator, and target config; package-instance digests stamp nominal declarations across sibling/transitive closures. Builds re-read inputs before emitting ordered module/lock/source/instance/Gallina digests (optional bundle maps full module names to Gallina files; missing revisions, undeclared imports, owner collisions, cycles, and stale locks fail; root packages enforce [default authoring checks](authoring-tools.md#locked-package-authoring); capped at 64 packages, 256 files, 16 MiB inputs, 32 MiB Gallina). [Package contract](../language/first-release.md#modules-and-packages)

## Try the mathematical fragment

[Bounded word counter](../../examples/word_count.hf) borrows validated UTF-8 per lookup, allocates new keys in a 3-byte builder (`red`, `red`, `blue` -> 2 `red`s + `KeyBytesFull` intact; other cases test scratch reuse, 2-slot exhaustion, and 2-byte `é`), replayed by `elaborate-qualify` ([release contract](../language/first-release.md) governs represented storage).

Run from repo root (`python3` on Linux):

```console
python tools/run.py holdfast-parser elaborate examples/dependent.hf
python tools/run.py holdfast-parser elaborate-qualify
```

[Dependent example](../../examples/dependent.hf) combines generic identity, HOFs, inferred vector lengths, `Fin` lookup, dependent callables, and equality proofs (`elaborate` needs locked parser; `elaborate-qualify` adds locked Rocq kernel verdict). Generic `<TElement, ghost Nat length>` defaults to `Type` and infers arguments (`_` for holes; contextual `value => ...` / `(l, r) => ...` lambdas; `=> expr;` bodies; `Fn(Nat length, Vec<Nat, length> values) -> Vec<Nat, length>`). `Fst`/`Snd` project products; `Vec<TElement, length>` (`VNil`, `VCons`, `Fin`, `FZero`, `FSucc`, `At`) is purely mathematical (use `Succ(length)` / `1 + length` for definitional successor; arbitrary math needs theorems); `proof` blocks use `assert` / `by` lemma steps; concrete projections/lookups compute, and `type[Eq<T>(left, right)]` passes proof values.
