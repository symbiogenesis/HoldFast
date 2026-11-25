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

The elaborator uses the [surface grammar](../language/surface-grammar.md)
and supports the following features.

- Generic type and stable ghost-value telescopes, explicit generic application
  and fresh inferred instantiation at each use. Generic variables in a
  declaration are rigid; inference cannot specialize its promised signature.
  Executable function bodies reject dependencies on erased values and on
  specification-only operations through helpers, properties and imports.
  A mathematical definition may compute with its ghost index in proofs.
- Numeric predicative universes `Type` and `Type<n>` for levels zero through
  eight, dependent `Fn` telescopes, type-valued parameters and
  computed types. Substitution preserves dependency and avoids capture. Reject
  self-typing universes and escaping inference variables. Symbolic universe
  declarations, implicit cumulativity and universe-level inference remain
  unsupported; universe levels match exactly. Use `<P : Prop>` for a
  proof-polymorphic routine.
- Bidirectional inference for applications, immutable locals, products and
  higher-order functions. Expected types constrain lambdas and omitted generic
  arguments. An annotation hole `_` requests inference, never an axiom. Ambiguous
  or unresolved variables are errors. No implicit numeric or option coercions.
- Calls use positional arguments or a positional prefix followed by a labeled
  suffix. Each label must match the next declared value parameter, including
  named `Fn` parameters; unnamed callable parameters accept no labels. No
  argument reordering, omission or defaults are inferred. Dependent later
  parameters are instantiated in declaration order before their arguments are
  checked, preserving complete telescope substitution. Recursive and direct calls
  check every declared precondition, including quantified propositions. A
  callable can be passed as a plain `Fn` when its preconditions hold for fresh,
  arbitrary arguments of the destination signature. An explicit wrapper can
  establish a remaining precondition. The signature preserves each parameter's
  ownership and loan mode. A caller may discard a stronger return guarantee.
  Top-level functions and definitions can take a named, unary scalar callback
  such as `Fn(Nat x) -> Nat effects(none) with { requires x <= 5; ensures result == x; } f`.
  Its argument must be a named function with checked empty effects or another
  contracted parameter. The required input domain must imply the argument's
  preconditions. Its guarantees under that domain must establish the promised
  result. Invocation checks the input obligation and records the result fact.
  This increment supports Boolean predicates over the callback's scalar
  argument, result and literals. Contracted callable aliases, captures and
  nonempty effect bounds require the broader callable-type checker.
- Mathematical `Nat`, `bool`, `char`, `Unit`, products, decidable structural
  Boolean equality (`==`, `!=`) over `Nat`, `bool`, `char`, `Unit`, fixed-width
  integers, tuples, `Vec<T, n>`, `Seq<T>` and non-dependent nominal `record` and
  `union` types, propositional equality and existential
  (`exists (T x, ...) => P(x)`) propositions, and proof blocks with `assert`
  statements, calculational `calc { ... }` transitive equality chains, inductive
  `match` case analysis, and `by` expression or block justifications (supporting
  WHNF-aware congruence, symmetry and transitivity equational rewriting as well
  as existential witness introduction via `@Corelib.Init.Logic.ex_intro`), plus
  `requires` preconditions and multiple `ensures` clauses on `theorem` and `lemma`
  declarations. Indexed vectors and finite indices provide a
  concrete dependent collection boundary, including length preservation and safe
  lookup.
- Regular and multi-quote raw string literals (`"""..."""`) elaborating to
  UTF-8 byte vectors `Vec<Nat, n>` (bounded by 256 bytes) with `ByteLength`
  and `At` lookup, and `TextBuilder<capacity>` / `EmptyBuilder` /
  `Format.Write(ref builder, $"...")` / `Fits` / `Written` modeling allocation-free
  checked formatting. Menhir parses each interpolation hole with the ordinary
  expression production and retains its original byte span. A trailing format
  specifier is separate from the expression. Holes support `Nat`, `bool`, `char`
  when concrete or proved ASCII, and `Vec<Nat, n>`. Numeric holes accept
  specifiers including `:x2`, `:x4`, `:x8`, `:d` and `:b`. The checker
  checks target-buffer aliasing and requires `ValidUtf8(bytes.Model)` for a byte-vector hole. `WrittenBytes(builder)` exposes the exact committed byte sequence and `Written(builder)` counts it. Holes evaluate once from left to right. Their effects on other places occur before the capacity check. A write appends the whole formatted sequence on success. Exhaustion sets `Fits` to false and preserves the previous bytes. Later writes to that failed builder preserve the same bytes.
- Structural recursion over `Nat` parameters on `definition`, `function`,
  `lemma` and `theorem` declarations, elaborated to Gallina `fix` terms with
  optional explicit `decreases parameter` contracts on `definition` and
  `function` declarations. Recursive calls must supply invariant generic
  arguments and pass a structurally smaller `Succ(...)` pattern binder for the
  decreasing parameter; non-decreasing, polymorphic-recursive or unapplied
  self-references are rejected.
  The packet backend erases mathematical declarations, including type-valued
  functions and recursion over unbounded naturals. For each selected executable
  declaration it checks the elaborator's resolved recursion information before
  emitting C. Recursive code needs a stack bound and lowering rule. The packet
  profile currently admits acyclic calls among its represented functions.
- Exhaustive `match` expressions and returning statement `match` over `Nat`,
  `bool`, `char`, `Unit`, `Vec<Nat, n>`, products and nominal `record` and `union`
  types, with wildcard (`_`), variable, `()`, Boolean literal, character literal
  (`'a'`), string literal (`"..."`), nested tuple, decimal natural (bounded by
  structural unrolling), `Succ(...)`, record and union constructor patterns (supporting
  optional declaration-order `label: pattern` arguments), optional dependent
  `as name : Type` motives, and irrefutable `let (a, b) = ...` or
  `let RecordName(...) = ...` destructuring in blocks and `let ... in ...`
  expressions. A later arm wholly covered by a single earlier pattern is refused;
  a lowercase catch-all resembling a visible constructor identifies the likely spelling.
  Constructors and binders in patterns are distinguished by token
  shape (uppercase initial letter for constructors and lowercase letter or `_`
  for binders), and nullary constructors are written bare without `()`.
- Conditional `if (cond) a else b` expressions (`if_expression`), Boolean
  `expr is Pattern` tests, flow-refined `if (expr is Pattern)` statements and
  expressions (binding `Pattern`'s variables in later `&&` operands and the `then` branch), scoped
  early-exit `let Pattern = expr else { return ...; }` (`let_else`) guards in
  blocks and `assert ... by { ... }` proof blocks, and postfix `expr?`
  early-return propagation over 2-variant `Option<T>` (`None`, `Some(v)`) and
  `Result<T, E>` (`Err(e)`, `Ok(v)`) unions. The elaborator records the
  success and failure cases on the resolved type declaration. An alias retains
  this capability. A differently named union with similar constructors has its
  own identity. Checked arithmetic always produces the built-in result type.
  Propagation inside the right
  operand of `&&` or `||` remains under that operand's Boolean guard:
  `Some(false && absent?)` returns `Some(false)` and
  `Some(true || absent?)` returns `Some(true)` when `absent` is `None`.
  Left-operand and nested propagation preserve the same evaluation order.
  Extraction across earlier sibling values refuses when either sibling contains
  a call, ownership transfer or block evaluation; write the earlier computation
  as an explicit local first. The dedicated `&&`/`||` guard evaluates its left
  operand once before deciding whether to propagate from its right operand.
  A statement such as `if (value is Some(n) && Update(ref count, n))` threads
  the mutable loan through the successful path. A compound pattern guard used
  as a Boolean value or in a conditional expression requires read-only calls.
  Propagating such a Boolean value with `?` in a function with borrowed outputs
  requires explicit control flow.
  A pattern on the true path of an implication introduces its bindings in
  the consequent, including when the consequent is a contract proposition.
  The antecedent short-circuits on its first false conjunct. The
  [surface scope rules](../language/surface-grammar.md#pattern-test-scope)
  define which patterns contribute bindings.
- A file-private or locked-package `internal` nonrecursive top-level function
  can omit its `effects` clause when every direct user-function call has a
  closed footprint. Only sibling modules of the same locked package instance
  can import the `internal` function. Inference includes transient writes and
  uses the same conservative accounting for borrowed reads as an explicit
  bound. A closed write bound preserves the caller's current value for any
  `ref` argument outside that bound, including calls across an opaque module
  interface. Named `calls` entries carry the identity of the resolved
  declaration or parameter through imports and aliases. A transparent
  mathematical definition records the positions of callbacks it invokes,
  including forwarding through another definition. A fully applied call can
  discharge those positions with a named function checked to have empty
  effects, or with a capture-free lambda over its parameters, literals and
  built-in operators. An explicit
  caller bound can name the actual callback parameter. Naming a higher-order
  helper also requires accounting for each callback supplied to it. Unresolved
  indirect calls, record or interface dispatch, and invocation of a returned
  callable require a separate checked bound. Exported functions, including
  `const` functions callable at runtime, keep their published bounds. The
  prototype also accepts unannotated functions outside the inferred subset
  with an untracked footprint. The [release package contract](../language/first-release.md#package-effect-contracts)
  requires explicit bounds at exports and specifies package-internal inference.
- In executable bodies, a bare expression statement cannot discard the built-in
  `Result<T, E>`. The source control-flow check follows named by-value parameters
  and inferred or annotated locals through aliases, overwrites, branches, early
  `?` exits and returns. A constructor test or match examines a result; a return
  or by-value call forwards it. Proof-only assertions give no runtime handling
  credit. Record fields and tuple components carry separate obligations. An
  exhaustive union match transfers obligations to the selected payload
  bindings. Generic ability constraints and complete resource accounting
  across separately compiled interfaces remain release obligations.
- Nominal `record Name(T1 Field1, ...)` and `union Name { Case1(...); ... }`
  declarations with primary-constructor fields and tagged sum variants (lowering
  non-dependent field telescopes to `@Corelib.Init.Datatypes.prod` and dependent
  field telescopes where later field types depend on earlier fields to
  `@Corelib.Init.Specif.sigT` / `existT` / `projT1` / `projT2`), total
  read-only expression properties (`public T Prop => expr;`) on records and at
  module scope, record member methods (`definition` and `function` declarations
  inside `record { ... }` with implicit `this` receiver, field/property scope, and
  `requires` and `ensures` contracts), `.Field`, `.Property` and
  `.Method(...)` member access (including record field paths in dependent type
  arguments), and postfix `base with { Field = expr, ... }` record updates
  evaluated in declaration order (refusing partial updates to an index field when
  a dependent field is not also updated).
  The raw record carrier supports intermediate values in an `open` block.
  A theorem or exported postcondition over a direct record input binds each
  declared invariant as a proof premise. A proof invoking that theorem on a
  concrete record must supply or establish its validity. An `out` parameter
  acquires its invariants when initialized.
- Unicode scalar values (`char` in `[0, 0x10FFFF]` excluding surrogates
  `[0xD800, 0xDFFF]`, character literals `'a'` with `\n`, `\r`, `\t`, `\0`, `\\`,
  `\'`, `\"`, `\xNN` and `\u{...}` escapes, relational comparisons `<`, `<=`, `>`,
  `>=`, and explicit conversions `Nat(c)`, `u32.From(c)`, `char.From(b)` from
  `u8`/`byte` and `char.TryFrom(x)` returning `Result<char, ConversionError>`),
  fixed-width represented integer types (`u8`, `u16`, `u32`, `u64`, `usize`,
  `i8`, `i16`, `i32`, `i64` and `byte = u8`) and `import HoldFast.Numerics;`
  aliases (`int = i32`, `uint = u32`, `long = i64`, `ulong = u64`, also
  available qualified as `HoldFast.Numerics.int`), with associated constants
  `T.Min`, `T.Max` and `T.Bits`, decimal/hexadecimal (`0x...`)/binary (`0b...`)
  literals with `_` separators, suffixed or expected-type contextual literals,
  and syntactic negative signed literals (admitting `T.Min`). Ordinary `+`, `-`,
  `*`, `/`, `%`, unary `-`, `ShiftLeft`, `ShiftRight` and `WrappingShiftLeft`
  enforce explicit range, nonzero-divisor and shift-count (`usize < T.Bits`)
  preconditions discharged from concrete bounds, bitwise masks (`&`), widening
  conversions, branch conditions and parameterized `requires` contracts. Total
  modular (`WrappingAdd`, `WrappingSub`, `WrappingMul`, `WrappingNeg`,
  `WrappingShiftLeft`), saturating (`SaturatingAdd`, `SaturatingSub`,
  `SaturatingMul`, `SaturatingNeg`) and checked (`CheckedAdd`, `CheckedSub`,
  `CheckedMul`, `CheckedDiv`, `CheckedRem`, `CheckedNeg`, `CheckedShiftLeft`,
  `CheckedShiftRight` returning `Result<T, ArithmeticError>`) operations and
  explicit conversions (`Nat(x)` for unsigned types, `T.From(x)` for lossless
  widening and `T.TryFrom(x)` returning `Result<T, ConversionError>`) reduce on
  closed values. The emitted integer carrier contains a word indexed by the
  width of its tag. Every inhabitant of the emitted character carrier carries
  a proof that its code satisfies the Unicode scalar test. These restrictions
  also apply to open parameters and quantified variables.
- `python tools/run.py holdfast-parser check-arithmetic SOURCE` emits and replays a
  theorem at each elaborated partial word operation. The theorem states that
  the checked primitive returns `Ok` of the ordinary primitive's result.
  Wrapping left shift checks its count and permits discarded high bits.
  Closed operands support every represented width. With one symbolic byte,
  signed or unsigned, Rocq checks all 256 words under the comparison premises
  printed in the theorem. For wider words or two symbolic operands, structural
  lemmas connect the actual bits, comparisons and overflow checks to binary
  integer arithmetic. These lemmas cover signed and unsigned addition and subtraction,
  signed negation, signed and unsigned division and remainder, right shift and
  wrapping left shift. Operands can be word variables or literals. Guards can
  compare unsigned operands for order or equality. Signed addition and subtraction
  also use signed order, equality and inequality guards. Their proofs interpret
  the sign bit and rule out overflow in the emitted two's-complement operation.
  Other signed operations can use equality and inequality guards.
  Signed division checks both a nonzero divisor and
  the minimum-value divided by minus-one case.
  The native qualification applies each source-span theorem to an independent
  statement about the emitted function under its source guards, audits its
  assumptions and runs `rocqchk`. Other symbolic operations, compound operands
  and bounds that the kernel proof cannot establish receive no replay verdict.
- Suffix framing over byte stores follows writes, fills and restored sliced
  copies through conditional branches. For a symbolic count bounded by a source
  fact, the checker proves a suffix bound when the mathematical sum of the
  constant offset and maximum count fits below the suffix. A Rocq theorem
  relates unsigned word comparison and addition to binary integers. Its
  application takes the same form for every count bound, including a billion.
- Typed `const` values of `Nat`, `bool`, `char`, `Unit`, target words and
  [bounded vectors](#frozen-static-tables), at module or local scope,
  under the [required-static contract](../language/surface-grammar.md#required-static-constants).
  Initializers use earlier constants and admitted total pure calls with static
  arguments and explicit static parameters; unmarked outer runtime parameters,
  ordinary locals and generic or ghost indices are refused before reduction,
  including dead or ignored dependencies.
  Internal locals of a pure call evaluated with static arguments remain part of
  that evaluation. Emit the bounded evaluated value, with no runtime fallback.
  A constant can index `Vec<Nat, Limit>` directly; it is a value, so `Limit()`
  is not a constant access. Represented machine types retain target prerequisites.
- Constant-compatible function modifiers and `const` value parameters use the
  same [compositional contract](../language/surface-grammar.md#required-static-constants).
  The former preserves runtime calls; the latter requires static arguments and
  supports symbolic local constant computation. Static parameter requirements
  follow dependent function telescopes, partial applications and higher-order
  uses. A closed instantiation computes its demanded constants under the existing
  bounded reducer. Logical templates retain their interpretation in CIC; no
  production backend or runtime-storage guarantee is supplied by these terms.
- Aliases, definitions, returning pure functions, theorem/lemma bodies and
  immutable proof locals. Equality proofs are ordinary first-class values;
  theorem bodies must inhabit the declared proposition. Ordinary expression
  equality remains Boolean, while theorem equality denotes a proposition.
- Concrete `Span<byte>` capability-and-memory carrier (`in Span<byte>` and
  `ref Span<byte>` parameter modes, `.Base`, `.Length`, `.Tag`, `.PermRead`,
  `.PermWrite`, `.CanRead` and `.CanWrite` metadata, and `Span.AllocZeroed`,
  `Span.Read`, `Span.Write`, `Span.Fill`, `Span.Slice`, `Span.ReadOnly`,
  `Span.Invalidate`, `Span.Disjoint`, `Span.CopyPrefix` and `Span.Restore`),
  together with `requires`, `ensures` (with `result` bound to the body) and
  `restores param` contract obligations on `definition` and `function`
  declarations. The bare parameter form checks descriptor preservation at call
  return. A general restoration predicate describes the lender when a returned
  loan ends and requires a deferred witness. The prototype reports this form
  as unsupported. Use `ensures` for a predicate over the immediate post-state.
  See the [first-slice qualification](../language/first-release.md#first-slice-qualification).
- Pure sequence vocabulary (`Seq<T>`, `Seq.Empty`, `Seq.Singleton`, `.Count`,
  `.At`, `.Update`, `.Append`, `.Take`, `.Skip`, `.Slice`, `.Contains` over
  structurally equatable element types, `.All` and `.Any`), `.Model` domain views on
  `Vec<T, n>`, `Span<byte>`, `Slots<T, capacity>` and `Seq<T>`, postfix indexing
  `expr[idx]` on `Span<byte>`, `Slots<T, capacity>`, `Seq<T>` and `Vec<T, n>`, and
  pre-state `old(...)` expressions inside callable contracts.
  A proved numeric index into a visibly nonempty vector lowers to a finite index
  and total `At`, including for abstract element types. An explicit `Fin<n>`
  indexes a vector of symbolic length. Sequence and slot reads can use a
  represented element of a nonempty model. A lookup requiring an unavailable
  element witness reports the limitation at its source location.
- Mutable local bindings (`var`, `var` pattern bindings and `var ... else`),
  assignments (`=`, `+=`, `-=`, `*=`, `/=`, `%=`) to mutable variables, record
  fields and indexed collections (`target[idx] = val` on `Span<byte>`,
  `Slots<T, capacity>`, `Seq<T>` and `Vec<T, n>`), non-terminal `if` state
  threading, and bounded range (`foreach (let i in start..end)`), collection
  (`foreach (let | in | ref x in coll)`) and `while (cond)` loops with `invariant`
  verification, `decreases` termination measures, `break`, `continue` and
  collection-freeze checks. Symbolic ranges accumulate state with a Gallina
  fold or an exact counter or contiguous fill. Symbolic while loops can use
  a single nonnegative decreasing bound as fuel. Unsupported symbolic early
  exits and mutable element writeback require explicit control flow.
- Named and unnamed `record` invariants (`invariant [Clause:] expr`), verified
  on construction, `with` updates and field mutations, together with selective
  invariant lifting (`open (ref target, ...) lifts Clause, ... { ... }`) that
  refuses target escape or early exit until lifted clauses are restored at scope
  exit.
- Vacant-slot storage (`Slots<T, capacity>`, `Slots.AllocVacant`, `Slots.Write`,
  `Slots.Read`, `Slots.Disjoint`, `Slots.RepEqual`, `LivePrefix`,
  `VacantRange`, `VacantSuffix` and `PrefixModel`) and two-step bulk relocation
  (`CopyRepresentation` followed by `TransferType<T>`) with capacity-independent
  region verification. A live prefix gives read permission, its live count and the
  exact length of its logical sequence. A vacant range gives write permission and
  bounds. Relocating a readable source additionally requires write permission on
  that source. Publishing the destination as a live prefix requires read permission
  there, even after its representation has been copied. For a move between
  independently quantified capacities, the kernel checks destination liveness,
  both vacancy postconditions and equality of the destination prefix to the
  source prefix at entry.
- Inline `out var name` declarations in standalone `Unit` calls introduce
  fresh mutable locals after the call returns. Each local takes its type from
  its output parameter and its value from the checked callee update. Calls
  through an abstract interface output require a concrete update before they
  can introduce a local this way.
- Write-only initialization loan parameters (`out T`) and `out target` call-site
  arguments, with path-sensitive initialization tracking across `if`/`else`,
  `match`, `let_else`/`var_else` and loops, refusal of reading, partially
  mutating (`+=`, `.Field =`, `[idx] =`), `old(...)`, or returning/propagating
  (`?`) before every `out` parameter is initialized on all normal return paths,
  and immediate postcondition (`ensures`) binding to the final initialized
  value.
- Source-bound local borrow bindings (`let r = in target;` and `let r = ref target;`
  over local variables and disjoint record fields `target.Field`), general
  `in T` and `ref T` runtime value loans, consuming ownership (`owned T`
  parameters and data fields with explicit `move expr` transfers and consuming
  record updates `move base with { ... }`), and closed `effects` footprints
  (`reads(...)`, `writes(...)`, `calls(...)`, and `effects none`), connected to
  path-sensitive loan-end inference ([`loans.py`](../../tools/toolchain/loans.py))
  and dependent mutation-invalidation rules under the
  [borrow-analysis promotion contract](../language/core-design.md#borrow-analysis-promotion):
  local `in` and `ref` borrows suspend conflicting parent/field reads, writes and
  moves until the borrow's path-sensitive last use while permitting simultaneous
  borrows and mutations of disjoint sibling record fields (`r.Low` versus `r.High`),
  `owned` parameters require explicit `move` arguments at call sites and refuse
  use-after-move (`use-after-owner-move`), partial field/element moves
  (`partial-owner-move-unsupported`), and moves through loans
  (`move-through-loan-unsupported`), closed `effects` clauses verify borrowed
  parameter reads, mutable parameter writes, and direct or transitive callable
  invocations, and writes to a mutable variable, field or indexed collection
  invalidate stale current-value facts while preserving immutable snapshots
  (`let snap = ...`), `old(...)` pre-state references and proved-disjoint field
  facts.
- The loan checker uses [two-phase borrowing](../language/core-design.md#two-phase-receiver-borrows)
  for implicit `ref` interface receivers and `slots.Write(...)`. It permits
  a receiver read that ends during argument evaluation and checks retained
  overlapping loans at activation. Explicit `ref` and `out` retain their
  ordinary grant timing.
- Explicit nonoverlapping `interface ISized<T> { ... }` and
  `impl ISized<Nat> { ... }` declarations, supporting abstract callable
  signatures with `requires` and `ensures` contracts and abstract
  `lemma`/`theorem` law signatures, unification-based coherence and overlap
  refusal, blanket-impl and computed-type head refusal, Liskov signature and
  contract verification, explicit law proof checking, Gallina emission, and
  `where T : ISized<T>` generic constraint resolution with dictionary witness
  passing. Type-qualified (`T.Size(in value)`) and receiver (`value.Size()`)
  calls use the implementing type for dispatch.
  [Interface resolution](../language/first-release.md#interface-constraints-and-dispatch)
- Multi-module `import Module.Path;` composition (`elaborate(..., imports=...)`
  and `elaborate_package(modules)`) with topological dependency sorting,
  circular-import refusal, `public` versus `private` visibility enforcement
  across module boundaries for declarations, record properties and methods.
  Standalone Gallina modules distinguish dotted paths from literal underscores.
  For example, `A.B` emits `HoldFast_A_B`, while `A_B` emits `HoldFastEncoded_415f42`.
  Emitted package declarations carry their defining module identity, including
  private helpers in transitive dependencies. A plain import opens the public
  names and rejects conflicts. An aliased import exposes only qualified names. A selective import binds
  only its listed public names, including individually renamed constructors and interfaces.

Source callable interfaces preserve explicit arity: `Fn() -> Unit` and
`Fn(Unit value) -> Unit` require different calls and lambda parameter lists even
though their CIC interpretations use unit. Neither named arguments nor unit
normalization supplies an omitted argument.

Inference uses bounded structural unification with occurs and scope checks and
bounded definitional conversion. It proves no arbitrary arithmetic equality and
uses no external solver. Reduction exhaustion is a limit diagnostic, never an
established equation. Every unsupported syntax role, effect, capture, resource
modifier, grade, contract or unfinished proof is refused explicitly. This
increment supplies theorem authorship and proof parameters; automatic discharge
of `requires`/`ensures` and the full proof language remain frontend work.

The implementation is decomposed across the public entry point
([`elaborate.py`](../../tools/toolchain/elaborate.py)) and cohesive
submodules for CIC terms and carrier metadata
([`elaborate_types.py`](../../tools/toolchain/elaborate_types.py)),
schema-2 AST validation
([`elaborate_protocol.py`](../../tools/toolchain/elaborate_protocol.py)),
strings, characters and formatting
([`elaborate_strings.py`](../../tools/toolchain/elaborate_strings.py)),
definitional WHNF reduction and structural equality
([`elaborate_whnf.py`](../../tools/toolchain/elaborate_whnf.py)),
carrier and sequence intrinsics
([`elaborate_intrinsics.py`](../../tools/toolchain/elaborate_intrinsics.py)),
interval/algebraic precondition discharge
([`elaborate_solver.py`](../../tools/toolchain/elaborate_solver.py)),
proof terms and calculational chains
([`elaborate_proofs.py`](../../tools/toolchain/elaborate_proofs.py)),
pattern matching and exhaustiveness
([`elaborate_patterns.py`](../../tools/toolchain/elaborate_patterns.py)),
statements, indexing and bounded loops
([`elaborate_statements.py`](../../tools/toolchain/elaborate_statements.py)),
and module declarations, records, unions and contracts
([`elaborate_declarations.py`](../../tools/toolchain/elaborate_declarations.py)).
It owns explicit finite source, syntax-depth, inference-work,
reduction and output limits. Diagnostics retain source positions and distinguish
unsupported syntax, names, typing, unresolved inference, protocol and limits.
The consumer validates schema, source digest, fields, spans and identifier
spellings before constructing terms. Hygienic generated names and a closed
builtin mapping prevent Gallina injection. No raw Gallina, axiom, admission,
unchecked hole or foreign proof escape is emitted.

## Natural arithmetic

The elaborator checks the [Nat operand requirements](../language/reference.md#expressions-and-operators)
at each use of `-`, `/` or `%`. Closed operands, branch conditions and
`requires` clauses can supply the necessary facts. For example,
`requires used <= total` permits `total - used` in the function body and
requires callers to establish the bound. An unproved requirement stops
elaboration at the operation.

`Nat.SaturatingSub(a, b)` is total and returns zero when `b > a`.
Natural arithmetic emits the corresponding Rocq natural operations after
elaboration checks their source conditions. Calls such as `(-)(a, b)`
check the same requirements. To pass one of these operators as an
unconstrained function, use a lambda that establishes the premise in its body.

## Frozen static tables

A mathematical `const` can hold a length-indexed vector of static scalars or
other such vectors. A string literal supplies its UTF-8 bytes as a
`Vec<Nat, n>`. For example, `const Vec<Nat, 2> Accent = "é";` freezes the two
bytes 195 and 169. Word elements retain their declared signedness and width.
The mathematical target gives `usize` 64 bits.

The compiler checks the initializer and layout under the static dependency
rules. A call in a static initializer needs an empty effect footprint across
its callees, including operations behind helper functions and method receivers.
For a conditional choice of functions, both alternatives must qualify. A
higher-order helper can call a supplied callback with checked empty effects.
Closed demands reduce every element to its declared scalar or vector
value. A symbolic static binder can defer the calculation until a closed
specialization. Each frozen value has a budget of 64 vector slots, summed
across all dimensions. An empty vector consumes zero slots. A table with
two 31-element rows consumes 64. The source, reduction and output limits
also apply.

For a module constant, the emitted `_freeze` equality compares the interpreted
initializer with its frozen declaration. Closed local and argument freezes
carry conversion checks in the containing module. Rocq checks each equality
by conversion. The `holdfast_freeze_observe` lemma transports an observation
whose result type depends on the table along that equality. Consumers can
retain the frozen value at its declared type. The
[locked mathematical package build](#locked-mathematical-packages) binds the
frontend, parser, target and transitive source inputs used for specialization.

## Commands and acceptance

The [playground console](playground.md#dependent-mathematics-increment)
uses the bounded closed-expression evaluator.

`python tools/run.py holdfast-parser elaborate SOURCE` parses the complete surface,
elaborates this mathematical fragment and emits Gallina. `--output FILE` uses
atomic publication after complete validation and refuses input aliases. Missing
parents, malformed input and failed writes leave existing destinations intact.
The command runs through the existing guest dispatch because Menhir is native.
`holdfast-parser elaborate --help` documents development status and limits.

`python tools/run.py holdfast-parser elaborate-qualify` builds the pinned parser,
elaborates the authored example and independent positive/negative sources, then
kernel-checks emitted terms with the locked proof switch and recursively checks
the resulting library. Its receipt binds source, elaborator, parser and tool
identities, including the imported local checker sources, assumption auditor and
Python dependency/version owners. A late change to any bound input withdraws the
passing receipt. The assumption audit refuses empty, malformed or unsupported
reports; only the recognized closed-context response establishes zero assumptions.
A rejected neighbor must reach its intended semantic diagnostic;
parse failure and unavailable tooling supply no semantic rejection evidence.
Kernel replay covers generated terms. Checked parsing and source correspondence
require their own evidence.

Each `assert` in an executable proof, including a step within `calc` or a
justification block, emits a separate Gallina definition indexed by its source
byte span. Its type exposes the values and local proofs on which the
assertion depends. The assumption audit includes that definition even when
the next instruction does not use it. The natural-number bound checker can
weaken a comparison from a local proof or an ordinary executable `if` guard.
It uses the exact Boolean value of that guard on the selected arm. For
example, `if (n < 5)` supplies the premise for `n <= 4` on its true arm and
`n > 3` on its false arm. It can also join in-scope comparisons by
transitivity. Given `n < m` and a false `k < m` guard, it can prove
`n < k`. A strict or non-strict bound also survives adding the same term
on either side of each operand. The checker reuses the scoped comparisons and
constructs the corresponding Rocq monotonicity proof for each common addend.
It can also cancel common addends in a scoped premise. For example, a guard
`base + used < base + limit` supplies `used < limit` on its true arm and
`limit <= used` on its false arm. The resulting relative comparisons can join
other in-scope bounds.
The search examines at most 256 candidate joins per assertion, including
searches under common addends. If checking cannot establish an assertion or
exhausts this allowance, the diagnostic reports the outstanding proposition at
its source site. An explicit proof supplied with `by` can establish it.

Independent focused host tests exercise fresh polymorphic instantiations,
explicit/inferred arguments, dependent substitution, vector lengths and finite
lookup, higher-order constraints, proof composition, definitional conversion,
determinism and name hygiene. Negative neighbors cover unequal indices, wrong
domains, false equality proofs, non-propositions, universe misuse, occurs/scope
failures, ambiguous holes, missing proof bodies, stale or malformed protocol,
unsupported contracts and resource syntax, and bounded failures. CLI controls
exercise atomic publication, input aliases and failure preservation. Native
qualification replays source through the actual parser and kernel rather than
only using hand-authored syntax fixtures.

## Named goals

The native checker reports each `?name` at its source occurrence. For example,
`assert n == 4 by ?bound;` with `Nat n` reports the outstanding core
proposition `Eq(Nat, n, 4)`. A diagnostic pass checks the surrounding terms
with fresh variables for the missing values. Its report includes the expected
type supplied by the enclosing rule, available locals, branch facts, local
loans and the current return type. Two occurrences with the same spelling can
have different expected types. A source with any named goal fails compilation,
evaluation and package building.

A sibling operand can determine a hole's type through unification. A site
without a contextual or inferred type reports that the type is unavailable. If
checking stops before a site, the report keeps the first blocking diagnostic
and records which goals it could inspect. The inventory admits up to 128 sites
and bounds all goal and context text to 65,536 UTF-8 bytes. Reports in the
[local playground](playground.md#browser-behavior) follow the active buffer.
The release fixture's copy, cleanup and returned-view judgments require their
own [resource derivations](../language/core-design.md#typed-holes-and-invalidation).

## Locked mathematical packages

The batch builder composes packages for editions `math-1` and `math-2` on
target `rocq-gallina`. Each package's edition selects its
[import rules](../language/first-release.md#modules-and-packages).
In an offline workspace, each package revision lives at
`<name>/<revision>/holdfast-package.toml`. The manifest names both identifiers,
the edition and target, a `modules` table mapping exact HoldFast module names to
source paths, a `dependencies` table mapping canonical package names to
exact revisions, and an `inputs` list of additional files to bind. All input
paths are relative to the manifest. Install the selected revisions into the
workspace before locking. [Example manifest](../../examples/packages/scale/v1/holdfast-package.toml)

```console
python tools/run.py holdfast-parser lock-package examples/packages scale v1 --output scale.lock
python tools/run.py holdfast-parser build-package examples/packages scale.lock --output scale.json
```

The lock records every reachable manifest, file digest, module, revision and
dependency edge together with the parser, elaborator and target configuration.
A diamond must select a single revision for each package. A module can import
its own package and its direct dependencies, plus the built-in `HoldFast.Numerics`
aliases supplied by the locked frontend. A package instance digest binds its
canonical name, revision, declared files and dependency instances. Its nominal
declarations carry that identity in the emitted modules. The compiler checks
instance ownership and overlap across the closure, including sibling modules.

The build reads the locked inputs again before publishing a result. Its receipt
lists the module build order and the exact lock, source, package-instance and
Gallina digests. The optional output bundle maps full module names to complete
Gallina files and binds them to the lock digest. Missing revisions, undeclared
imports, conflicting module owners, cycles and stale lockfiles fail the build.
The `math-2` root also applies the [default authoring checks](authoring-tools.md#locked-package-authoring).
The closure is bounded to 64 packages, 256 files, 16 MiB of inputs and 32 MiB
of combined generated Gallina. This target produces mathematical elaborations.
Kernel replay and release artifact admission have their own evidence owners.
[Package contract](../language/first-release.md#modules-and-packages)

## Try the mathematical fragment

The [bounded word counter](../../examples/word_count.hf) borrows validated
UTF-8 for each lookup. A new key takes its own bytes in a three-byte builder.
An existing key only updates its count. With `red`, `red`, `blue` the table
counts two occurrences of `red` and returns `KeyBytesFull` with the table
intact. Other examples reuse one scratch variable, exhaust the two entry
slots, and count the two UTF-8 bytes of `é` against the byte budget.
`holdfast-parser elaborate-qualify` replays these proofs in Rocq. Represented storage is governed by the [release contract](../language/first-release.md).

Run from the repository root on Windows, using `python3` on Linux:

```console
python tools/run.py holdfast-parser elaborate examples/dependent.hf
python tools/run.py holdfast-parser elaborate-qualify
```

The [example](../../examples/dependent.hf) combines a generic
identity, higher-order application, inferred vector lengths, finite-index lookup,
a dependent callable and equality proofs. `elaborate` prints Gallina or writes
`--output FILE` in an existing directory. It requires the parser's locked native
toolchain; `elaborate-qualify` additionally requires the locked proof switch.
Only the latter command supplies a kernel verdict for its declared fixtures.

Generic parameters default to `Type`. The telescope `<TElement, ghost Nat length>`
quantifies a type and stable natural index. Each call infers new arguments by
default. The [generic application syntax](../language/surface-grammar.md#bindings-match-arms-and-generic-calls)
supplies them explicitly, and `_` requests an inferred argument. A contextual lambda can
use `value => ...` or `(left, right) => ...`; omitted parameter annotations use
the same bounded expected-type inference as annotation holes. Missing type
information remains an error. Ordinary value-returning functions may use
`=> expression;` as the checked equivalent of a single return block.
Declare a dependent callable with
`Fn(Nat length, Vec<Nat, length> values) -> Vec<Nat, length>`.

`Fst` and `Snd` project ordinary products. `Vec<TElement,length>` is a mathematical indexed collection, with `VNil`, `VCons`, `Fin`,
`FZero`, `FSucc` and `At` for construction and safe lookup. This prototype gives
it no machine layout. Definitional equality is computational: use `Succ(length)` or
`1 + length` for a successor index; arbitrary rearrangement of natural arithmetic
needs an explicit theorem. Inside `proof` blocks, `assert expr;`,
`assert expr by Lemma(args);` and `assert expr by { ... }` guide verification
using ordinary lemma calls and intermediate assertions rather than hand-built
proof combinators. Concrete product projections and finite lookup reduce during checking,
so the example proves its lookup result. `type[Eq<T>(left, right)]` lets an
ordinary parameter carry that proof.
