# HoldFast first supported release

This contract defines the first release's scope, primitive semantics, module
rules, ownership libraries and acceptance criteria. The
[language reference](reference.md) describes prototype support. The
[delivery plan](../../PLAN.md#holdfast-first-release-delivery) tracks implementation.
The [VerifiedOS requirements register](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/requirements-register.md)
governs platform admission.

## Release boundary

The first product is a synchronous, bounded systems-language subset connected to
one retained compiler route. It supports explicit machine representations,
records and finite tagged sums, generics, stable dependent lengths and states,
exhaustive matching, `Option`/`Result`, bounded loops, shared and exclusive loans,
ownership transfer, resource-aware exits, closed effects and checked contracts.
The resource discipline includes unrestricted, affine, relevant-verdict and
linear-obligation cases alongside [graded dependent typing](#default-graded-checking).
Permissions and disposal rules come from the resource interpretation. Public
interfaces fix representations, required-static inputs, effects and resource
contracts. Ordinary local inference preserves those contracts.

Ordinary `+`, `-` and `*` carry the representability obligations of
[primitive semantics](#primitive-semantics): linear facts discharge
automatically, while nonlinear facts need explicit proof or a checked, wrapping
or saturating operation. Runtime calls use closed effect footprints, with
[inference for eligible package-internal helpers](#package-effect-contracts)
and explicit public bounds. Implicit `ref` receivers use
[two-phase borrowing](core-design.md#two-phase-receiver-borrows) so argument
evaluation can read the receiver before the method acquires exclusive access.
Iteration-local loans end at each iteration boundary under the
[loop resource rules](core-design.md#loans-and-control-flow), with
[checked lending and spatial separation](#default-borrow-checking) in the
ordinary borrow checker.

Specifications and proofs may use the admitted mathematical definitions and
libraries in the existing kernel. A mathematical definition's expressiveness
does not imply a runtime representation or admission to executable type
conversion. The [mathematical prototype](../tooling/elaboration-prototype.md) retains its
own supported subset; the [pure prototype](../tooling/pure-prototype.md) and
[surface parser](surface-grammar.md) retain theirs. Parsing a larger feature does
not make it part of this release.

All language laws concern the elaborated image in an existing semantic anchor
under [the untrusted-elaboration boundary](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-020a). Located source
syntax, binding and resource derivations are inputs to checked interpretation
and source correspondence, not an independently authoritative operational
semantics. The kernel must check the interpretation and requested laws for the
actual source closure. A well-typed generated term alone proves neither intended
source meaning nor concrete memory safety. Concrete CHERI laws, representation,
lowering, final bytes and applicable admission remain separate obligations.

The first end-to-end client uses caller-supplied storage and the
[synchronous core](core-design.md). Bounded pool allocation is a later library
increment within this software product, requiring its actual allocator, manifest,
exhaustion and reuse proofs; there is no implicit heap or boxing. The release
does not require arbitrary grade domains, runtime multi-shot or shallow handlers,
general reflection/generation, concurrent interior mutation, native self-hosting,
ISA replacement or hardware authorship. Async and one-shot control capture need
a separately accepted consumer and their own resource/lowering slice.

Selecting an [extension](../extensions/README.md) requires a named client, a
comparison with the supported subset, an implementation and qualification budget
and a decision predicate. General grade domains and grade-directed authoring
tools follow the [graded selection protocol](../extensions/graded-foundation.md#extension-selection-and-qualification).

### Default graded checking

Ordinary elaboration of graded source reconstructs separate computation and
type-use demands, including the dependency rows of later declarations. The
supported domains are `NatExact`, whose computation demand must equal the
allowance, and `NatBound`, whose computation demand must fit the allowance.
Both retain exact type-use rows. Dependent functions, applications, graded
boxes and indexed record construction and elimination carry their demands
through substitution and checked motives. A checked derivation belongs to the
resolved source closure. The build rejects a violated allowance and reports
an unresolved obligation when it cannot reconstruct or replay the derivation.
[Graded rules and evidence](../extensions/graded-foundation.md#proof-and-qualification-obligations)

Calls preserve ordered evaluation, effects and exits even when the result of
evaluating an argument has zero computation use. A repeated use reads the
returned value of a single evaluation. Erasure and runtime admission require
the corresponding interpretation and representation laws. Read, write and
restoration authority follow the loan rules.
[Resource and computation interface](../extensions/graded-foundation.md#resource-and-computation-interface)

### Default borrow checking

Ordinary elaboration infers loan ends along control-flow paths and uses checked
facts to establish separation of symbolic footprints in owner coordinates. A
disjoint write can coexist with a live view, including across a branch join or
within a bounded loop with a checked footprint. Bounded lending must establish
the element loan's lifetime, restoration, and the loop and exit invariants.
Unresolved overlap or restoration produces a located obligation.
[Borrow-analysis promotion](core-design.md#borrow-analysis-promotion)

Qualification demonstrates where the default checker accepts direct source
that the pinned Rust modes reject, and records passing Rust API rewrites and
any runtime checks they require. It exercises conditional returns, lending
iteration and generic composition with the same expected behavior and matched
evidence endpoints. Claims of improved precision apply to the tested workload.
[Borrowing comparison](loan-analysis.md#conditional-borrowing-comparison)

## Primitive semantics

Every operation below has the same meaning in constant evaluation and runtime
code and under every assurance preset. Runtime representations come from the
selected target, never the build host. The
[existing integer policy](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-144) requires explicit conversions,
total ordinary arithmetic and named modular/saturating operations. The language
binds that policy as follows; the target bridge must prove the binding.

| Surface or operation | First-release meaning |
| --- | --- |
| `bool`, `Unit` | Exactly `false`/`true`, and the single unit value `()`. Integers have no truthiness conversion. |
| `u8`, `u16`, `u32`, `u64`; `i8`, `i16`, `i32`, `i64` | Unsigned values range from zero to `2^w - 1`; signed values range from `-2^(w-1)` to `2^(w-1) - 1`. Bitwise signed representation is two's complement. `byte` is an alias for `u8`. |
| Standard numeric aliases | The standard library module `HoldFast.Numerics` exports ordinary public aliases `int = i32`, `uint = u32`, `long = i64` and `ulong = u64`. Each denotes exactly its target type, including representation, arithmetic and proof obligations. Width-named spellings remain available. |
| `usize` | Unsigned index/count arithmetic at the target's declared XLEN width. This is not a capability's representation, permission to address all values of that width, or a pointer/integer conversion. Target specialization fixes the width and its representability obligations. |
| Mathematical `Nat` and integers | Specification/static values with their mathematical operations. Runtime use needs a selected finite representation and a proved range relation; there is no implicit arbitrary-precision runtime. |
| Integer literals | Decimal, binary and hexadecimal digits with the [separator rules](../tooling/authoring-tools.md#numeric-separators) denote exact mathematical magnitudes. A suffix or expected type determines the representation; an unconstrained runtime literal needs an annotation. No machine-default integer type is guessed. A syntactic negative integer literal is checked as one signed value, admitting the signed minimum; negation of an already typed expression obeys the ordinary range rule. An out-of-range literal is a compile-time error. |
| Ordinary `+`, `-`, `*` and unary `-` | Exact mathematical result with a proof that it is representable in the result type. Failure to discharge the premise is an unresolved obligation, not wrapping, trapping or a debug/release distinction. Operands have one explicitly determined type. |
| Ordinary `/` and `%` | Division truncates toward zero. For the mathematical quotient `q`, `a = q*b + r`, with `r` zero or of the dividend's sign and `abs(r) < abs(b)`. Both operations require a nonzero divisor; division additionally requires a representable quotient, excluding signed `MIN / -1`. Signed `MIN % -1` is exactly zero. A pair of runtime quotient/remainder results satisfies the equation only when the quotient is representable; the mathematical equation also describes the exceptional division input. |
| Checked arithmetic | Named `CheckedAdd`, `CheckedSub`, `CheckedMul`, `CheckedNeg`, `CheckedDiv` and `CheckedRem` return `Result<T, ArithmeticError>` with the ordinary value on `Ok`, otherwise the named `Overflow` or `ZeroDivisor` case. Division checks zero before signed quotient overflow; `CheckedRem(MIN, -1)` returns `Ok(0)`. They do not mutate their inputs or expose a partial result. |
| Modular and saturating arithmetic | Named `WrappingAdd`, `WrappingSub`, `WrappingMul` and `WrappingNeg` reduce modulo `2^w`, interpreting the resulting bits as the selected signed/unsigned type. `SaturatingAdd`, `SaturatingSub`, `SaturatingMul` and `SaturatingNeg` clamp the exact result to that type's minimum/maximum. There is no implicit modular conversion and no wrapping division/remainder in this initial vocabulary. |
| Bitwise operations and shifts | Bitwise operations use the selected `w` bits. Named `ShiftLeft` and `ShiftRight` take a `usize` count and require `count < w`; no implicit masking of excessive counts. Numeric left shift additionally requires the mathematical result to fit. Explicit `WrappingShiftLeft` discards high bits but retains the count bound. Right shift is zero-filling for unsigned and sign-extending for signed values, equivalent to floor division by `2^count`. `CheckedShiftLeft` and `CheckedShiftRight` return `InvalidShift` for an excessive count; the former returns `Overflow` for numeric left-shift range failure. |
| Conversions and comparisons | Infallibly wider scalar conversion uses `T.From(x)` (such as `long.From(x)` from `int`); range- or sign-checked conversion uses `T.TryFrom(x)` (such as `usize.TryFrom(x)` from `int`) and returns a named range failure; a proved conversion requires its range premise. Explicit truncation/reinterpretation uses a separately named bit operation. Ordering compares mathematical values within one type. Executable equality is Boolean through a selected decidable operation; proposition equality and transport stay in proof/contract interpretation. |
| Layout and encoding | Scalar representation/alignment is fixed by the target/ABI. Integer-to-byte encoding uses explicitly named little- or big-endian library operations; native record layout and padding never define a wire format. Capability fabrication and implicit pointer/integer conversion remain excluded. |
| Floating point | Not in this initial runtime release. A future consumer must select formats, NaN/signed-zero/rounding and exception behavior, equality/ordering, constant evaluation and target correspondence together. Parser recognition or existing hardware floating-point instructions supply no HoldFast support claim. |

The [e-means numerical research candidate](../extensions/numerical-workloads.md)
retains separate consumer and arithmetic qualification gates beyond this runtime
scope; it adds no primitive or first-release client.

Numeric aliases follow the [module rules](#modules-and-packages). Use
`import HoldFast.Numerics { int };` for an unqualified `int` in either package
edition. A plain `import HoldFast.Numerics;` binds `Numerics.int` in `math-2`
and opens `int` in `math-1` or stand-alone source. An explicit namespace alias
also works, as does the fully qualified `HoldFast.Numerics.int`.
The dependency lock binds the standard library package and its definitions;
there is no implicit prelude or import-order precedence. A duplicate local or
imported alias name is diagnosed under the same rules as another duplicate
binding; explicit qualification identifies the intended declaration. The source
facts retain that alias declaration and source spelling while type equality,
instance coherence, representation and lowering use the target type identity.
An alias creates no new nominal type, distinct implementation instance, runtime
conversion, numeric suffix or default integer type. Literals follow the suffix and expected-type rule. Qualify alias/target agreement,
resolution, collisions, range refusals and source provenance.

Named operations require library implementations and checked operation laws.
Generic operator overloading preserves primitive meanings and explicit conversions.
Bounds are established by proof or checked APIs.

### Contextual inference

Local inference removes an annotation only when the selected declaration and
checking context determine its meaning. Expected types may determine exact
integer literal representations, generic arguments, lambda parameters and
stable dependent indices. Range bounds share a selected integer representation:
`0..buffer.Length` can infer `usize` for the literal from that upper bound.
A suffix or annotation conflicting with the bound is an error; an already typed
operand never changes type to make the range fit. Ambiguous runtime widths need
an annotation, including an otherwise unconstrained `let count = 0;`.

In the [packet validator](../../examples/first_slice.hf),
`let magic = pkt[0];` selects `usize` for the index and `magic != 0x56`
selects `byte` for the compared literal. The packet C lowerer reads the
immutable syntax snapshot and literal widths from the checked elaboration.
Ordinary calls in the executable subset use the declaration sites resolved by
the checker. Supplying a checked result for different source bytes or a different
syntax tree fails before emission. Explicit and contextual spellings yield the
same Gallina terms and packet C code apart from the source digest.

Inferred indices retain stability and representation checks. Inference never
changes instance coherence, supplies authority, converts an existing value,
inserts ownership transfer or drops an obligation. An inferred proof is still
checked evidence; an unresolved goal remains unresolved. Public signatures keep
reviewed representations, static inputs, resource modes, effects and exits.
Qualification compares explicit and inferred clients at the same interpretation
and artifact endpoint, with exact boundary literals, ambiguity, wrong widths,
unstable indices and stale-source controls. Current pure/mathematical prototypes
retain their own scalar types; parsing a machine literal or loop supplies no
represented-inference implementation.

### Bytes and text

Source files are strict UTF-8. First-release identifiers retain the prototype's
ASCII identifier alphabet; string contents may contain Unicode. A `char` denotes
one Unicode scalar value (`U+0000` through `U+10FFFF`, excluding surrogates), with
a checked finite representation. A string literal denotes its exact UTF-8 bytes
without normalization, a terminator or implicit allocation. Embedded `U+0000`
is an ordinary scalar. Literal escapes are `\\`, `\"`, `\'`, `\n`, `\r`, `\t`,
`\0`, and `\u{H...}` with one through six hexadecimal digits denoting a scalar;
malformed/unknown escapes, invalid UTF-8 and non-scalar escapes are rejected.
Character literals decode to exactly one scalar. Raw string literals open with
three or more double quotes (`"""..."""`) and close with the matching quote
count without escape processing. Single-line raw strings contain no line breaks
between delimiters; multi-line raw strings follow the opening delimiter with a
newline, place the closing delimiter on its own whitespace-indented line, strip
that closing line's leading horizontal whitespace from every non-empty content
line (rejecting non-empty content lines with less indentation), exclude the
opening newline and the newline immediately preceding the closing delimiter, and
normalize interior line breaks to LF (`\n`). Raw byte data uses byte buffers
and explicit encoders rather than malformed text literals.

The initial text library uses an immutable validated UTF-8 view with represented
byte extent and the ordinary loan/lifetime contract. Decoding untrusted bytes
returns either that view with its validity proof or a typed encoding error;
neither path invents ownership or extends the input's lifetime. A mutable byte
alias cannot survive beside a validity-dependent immutable text view.

`ByteLength` counts encoded bytes. `ScalarCount` is an explicitly bounded
traversal; neither claims to count grapheme clusters or display cells. Text has
no ambiguous integer indexing operation: access its byte view, iterate scalars,
or use a checked byte-range slice whose endpoints are UTF-8 boundaries. Text
equality compares exact encoded bytes; canonically equivalent but differently
encoded scalar sequences remain distinct. Normalization, locale collation and
grapheme segmentation require separately specified libraries. Runtime-built
text uses explicit bounded storage, validation, and capacity outcomes. Literal
backing is read-only and counts toward the composed image. An interpolation
template belongs to a buffer-writing call such as `Format.Write(ref builder, $"...")`.
The destination is a `ref TextBuilder<capacity>` or `ref Span<byte>`.
Each hole resolves a static `IFormat<T>` implementation. `{value:spec}` also
checks its format specification at compile time. The call returns
`Result<usize, CapacityError>` and requires no runtime reflection, boxing, or
ambient locale. When a builder write runs out of capacity, it returns
`Err(CapacityError)` and preserves the builder's previous length and bytes.
The span overload declares whether failure rolls back or retains a prefix.

## Modules and packages

The module boundary must support two independently authored libraries before
public generic APIs qualify. A package manifest names its canonical package,
language edition, module roots, direct dependencies, explicit build inputs and
target/profile. A lock records each resolved package's exact source digest,
selected version/revision, transitive closure, generator/tool identities and
configuration. Locked builds neither resolve a different version nor read
undeclared ambient inputs. Fetching dependencies is an explicit preparation
operation; missing locked inputs produce an incomplete-build result.

The mathematical batch target builds this closure from local package
revisions and binds its generated Gallina bundle to the exact lockfile.
[Locked mathematical packages](../tooling/elaboration-prototype.md#locked-mathematical-packages)

Each linked closure selects one revision per canonical package and one owner per module path. Incompatible dependency requirements fail resolution. Aliases change local spellings after resolution. Two revisions can be built in separate closures. The mathematical package checker enforces module-path uniqueness and reports both source digests on a collision.

The initial import graph is acyclic and imports are explicit. Cycles report the
cycle rather than depending on traversal order. Modules have no runtime
initializers. Required-static initialization evaluates ordinary total pure
definitions: each required-static input must resolve to an admissible closed
value when its use is specialized, or the build reports a located obligation or
refusal with no runtime fallback. [`const` declarations](surface-grammar.md#required-static-constants)
spell the interface, and [the core's staging rules](core-design.md#refinement-effects-and-staging)
bound conversion and erasure.
In a locked `math-2` package, a plain `import Module.Path;` introduces the
namespace `Path`. Use `Path.Operation(...)` to call an export. Imports in a
`math-1` package or a stand-alone mathematical source retain their open scope.
`import Module.Path as M;` introduces only the namespace `M` in either edition.
`import Module.Path { State, Busy as Occupied };` brings just those declarations
into scope. Constructors retain their nominal identity under an uppercase alias.
The importing package selects its own edition independently of each dependency.
Before migrating an open import, identify its consumed exports and select them
explicitly, or qualify uses with a namespace. If two module paths end with the
same name, give at least one an explicit namespace alias. Replay callers'
contracts and check imported instance selection across the migration.
Qualified names resolve independently of import order. Duplicate local/imported
bindings are errors unless an explicit alias distinguishes them. A public nominal
identity comprises the resolved package instance, module path and declaration
identity. Two package revisions with the same printed type name are distinct;
neither structural similarity nor reflection can equate their private types.

### Interface constraints and dispatch

The interface implementation model uses explicit nonoverlapping
instances. The defining package must own the interface or the outer
nominal implementing type. A bare type parameter does not establish ownership;
foreign interfaces on foreign primitive types require a local nominal wrapper.
Instance heads use nominal type constructors, rigid constants and type
parameters, with structural unification deciding possible overlap. Arbitrary
computed type families and proof search are unavailable in instance selection.
Potentially overlapping instances are rejected without specialization, priority,
negative bounds or import-dependent choice. The first interface argument is its
implementing type. A generic declaration requests each interface implementation
with a bound on that type, such as `where T : ISized<T>`. Each bound supplies
a checked dictionary, including the declared contracts and required laws.
[Constraint syntax](surface-grammar.md#generic-interface-constraints)

Call through the implementing type, as in `T.Size(in value)`, or use a receiver
call, as in `value.Size()`. A receiver supplies the first method argument and
uses its declared loan mode.
Generic dispatch uses the bounds on the implementing type. Concrete dispatch
uses the implementations available for that type. The implementing type,
method name and source argument count must select a unique interface. When
several bounds provide the same method, a helper with one bound can select the
intended interface. The selected method's ordinary type, instance, loan and
contract checks apply.

### Exported signatures

Public signatures specify generic and required-static parameters, result types,
effects, call modes, transitive capture constraints, pre/postconditions and
resource exits. Private representations stay abstract except through explicit
published views or derivation interfaces. Implementation changes must re-establish
the exported contract. An interface fingerprint binds these semantic declarations,
the nominal identities and any exposed representation/ABI; source maps have a
separate exact-byte identity. Dependency records also include implementation and
proof bodies actually consumed, accepted assumptions, target and tools. An equal
interface fingerprint alone cannot reuse stale compilation or proof evidence.
Until finer dependency tracking is qualified, a semantic dependency change
invalidates the reachable component closure conservatively.

### Package effect contracts

The release lets a nonrecursive top-level runtime function omit its `effects`
clause when the function is file-private or `internal` and each call has a
direct, statically resolved target with a checked closed footprint. A sibling
module can import an `internal` function within the same locked package
instance. File-private functions are visible within their defining file.
Callers can use either an authored bound or a checked inferred footprint for
these helpers. Recursion and calls through a callable value require explicit
checked bounds.

Each exported runtime callable declares its closed bound, including
`effects none` for an empty bound. Within the package, the checker composes
inferred and explicit footprints and verifies each export against its published
bound. Importing clients check calls against that published bound with the
implementation opaque. Calls use the resolved declaration and parameter
identities under qualification and import aliases. The
[footprint rules](reference.md#contracts) define propagation to caller places.

### Public API evolution

Adding a case to a public closed union can break downstream exhaustive matches;
adding a public export can make an existing open import ambiguous. Adding a
required interface method or law changes the obligations of existing instances.
Parameter labels, required-static status, grades, capture and effect bounds, and
public representation participate in compatibility alongside parameter/result
types. An upgrade that strengthens a precondition or weakens a postcondition can
invalidate callers and their proofs. An upgrade that widens a published effect
bound can invalidate callers whose own bounds no longer cover it. A helper
refactor whose effects fit the existing published bound preserves that part of
the interface and still requires fresh evidence for the changed locked inputs.
A release must identify interface changes, version breaking changes accordingly,
and supply a migration or retain an adapter where the prior interface can still
be implemented. An API intended to admit new internal cases can expose an
abstract type with stable eliminators.

Run `holdfast-parser diff-contract BASELINE CANDIDATE` to review the authored
changes to one module. The JSON report binds both source digests and lists
added and removed public declarations, changed declaration fields, and changes
to imports and implementation declarations that can affect resolution.
It compares syntax without source locations or comments. It includes contracts
and effect clauses and retains transparent definition bodies. It omits
top-level executable function and theorem/lemma bodies. The comparison treats
changes to binder spelling and equivalent expressions as differences and gives
no semantic compatibility, kernel assumption or runtime permission verdict.

The local [client replay command](../tooling/elaboration-prototype.md#client-upgrade-replay)
keeps client and dependency sources fixed and elaborates both revisions, including
exhaustiveness and proof obligations exercised by those clients. Release
qualification also requires its kernel, ABI and target-specific evidence.

## Ownership libraries

The initial client needs a small, proved library of buffers, immutable/mutable
spans, bounded iteration, records/sums, initialization and typed errors. Public
operations state capacity, bounds, overlap, initialization, retained loans and
resource states on every exit. Every sequence-modeled view or buffer implements
the law-carrying `ISequenceModel<C, T>` interface for container type `C` and
element type `T`. It projects the container to its canonical erased pure
`Model : Seq<T>` (`Nat(Length) == Model.Count`) while
keeping the C#/Kotlin-style collection predicates and slice combinators—`.All(x => ...)`,
`.Any(x => ...)`, `.Contains(x)`, `.Take(n)`, `.Skip(n)`, `.Slice(a, b)` and
`.Count` alongside `.At(i)`, `.Update(i, v)` and `.Append(x)`—as concrete
operations on `Seq<T>` backed by pre-proved standard-library lemmas. Contracts
on concrete containers or on `C` with `where C : ISequenceModel<C, T>` write
`requires items.Model.All(x => x > 0)` rather than raw `forall`/`exists`
index quantifiers, and bounded predicates over finite sequences with decidable
element bodies discharge in the
[decidable/domain refinement tier](core-design.md#refinement-effects-and-staging)
rather than open quantifier instantiation or polymorphic LINQ dispatch. No
runtime `IQueryable<T>` or reflection-based expression-tree interface is
introduced; contract checking inspects `Seq<T>` predicate lambdas statically, and
compile-time query specialization is an extension under the [staging design](../extensions/metaprogramming.md#evaluation-and-phase-boundaries).
Iterators carry their bounds and loan contracts; they do not require ordinary
users to reconstruct a separation-logic proof at each element. Codecs retain the
platform's required format-description and
[boundary initialization obligations](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-124).

The [collection-loop surface](surface-grammar.md#ergonomic-authoring-and-bounded-collection-iteration)
uses a law-carrying `IBoundedIterable<C, T>` interface refining `ISequenceModel<C, T>`
rather than C#'s stateful `IEnumerable<T>` / `IEnumerator<T>` (`MoveNext`/`Current`/`IDisposable`).
Value iteration requires copy permission; shared/exclusive iteration selects an
explicit element loan. The source is evaluated once, a declared `Model.Count`
bound and stable footprint determine iteration, and step `k` connects directly to
`Model.At(k)`, `Model.Take(k)` and `Model.Skip(k)`. All exhaustion and early-exit
paths restore or explicitly return the resources promised by the iterator
contract. No enumerator allocation, implicit disposal, owned-element copy,
escaping element loan or invalidating mutation is introduced. Parser support is
syntax-only until a real iterator library and represented checker discharge those
duties.

`out T` retains its simple rule: no reads before initialization and a fully
initialized `T` on every normal return, including an error return. Fallible
construction instead consumes an owned storage/builder state and returns an
outcome-indexed state: a completed value, an explicitly retained initialized
prefix, or restored empty storage after total rollback. These are library types
and resource contracts, not an unchecked `MaybeUninit` escape. The initialization
map names exactly the fields/elements that may be read or disposed; dropping a
partially built object visits only those entries, accounts for their resources,
and restores the promised storage state. Failure must return storage and
unconsumed inputs or discharge them through an explicit proved operation.
For an ordinary fallible factory, return `Result<T, E>` and bind the completed
value on `Ok`. Reserve a state-indexed builder for callers that supplied storage
or own resources during construction. If an error can leave that storage
partially initialized, its payload carries the builder and its initialized
prefix. An `out` diagnostic on an early `Err` or `?` points to that return
and suggests the factory form when the caller supplied no storage. Boundary
contracts continue to determine whole-buffer initialization and zeroization.
The [elaboration replay](../../tools/toolchain/elaboration_check.py) exercises a
fallible byte update with arbitrary initial contents. It checks the written byte
on success, restoration of its original value on failure, and preservation of
every other byte on both paths. Omitting the error-path restoration fails the contract.
`TextBuilder<capacity>` and `Format.Write(ref builder, $"...")` (or
`Format.Write(ref span, $"...")` over `ref Span<byte>`) follow the bounded
buffer-writing contract in [Bytes and text](#bytes-and-text), evaluating hole
arguments left-to-right under the active receiver loan and returning
`Result<usize, CapacityError>` with the declared prefix/rollback state on
`Err(CapacityError)`.

Construction, replacement and bounded collection growth must demonstrate failure
before the first write, partial failure, successful completion and rollback with
a live unrelated frame. Multi-step container updates that temporarily decouple
fields declare named invariant conjuncts (`invariant Clause: ...`) and open only
the affected clauses through `open (ref this) lifts Clause, ... { ... }`:
unlifted conjuncts remain active without re-proof across disjoint or
non-invalidating field writes, while the linear close debt forbids early exits
(`return`, `break`, `continue`, `?`), suspension, handler capture or whole-receiver
calls until the lifted clauses are re-established at the closing brace. Bulk prefix
relocation between vacant-slot buffers (`Slots<T, capacity>`) separates physical
representation copying from logical ownership transfer: `CopyRepresentation`
performs a CHERI-tag-preserving copy of `[0..count)` into logically vacant
destination slots (`Vacant<T>`), leaving the destination vacant/unowned and
recording a revision-bound representation-equality fact without arming destructors
or duplicating linear ownership, and the erased operation `TransferType<T>`
consumes that representation-equality fact with the initialized source prefix and
vacant destination prefix to transition source `[0..count)` to vacant and
destination `[0..count)` to live initialized `T` in one capacity-independent range
step. A collection exposes the two steps as one checked prefix-relocation method.
Its element law establishes that moving a live value to a fresh address preserves
its invariant and all outstanding observations. An interior pointer into the old
range, a pinned value, or a device retaining the old address needs a separate
transition that ends or repairs that dependency. Equality of bytes and tags
alone cannot establish the law. The mathematical prototype admits fixed-width
integers, `bool`, `char` and `Unit` at both operations. Generic or opaque
elements require a checked law before the release implementation can admit them.
The [element-loan regression](../../tools/tests/test_holdfast_loans.py#_element_loan_during_relocation)
passes a shared loan of the first occupied slot as one argument and relocates the
source prefix while evaluating the next argument. The elaborator reports the
exclusive source borrow at relocation and the earlier element loan. Copying the
`u32` into a local before the call preserves the value to observe and lets the
same relocation proceed.

No allocation, emergency capacity or cleanup retry is
implicit. A later explicit bounded-pool library additionally satisfies the
[pool declaration and exhaustion contracts](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-046), with
reuse/quiescence proof before returned backing is lent again.
Its qualification includes an older list whose header survives while growth
moves its elements into scratch storage. Reclaiming that storage with the list
still pointing into it must fail at the reclamation obligation. In the valid
case, build the new elements in scratch and copy the selected bytes into the
older list's independently owned backing. End the scratch loans, reclaim and
overwrite the scratch storage, then read the retained bytes from the list.
A surviving field or element that still points into
scratch keeps its backing live. These cases apply to the
[bounded-pool milestone](../../PLAN.md#q25bx) and are drawn from
[Zero C#'s arena rollback example](https://onurgumus.github.io/zero-csharp/concepts/memory.html#the-restore-hazard).

An initialized buffer can use `buf.Update(buf.ReadCount())` with an implicit
whole-object `ref` receiver and a count that carries no loan into the call.
The [receiver rule](core-design.md#two-phase-receiver-borrows) reserves the
buffer before evaluating the count and acquires exclusivity at method entry.
A diagnostic identifies the competing access if an argument mutates the buffer
or retains an overlapping view. It may suggest an explicit snapshot only when
the snapshot preserves the observed revision, evaluation order and lifetimes.

Public named views still let a caller keep a shared loan of `Count` while a
method takes exclusive access to `Data`. The provider's disjointness law
establishes separation for each representation and permitted entry state.
Qualification repeats this client across a package boundary after a private
layout change, verifies that overlapping backing fails the law, and records
which client proofs or annotations changed. The
[receiver qualification cases](loan-analysis.md#two-phase-receiver-trial)
check both the argument read and the retained-view conflict.

<a id="csharp-transition-guide"></a>

## Authoring idioms

For authoring syntax and its semantics, use the [language reference](reference.md),
[authoring style](../tooling/authoring-tools.md#common-style), and
[checked code actions](../tooling/authoring-tools.md#compiler-verified-assist-dont-coerce-tooling).
Unwrap before member access with `(Read()?).Value` or an explicit `match`.

## Qualification

The [delivery plan](../../PLAN.md#holdfast-first-release-delivery) selects a real
bounded byte-buffer consumer and an independently chosen second client before
implementation. Their contracts must identify actual formats, entry states and
independently expected success/failure results. A candidate that only parses,
emits a term or returns an unconstrained theorem has not met this predicate.

| Subject | Acceptance evidence |
| --- | --- |
| Interpretation and concrete resources | Checked elaboration-image laws, an inhabited carrier state, read/write/initialization/frame and loan restoration, with wrong-offset, alias, premature-restoration and partial-initialization neighbors rejected at the intended obligations. Missing laws remain missing; no axiom or source judgment substitutes for them. |
| Scalar and text behavior | Independent boundary fixtures for every supported type and operation, signed division/remainder signs, zero and minimum/-1, shift zero/width-1/width, exact/wrapping/saturating arithmetic, target versus host width, invalid conversions, embedded NUL, malformed UTF-8/escapes, raw-string delimiter/indentation and LF-normalization rules, static `IFormat<T>` checked formatting (`Result<usize, CapacityError>` on exact fit and `CapacityError` exhaustion without heap allocation or ambient locale), scalar boundaries and byte slicing. Static and runtime meanings agree under the same target. Generate finite boundary classes from an independently reviewed oracle; a shared implementation is not an independent expectation. |
| Package composition | Two independently authored packages compose with fixed instances; reordered imports preserve meaning; overlap, cycles and conflicting nominal identities are diagnosed. Locked builds reproduce their source/input closure. Contract, representation, proof assumption and tool changes invalidate affected evidence before reuse. |
| Graded dependent typing | The default build checks both natural domains, dependent substitution, box and indexed-record elimination, and separate type and computation demands on a reviewed client. Incorrect allowances, altered motives and stale dependencies fail at their obligations. Check ordered evaluation and erasure at the claimed representation endpoint, including unused and repeated arguments. [Default graded checking](#default-graded-checking) |
| Borrowing precision | The default build checks proof-backed symbolic separation, conditional returns, and bounded lending across its supported control flow. Replay restoration and the frame for each exit. Use paired positives and invalid neighbors on held-out clients, record unsupported cases and exhausted budgets, and measure checking cost. [Default borrow checking](#default-borrow-checking) |
| Everyday ownership | Bounded collection/iterator, `.Model` sequence-predicate/slice, `TextBuilder<capacity>` / `IFormat<T>` checked formatting, [two-phase receiver calls](loan-analysis.md#two-phase-receiver-trial), selective invariant lifting (`invariant Clause: ...` / `open (...) lifts ...`), two-step bulk relocation (`CopyRepresentation` + `TransferType<T>`), fallible-builder and error-propagation clients compile under their actual representations and the [borrow-analysis promotion contract](core-design.md#borrow-analysis-promotion). Escaped views, duplicated tokens, reads of unwritten or moved-out vacant slots, early exits or whole-receiver calls while an invariant clause is lifted, stale current-content facts and lost mandatory outcomes fail at the responsible resource rule. Bounded buffer, builder and bulk-relocation proofs/certificates pass a **capacity-invariance gate**: checking at tiny static capacity ($N = 4$) and large static capacity ($N = 10^9$) produces equal obligation counts and the same proof and certificate structure after changing only the encoded capacity literal. Count and compare emitted range obligations and prohibit per-element unfolding, enumeration or evidence. The current first-slice pilot compares 8 and 10⁹ because its packet requires eight bytes. Each capacity must fit the 4 MiB generated Gallina limit, each Rocq compile and the combined kernel replay must finish within 120 seconds, and the pilot also compares symbolic reduction and work counters. Record actual replay measurements separately from this pass condition. |
| Complete software path | Authored source and independent contract reach one retained backend with checked correspondence, representation and lowering; applicable final-byte, resource, observation and admission duties meet their existing owners. Report source, artifact and production evidence separately. |
| Developer usefulness | Record annotation burden, first useful diagnostic, checking latency, code/stack/storage consequences and repair after a semantic-preserving refactor, a representation change and a real contract change on both clients. Count arithmetic lemmas and checked operations, the effect clauses edited for a package-internal refactor or a public widening, and snapshots, named views or loop rewrites required by borrowing. Compare the receiver call with a legal snapshot spelling under equivalent evaluation order. Preserve the held-out client and record the adaptations it needs. |

Hard safety, resource and admission limits are mandatory. Technical feasibility,
recurring authoring/maintenance benefit and eventual economic adoption are
separate decisions. Charge setup and shared maintenance fully, without requiring
the first two small clients to repay the entire language foundation. Any accepted
size/speed trade has a declared target envelope and per-case evidence; no average
hides a missed hard bound.

### First-slice component and concrete `Span<byte>` carrier <a id="first-slice-qualification"></a>

The [authored packet validator](../../examples/first_slice.hf) copies the accepted
header and payload into the destination and zero-pads the eight-byte work area.
Success returns a read-only view of the payload. Framing rejection preserves
the complete destination. Other protocol rejections clear the work area.
Every exit preserves the bytes beyond that area.
[Packet walkthrough](../tooling/packet-walkthrough.md)

`SpecPacketOutcome` specifies what a caller observes from the returned result.
It gives framing errors priority over header errors, then checks the payload
length before the checksum. On success it gives the copied byte count. The
validator exports the equality between this specification on the entry state
and `PacketOutcome(result)`. Callers may use that equality with the body opaque.

At this entry point, `ref dst` and `in pkt` initially loan the
two descriptor places. Each descriptor must already identify live backing
with valid provenance, bounds and the declared permissions. The backing
extents may overlap. The framing test reads descriptor metadata and returns
`FramingShort` before accessing any byte on that path. Its successful edge
introduces exclusive access to the destination bytes and shared access to
the packet bytes for the rest of the operation. The success view retains
its destination loan as specified by the result. Internal copy operations
require their content loans and separation at entry. Ordinary calls that
already require exclusive access to backing retain the
[core loan rule](core-design.md#loans-and-control-flow).

The generated C harness passes one backing array through the packet functions.
Each descriptor carries a byte cursor for memory access and a logical base for
interval checks. Allocation initializes both to the same offset, and slicing
advances both. The observer checks the returned cursor and base independently
against the expected destination offset, including for an empty view.
Successful cases use disjoint extents of the allocation. The overlap case
observes the source header through the destination view before calling the
validator and checks every destination byte against its entry snapshot on
refusal. Admission for a foreign caller requires the machine interpretation
to justify descriptor validity and this correspondence before the framing
test may use its interval comparison.

The [mathematical carrier](../tooling/elaboration-prototype.md) represents a
`Span<byte>` by its backing store, `Base`, `Length`, `Tag`, `PermRead` and
`PermWrite`. `Span.AllocZeroed` belongs to specifications and theorems. Span
operations check bounds, representability of offsets and counts, permissions,
loans, and any required disjointness. These checks also apply at the last
representable byte, where an exclusive end address can overflow. Restoration
requires the view's immediate parent or the parent updated from that view.
Function postconditions use the returned value and `ref` post-state. Automatic
restoration checks preserve all five metadata fields of each `ref` span or slot
descriptor.

#### Qualification and receipt binding

Run `python tools/run.py holdfast-parser first-slice` for fresh proof and execution
checks. The [qualification harness](../../tools/toolchain/first_slice.py) owns the
input fixtures, commands and report fields.

| Check | Evidence |
| --- | --- |
| Source proof | Parse with Menhir, elaborate to Gallina, compile with `rocq c`, audit exported assumptions and replay with `rocqchk`. The `accepted` verdict requires an empty `solver_trust` ledger. The appended false equality must fail at the expected definition. |
| Capacity and refusals | Compare proof structure and inference/reduction work at capacities 8 and 10⁹ and replay both proofs. Each negative fixture must parse after its `/*error*/` marker is removed. Elaboration must report the expected category and message fragment at the marked line and column. |
| Capability execution | The handwritten purecap program checks the live four-byte view has data-load permission alone. Sail must reject the writable-view variant at that check, trap on a store through the narrowed view, and reproduce the bounds and tag traps. |
| Optional CompCert execution | Lower the validator and scenario drivers to Clight/C, execute under CompCert's interpreter and run purecap images in Sail. Check the passing paths and altered payload, padding, checksum-code and clearing controls. Use `--ccomp /absolute/path/to/ccomp` to require this run. Automatic discovery records `compcert_sail.available: false` when the compiler is missing. [Compiler build contract](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/implementation/contracts/contained-compiler-reuse.md) |
| Guest C11 regression | Compile the generated validator with the system C compiler at `-O0` and `-O2` and check all five exits. Before reading a successful payload, check its cursor, base, length, tag and permissions. Reject a cursor into the input for an empty view or an identical four-byte payload, and reject a view granting write access. |
| Inline proof erasure | [The native regression](../../tools/tests/test_holdfast_packet_erasure.py) adds an assertion, proof block and calculation to the checksum implementation, replays the annotated module, and compares the complete guest executable at both optimization levels. A false assertion fails during elaboration. |

Use `python tools/run.py holdfast-parser first-slice-bindings <receipt.json>` to
check a retained schema-2 receipt against the checkout and installed tools.
A match binds the exact source, toolchain, target profile, generated artifacts
and check transcripts. The checker regenerates the source-derived Gallina and C,
reassembles the control images, and derives verdicts from the retained process
output. It checks each retained type error against its fixture's marked location.
It requires the full export audit, kernel replay and execution observations,
including the effective CompCert inputs when that run is present.
Missing or substituted artifacts, malformed or contradictory
transcripts, and changes during verification refuse a match. Inventories are
limited to 4,096 entries and 256 MiB in the checkout's local output lane.
`status: matched` is a binding verdict with `proof_replayed: false`.
The result lists the packet functional result and returned-view authority in
`missing_deployed_evidence`. Each needs checked evidence for the exact admitted
image and entry point. A receipt that substitutes a host packet observation
for the deployed view evidence fails with the missing target claim.
[Deployed evidence contract](../assurance/compiler-route-contract.md#evidence-for-each-deployed-claim)

These checks qualify the symbolic source model and record concrete execution
observations. Exact executable acceptance requires checked source correspondence,
resource laws over canonical Sail, compiler refinement, contextual preservation
and artifact admission. The harness reports missing dependencies in `inventory`.
[Exact executable acceptance](../../PLAN.md#q25ba)
