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
that the pinned Rust modes or the implemented Ante subset reject. It records
passing rewrites and any runtime checks they require. It exercises conditional
returns, lending iteration and generic composition with the same expected
behavior and matched evidence endpoints. Claims of improved precision apply to
the tested workload.
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

Initial clients use a proved library of buffers, immutable/mutable spans, bounded iteration, records/sums, initialization, and typed errors stating capacity, bounds, overlap, initialization, loans, and per-exit resources. Sequence-modeled views/buffers implement `ISequenceModel<C, T>` projecting to erased `Model : Seq<T>` (`Nat(Length) == Model.Count`) with C#/Kotlin-style predicates and slices (`.All(x => ...)`, `.Any(x => ...)`, `.Contains(x)`, `.Take(n)`, `.Skip(n)`, `.Slice(a, b)`, `.Count`, `.At(i)`, `.Update(i, v)`, `.Append(x)`) backed by pre-proved stdlib lemmas. Contracts use `requires items.Model.All(x => x > 0)` (not raw `forall`/`exists`); decidable bounded predicates discharge in the [refinement tier](core-design.md#refinement-effects-and-staging) without open quantifiers, polymorphic LINQ, `IQueryable<T>`, or reflection expression trees (compile-time query specialization stays under [staging](../extensions/metaprogramming.md#evaluation-and-phase-boundaries)). Iterators carry bounds/loan contracts without manual elementwise separation proofs; codecs retain format-description and [R-05-124 initialization duties](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-05-124).

[Collection loops](surface-grammar.md#ergonomic-authoring-and-bounded-collection-iteration) use law-carrying `IBoundedIterable<C, T>` (refining `ISequenceModel<C, T>`) rather than stateful `IEnumerable<T>`/`IEnumerator<T>`. Value iteration needs copy permission; `in`/`ref` select element loans. The collection evaluates once; `Model.Count` and stable footprint bound iteration, tying step `k` to `Model.At(k)`, `Model.Take(k)`, and `Model.Skip(k)` and restoring/returning promised resources on exhaustion and early exits (no enumerator allocation, implicit disposal, escaping loans, or invalidating mutation). Parser support stays syntax-only until an iterator library and represented checker discharge these duties.

`out T` forbids pre-init reads and requires full initialization on all normal returns (including errors). Fallible construction consumes owned storage/builder state and returns outcome-indexed state (completed value, retained initialized prefix, or restored empty storage after rollback—library types/contracts, never `MaybeUninit`, tracking exact readable/disposable initialized entries and returning/discharging unconsumed storage on failure). Use `Result<T, E>` factories when callers supply no storage (`out` diagnostics on early `Err`/`?` suggest factories); reserve state-indexed builders for caller-supplied storage or owned mid-build resources. Boundary contracts still govern whole-buffer init/zeroization. [Elaboration replay](../../tools/toolchain/elaboration_check.py) checks fallible byte update with arbitrary entry bytes (written byte on success, restored byte on failure, untouched frame bytes on both). `TextBuilder<capacity>` and `Format.Write` follow [Bytes and text](#bytes-and-text), evaluating holes left-to-right under the receiver loan and returning `Result<usize, CapacityError>` with prefix/rollback state on failure.

Construction, replacement, and growth test pre-write failure, partial failure, completion, and rollback with live unrelated frames. Multi-step container updates declare named `invariant Clause: ...` conjuncts and lift affected clauses via `open (ref this) lifts Clause, ... { ... }`: unlifted conjuncts stay active across disjoint/non-invalidating field writes, while the linear close debt forbids early exits (`return`, `break`, `continue`, `?`), suspension, capture, or whole-receiver calls until restored at close. Bulk prefix relocation across `Slots<T, capacity>` splits CHERI-tag-preserving copy (`CopyRepresentation` of `[0..count)` into logically `Vacant<T>` slots with revision-bound representation equality, zero destructors, zero duplicated ownership) from erased logical transfer (`TransferType<T>` flipping source `[0..count)` to vacant and destination `[0..count)` to live initialized `T` in one $O(1)$ range step), exposed as one checked method requiring an element relocation law (destination invariant preservation and absence/repair of old-address observers/interior pointers/pinned values/DMA; byte/tag equality alone is insufficient; derived mode crossing admits fixed-width ints, `bool`, `char`, `Unit`, and closed non-dependent records, unions, and tuples whose components cross modes, while refusing authority-bearing types, loans, cells, and unconstrained generics without a checked law). [Element-loan regression](../../tools/tests/test_holdfast_loans.py#_element_loan_during_relocation) rejects a live first-slot shared loan across prefix relocation unless copied to a local `u32` beforehand.

No implicit allocation, emergency capacity, or cleanup retry exists; later explicit bounded pools satisfy [R-08-046](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/spec.md#r-08-046) and quiescence/reuse proofs before re-lending backing—tested on [bounded-pool milestone](../../PLAN.md#q25bx) using [Zero C#'s arena rollback cases](https://onurgumus.github.io/zero-csharp/concepts/memory.html#the-restore-hazard) (refuse reclaiming scratch while list points into it; accept copying into list's owned backing, ending scratch loans, overwriting scratch, and reading list).

Initialized buffers support `buf.Update(buf.ReadCount())` via [two-phase receiver borrowing](core-design.md#two-phase-receiver-borrows) (reserving receiver before arg evaluation, activating exclusivity on entry, diagnosing argument mutations/overlapping views, suggesting snapshots only when preserving revision/order/lifetimes). Public named views allow shared `Count` loans alongside exclusive `Data` calls via provider disjointness laws, qualified across package boundaries after private layout edits ([receiver cases](loan-analysis.md#two-phase-receiver-trial)).

<a id="csharp-transition-guide"></a>

## Authoring idioms

See [language reference](reference.md), [authoring style](../tooling/authoring-tools.md#common-style), and [checked code actions](../tooling/authoring-tools.md#compiler-verified-assist-dont-coerce-tooling). Unwrap before member access via `(Read()?).Value` or `match`.

## Qualification

[The delivery plan](../../PLAN.md#holdfast-first-release-delivery) freezes a bounded byte-buffer consumer and independent second client (formats, entry states, expected success/failure) before implementation; parsing, term emission, or unconstrained theorems alone do not pass.

| Subject | Acceptance evidence |
| --- | --- |
| Interpretation and concrete resources | Checked elaboration-image laws, inhabited carrier state, read/write/init/frame/restoration; wrong-offset, alias, premature-restoration, and partial-init neighbors rejected at intended rules (no axiom/source substitutes for missing laws). |
| Scalar and text behavior | Independent boundary fixtures for all types/ops: signed div/rem signs, 0 and MIN/-1, shift 0/width-1/width, exact/wrapping/saturating ops, target vs host width, invalid conversions, embedded NUL, malformed UTF-8/escapes, raw-string delimiter/indent/LF rules, static `IFormat<T>` formatting (`Result<usize, CapacityError>` on exact fit and exhaustion without heap/locale), scalar boundaries, and byte slicing (generated from independent oracle). |
| Package composition | Two independent packages compose with fixed instances; import reordering preserves meaning; overlap, cycles, and conflicting nominal IDs diagnosed; locked builds reproduce closures; contract/rep/assumption/tool edits invalidate stale evidence. |
| Graded dependent typing | Default build checks `NatExact`/`NatBound`, substitution, box/indexed-record elimination, and separate type/computation demands on a reviewed client; bad allowances, altered motives, and stale deps fail at obligations; ordered evaluation and erasure verified at representation endpoint (incl. zero/repeated args). [Default graded checking](#default-graded-checking) |
| Borrowing precision | Default build checks proof-backed symbolic separation, conditional returns, and bounded lending; replays restoration/frame per exit; pairs positives and negatives on held-out clients; records unsupported cases, exhausted budgets, and checking cost. [Default borrow checking](#default-borrow-checking) |
| Everyday ownership | Bounded collection/iterator, `.Model` predicates/slices, `TextBuilder<capacity>`/`IFormat<T>`, [two-phase receiver calls](loan-analysis.md#two-phase-receiver-trial), `invariant Clause: ...` / `open (...) lifts ...`, `CopyRepresentation` + `TransferType<T>`, fallible-builder, and `?` clients pass under actual reps and [borrow promotion](core-design.md#borrow-analysis-promotion) (failing escaped views, duplicated tokens, unwritten/vacant reads, early exits/whole calls under lifted clauses, stale content facts, lost verdicts). Bounded buffer/builder/relocation proofs pass a **capacity-invariance gate**: identical obligation counts and proof/certificate structure at $N = 4$ and $N = 10^9$ (8 and 10⁹ in first-slice pilot) modulo capacity literal, zero per-element unfolding, fitting 4 MiB Gallina and 120 s per-compile/combined replay (reporting actual timings separately). |
| Complete software path | Source and independent contract reach retained backend with checked correspondence, representation, and lowering; final-byte, resource, observation, and admission duties meet owners (source, artifact, production evidence reported separately). |
| Developer usefulness | Measure annotation burden, first useful diagnostic, latency, code/stack/storage impact, and repair cost across preserving refactors, rep changes, and contract changes on both clients (counting arithmetic lemmas/checked ops, effect clauses edited, snapshots/views/loop rewrites, and receiver vs snapshot spellings). |

Hard safety, resource, and admission limits are mandatory; feasibility, recurring developer value, and economic adoption are separate decisions (setup/shared maintenance charged fully without requiring the first two small clients to repay the foundation; size/speed trades require declared envelopes and per-case evidence).

### First-slice component and concrete `Span<byte>` carrier <a id="first-slice-qualification"></a>

[The authored packet validator](../../examples/first_slice.hf) copies header/payload into destination and zero-pads the 8-byte work area, returning a read-only payload view on success, preserving full destination on framing rejection, clearing the work area on other protocol rejections, and preserving all bytes beyond the work area on every exit. [Packet walkthrough](../tooling/packet-walkthrough.md)

`SpecPacketOutcome` gives framing priority over header errors, then checks payload length before checksum, and exports `SpecPacketOutcome(entry) == PacketOutcome(result)` for opaque caller reasoning. At entry, `ref dst` and `in pkt` borrow descriptors with live provenance, bounds, and permissions (extents may overlap); framing reads metadata before any byte access (`FramingShort`), after which success grants exclusive destination and shared packet access and transfers the destination view loan to the result (internal copies enforce entry loans/separation; ordinary calls keep [core loan rules](core-design.md#loans-and-control-flow)).

The generated C harness passes one backing array (`cursor` + logical `base`, initialized equal and advancing together on slice), checking returned cursor/base independently (including empty views) and verifying full destination preservation on overlapping-extent refusal; foreign callers require machine-interpreted descriptor validity before framing interval checks.

The [mathematical carrier](../tooling/elaboration-prototype.md) models `Span<byte>` with store, `Base`, `Length`, `Tag`, `PermRead`, `PermWrite` (`Span.AllocZeroed` for spec/theorems); ops check bounds, representability (incl. exclusive-end overflow), permissions, loans, and disjointness. Restoration requires the immediate or view-updated parent; automatic `restores` checks preserve all five `ref` metadata fields.

#### Qualification and receipt binding

`python tools/run.py holdfast-parser first-slice` runs fresh proof and execution checks owned by [first_slice.py](../../tools/toolchain/first_slice.py):

| Check | Evidence |
| --- | --- |
| Source proof | Menhir parse -> Gallina -> `rocq c` -> assumption audit (empty `solver_trust` for `accepted`) -> `rocqchk`; appended false equality must fail at target def. |
| Capacity and refusals | Equal proof structure and inference/reduction work at capacities 8 and 10⁹; negative fixtures parse without `/*error*/` and fail at expected line/col/category/message. |
| Capability execution | Handwritten purecap checks 4-byte view has data-load permission only; Sail rejects writable-view variant, traps store through narrowed view, and reproduces bounds/tag traps. |
| Optional CompCert execution | Lower validator/drivers to Clight/C, run CompCert `-interp` and Sail purecap images across passing paths and mutated view origin/write-perm/payload/padding/checksum/clearing controls (`--ccomp /abs/path/to/ccomp` requires it; otherwise `compcert_sail.available: false`). [Compiler build contract](https://github.com/symbiogenesis/VerifiedOS/blob/main/docs/implementation/contracts/contained-compiler-reuse.md) |
| Guest C11 regression | System C11 `-O0`/`-O2` checks all 5 exits and verifies cursor, base, length, tag, permissions before payload reads (refusing input-pointing empty/4-byte cursors and writable views). |
| Inline proof erasure | [Native regression](../../tools/tests/test_holdfast_packet_erasure.py) adds assertion/proof/calc to checksum, replays module, and verifies identical guest binaries at `-O0`/`-O2` (false assertion fails elaboration). |

`python tools/run.py holdfast-parser first-slice-bindings <receipt.json>` verifies a schema-2 receipt against checkout/tools by regenerating Gallina and C, reassembling controls, deriving verdicts from transcripts, checking error locations, auditing exports/replay/CompCert inputs, and comparing regenerated C bytes against retained inventories. Compiler-enabled runs also verify entry/return observations via [packet_entry.py](../../tools/toolchain/packet_entry.py) (9 frozen inputs, bytes, restoration, framing-before-access, scalar view fields, rejecting redirected cursors, writable return views, and tagged result-field stores). Missing/substituted artifacts, contradictory transcripts, or mid-run changes fail (inventories capped at 4,096 entries / 256 MiB locally). `status: matched` sets `proof_replayed: false` and lists functional result and returned-view authority under `missing_deployed_evidence` (host runs cannot satisfy deployed target claims per [deployed evidence contract](../assurance/compiler-route-contract.md#evidence-for-each-deployed-claim)). Exact executable acceptance still requires checked source correspondence, canonical Sail resource laws, compiler refinement, contextual preservation, and admission (`inventory` lists missing producers). [Exact executable acceptance](../../PLAN.md#q25ba)
