# HoldFast development surface grammar

This document specifies located syntax. The [first-release contract](first-release.md#release-boundary)
selects the synchronous subset and defines [primitive semantics](first-release.md#primitive-semantics)
and [module rules](first-release.md#modules-and-packages). The
[language reference](reference.md) describes which constructs each prototype checks.

The [constant syntax](#required-static-constants) covers required-static evaluation
in the development parser. Generic static parameter binders, derivation registration,
and quotation/splicing are [metaprogramming designs](../extensions/metaprogramming.md).

## Entry points

One authored Menhir grammar owns two public entry points and uses an internal
generic-call prefix probe sharing its generic-argument productions. The internal
probe is not an input/output protocol or a second syntax authority. The `file` entry and
schema 1 serve the pure prototype and its parser comparison. The
`surface_file` entry, selected with `holdfast-parser parse --surface SOURCE`, emits
schema 2 and a `surface_file` node with a module name and declarations. It has no
translation fallback. Pure translation continues to reject wider constructs.
All syntax nodes and names carry original-byte, half-open spans; numeric literals
retain their spelling, including underscores between digits of one base. The
[separator contract](../tooling/authoring-tools.md#numeric-separators) owns placement and
suffix boundaries; only actual digits count toward the literal bound. The
existing UTF-8, source-byte, literal-digit, delimiter,
syntax-depth, duration and output bounds apply to both entries. Save source as UTF-8
without an initial byte-order mark. Both entries identify the mark at line 1, column 1.

## Required syntax

The machine and hardware words `machine`, `hardware`, `state`, `register`,
`transition`, `rule`, `when`, `next`, `schedule`, and `cycle` are contextual
in value positions. Ordinary code can use them as parameter names, local
bindings, expression names, and members. In a hardware update, `next` precedes
a named storage place with optional field and index projections.

An import takes a module path and an optional namespace alias, as in
`import Storage.Blocks as Blocks;`. A selective form lists public names between braces and permits a
per-name alias, as in `import Storage.Blocks { Block, Empty as Free };`. The
list is nonempty and permits a trailing comma. Each alias is a located identifier. The
[module contract](first-release.md#modules-and-packages) defines its scope.

The surface entry must express the following features. Grammar actions only
construct syntax, including syntactically valid programs with semantic errors.

| Area | Syntax acceptance |
| --- | --- |
| Modules and abstraction | Qualified module names, imports, aliases, namespaces, public/private declarations, typed constants, interfaces and implementations, abstract signatures and definitions |
| Data and dependency | Records, structs, tagged unions, fields, constructors, named views, generic types and applications, typed ghost indices, region and capture parameters, grade parameters and annotations |
| Types and resources | Qualified and applied types, ownership, shared/exclusive loans and place-named lifetimes, ghost/tracked/scoped modifiers, function types with captures and effects, dependent binders and universe syntax |
| Contracts | Requires, ensures, restores, where, effects, unnamed and named (`invariant Clause: EXPR`) invariants, selective invariant opening (`open (ref target) lifts Clause, ... { ... }`), and decreasing measures; old/final are ordinary calls |
| Expressions | Literal spellings (including multi-quote raw strings and interpolated format templates) and representation suffixes, qualified access, nested calls, indexing and ranges, unary/arithmetic/comparison/logical operators, implication, pattern tests, explicit generic application, tuples, lambdas and named holes |
| Control | Immutable/mutable and typed locals, required-static local constants, assignments, blocks, returns, if/else, bounded-loop syntax, exhaustive-match syntax, break/continue and explicit propagation |
| Grades | Domain carrier/zero/one/add/mul/admits/interpret/laws declarations and parameter use grades |
| Effects and tasks | Effect operations and resumption bounds, deep/shallow handlers, return/operation clauses, resume/dispose/rehandle, async functions, structured task scopes (`scope (...) { ... }`)/spawn/await/commit and on-cancel cleanup |
| Mathematical proofs | Definitions, theorem/lemma statements, proof blocks, assertions with optional `by` expression or block justifications, calculations, quantifiers, inductive/coinductive declarations and constructors, universes and typed holes |
| Architecture and hardware | Machine/hardware containers, state/register declarations, transitions/rules, guards, next-state assignments and explicit schedules/cycles |

The surface uses type-first declarations and braced containers.
Ordinary explicit generic calls use `F<T>(arguments)` under the
[token-only call rule](#bindings-match-arms-and-generic-calls); explicit generic expression
application retains `::<...>` for function values and disambiguation.
Nested type arguments close with individual `>`
tokens; shifts may use named operations. Generic arguments admit values and
lifetimes. A parenthesized generic value disambiguates relational expressions.
Loop bodies use braces. A function type returning another function type puts that
result in parentheses. Lambdas use `=>`; function types use `->`. Quantifiers use
typed binders followed by `=>`. Proof commands end in semicolons. Architecture/hardware
syntax supplies no transition or circuit interpretation by itself.

Type-first local and callback annotations use bounded lexical lookahead to
distinguish a qualified, applied or parenthesized type followed by a binder from
an expression.
This classification consults token shape, with no symbol table or type judgment.
It preserves the original lexeme positions and the pure entry's tokenization.

The mathematical and machine syntax uses the following spellings.
`Type<u>` names a universe-indexed type, and `effect E` is a generic
effect parameter. `rehandle` takes the same body-and-clauses shape as `handle`.
Inductive/coinductive constructors may add `: TYPE` before their semicolon to
state result indices, for example `Nil() : Vec<T, 0>;`.

```text
module Syntax.Examples;
universe u;
public definition Nat Twice(Nat x) => x + x;
public Nat Increment(Nat x)
    requires x > 0
    ensures result > x
    => x + 1;
public inductive Natural { Zero(); Succ(Natural predecessor); }
public coinductive Stream<T> { More(T head, Stream<T> tail); }
public lemma Reflexive(Nat n)
    requires n >= 0
    ensures forall (Nat x) => x == x
    proof { assert n == n; assert n == n by Reflexive(n); ?step; }
public theorem Witness() ensures exists (Nat n) => n == 0;
public machine Counter {
    state Nat value = 0;
    transition Step() when (value < 10) { next value = value + 1; }
}
public hardware RegisterCounter {
    register u64 count = 0;
    rule Tick() when (count < 10) { next count = count + 1; }
    schedule Main { Tick; }
    cycle 1;
}
```

Proof holes and theorem signatures parse without establishing a theorem. The
[authored surface example](../../examples/surface.hf) combines
dependent data, contracts, loans and task cleanup;
the independent qualification fixtures exercise every feature row above.

<a id="acceptance-and-evidence"></a>

## Syntax and fixtures

### Composable type and resource syntax

The [graded foundation](../extensions/graded-foundation.md#functions-and-application) and
[borrow rules](core-design.md#loans-and-control-flow) use the same parameter,
data and elimination forms throughout the surface:

- Callable types accept the declaration parameter telescope, including optional
  names, grades and nested ownership modifiers: `Fn(Nat n, byte x @ q) -> Vec<byte, n>`.
  Every callable parameter is a located `parameter` node with `name`, `type` and
  `grade` fields; an unnamed argument has a null name. A lambda parameter accepts
  the same optional use grade, for example `(byte x @ q) => x`. Type-use demands
  remain inferred under the foundation's rules, not a second authored annotation.
- `Unit` is the unit type and `()` its value; `(T, U)` and `(x, y)` are product types and
  values. Parentheses around one type or value only group it. Products contain
  at least two components and may nest. Type, value and pattern nodes preserve
  their distinct roles (`type` for `Unit`, `unit`, `unit_pattern`, `tuple_type`,
  `tuple`, `tuple_pattern`). A product pattern uses existing binding patterns:
  `(owner, receipt) => ...`. Local elimination uses
  `let (owner, receipt) = value;`, with an explicit pattern node;
  `var` supports the same shape. A bare `_` is a `wildcard_pattern`, whose
  permission to discard a resource is an elaboration obligation.
  In generic arguments, bare parentheses retain their existing value-expression
  meaning. Prefix a structural type argument with `type`, as in
  `Result<type (owned Packet, tracked Receipt), Error>`; a named type such as
  `Unit` in `Result<Unit, Error>` needs no `type` prefix. This also accepts other
  type forms and avoids guessing whether `(a, b)` names types or values.
- Parametric aliases reuse the existing generic telescope:
  `alias Callback<grade q : NatExact> = Fn(byte x @ q) -> byte;`.
  Named dependent records supply dependent pairs, and indexed unions supply
  outcome-dependent resources. `Box`, `Result`, `Option`, cells, guards and
  protocol tokens remain ordinary library types and operations; they acquire
  no special parser authority or implicit disposal.

Qualification must compose these forms with place-named loans, captures,
restoration, nested reborrows, typestate transitions, dynamic-borrow conflict
branches and cleanup. Independent AST assertions must distinguish parameter
names from their dependent result indices, attach grades to the correct binder,
and retain nested pattern/type roles and original byte spans. Refusal fixtures
cover incomplete binders/grades, malformed products and patterns, and nesting
exhaustion. Semantic mistakes, including duplication, dropping a tracked token,
stale snapshot use and borrowing across suspension, still parse: this entry
supplies syntax for a future checker, not memory-safety acceptance.

### Dependent elimination and library interfaces

The foundation's [dependent elimination](../extensions/graded-foundation.md#dependent-data-and-elimination)
uses the existing record, union and pattern forms. A nonempty expression match
has comma-separated expression arms, with one optional trailing comma, under
the [match arm grammar](#bindings-match-arms-and-generic-calls):

```text
definition Vec<byte, packet.Length> Contents(Packed<byte> packet) =>
    match (packet) as whole : Vec<byte, whole.Length> {
        Packed(length, bytes) => bytes,
    };
```

Both expression matches and statement matches accept the optional
`as NAME : TYPE` motive. The name binds the scrutinee in the result type; branch
substitution and resource compatibility remain checking obligations. A located
`match_motive` node records its `name` and `type`. A match without an annotation
has a null `motive`. Expression matches use `match_expression` and
`expression_case` nodes with `pattern` and `value` fields; statement matches use
`match` and `case` nodes with `PATTERN => { ... }` or `PATTERN => STMT` arms
(`case PATTERN:` is refused as syntax). Incomplete
motives and mixed arm delimiters are refused. Expression
matches compose with calls, operators, lambdas, proofs and nested matches.

Ordinary fields accept the same optional `@ GRADE` as record and constructor
parameters, before an optional initializer. Their `grade` field is null when
omitted. Thus a graded box or retained callback environment can use either record
or struct presentation without a special storage primitive.

Implementation declarations reuse the generic telescope and declaration
contracts: `impl<T, grade q : NatExact> Dup<Box<T, q>> where Repeatable(T, q) { ... }`.
Their `generics` and `contracts` fields contain the same located nodes as other
declarations. Generic binding, instance coherence and the supplied laws are
elaboration obligations. A callable implementation target is parenthesized,
for example `impl (Fn() -> Nat effects(Read)) where Law() { ... }`, so its effect
bound stays distinct from implementation contracts.

Callable types reuse that telescope too, for example
`Fn<region 'loan>(scoped ref<'loan> T value) -> Unit`. Their optional contracts are
explicitly delimited after captures and effects:

```text
alias Update<T> = Fn<region 'loan>(scoped ref<'loan> T value) -> Unit
    with { requires Valid(value); restores Valid(value); };
```

The `with` block contains existing declaration contracts, each terminated by a
semicolon. `function_type` nodes expose `generics` and `contracts` arrays, empty
when omitted. Local binders, loan ancestry, scoped escape, callable invocation
laws and closure disposal require checking; syntax alone grants none of them.
The delimiters distinguish a callback's contract from its enclosing operation's
contract without name resolution or a second contract language.

Independent fixtures must distinguish the motive binder from branch binders,
retain dependent indices, field grades, locally bound regions and contract
ownership, and check original UTF-8 byte spans. Include malformed neighbors and
syntax-valid examples with incompatible branches, escaping loans or invalid
grade/resource use. These extensions keep ancillary boxes, cells, guards and protocols
as ordinary library definitions over shared syntax.

### Resource contracts and lexical handler capabilities

Effect operations reuse declaration contracts after their optional resumption
bound and before the terminating semicolon. Their `effect_operation` nodes expose
a `contracts` array, empty when omitted. The reply type, parameter grades,
resumption allowance and resource transitions remain separate syntax fields:

```text
effect Exchange<T> {
    owned T Replace(owned T replacement @ NatExact(1)) resumes(0..1)
        requires Available(replacement)
        ensures Returned(result)
        restores Closed(result)
        effects writes(Storage);
}
```

Struct, interface, machine and hardware containers accept the same
declaration contracts between their generic telescope and opening brace. Their
`contracts` arrays distinguish container laws from member contracts, for example
`interface Repeatable<T, grade q : NatExact> where Admits(T, q) { ... }` and
`struct LocalCell<T> invariant Closed(this) { ... }`. Abstract callable
signatures inside interfaces and modules use ordinary bodyless function
declarations (`T Read() requires Readable(this) ensures Stable(result);`), and
interface proof laws use bodyless `lemma`/`theorem` declarations
(`lemma ReadLaw(Handle target) ensures Owns(target);`). Theorem and lemma
declarations state their propositions with `requires`, `where` and `decreases`
precontracts followed by one or more `ensures` clauses in their `contracts`
array before `proof { ... }` or `;`; colon-delimited theorem propositions are
refused. The surface entry reserves `trait`, `operation`, and `handle`. Proof signatures
require a `lemma` or `theorem` declaration with its contracts. The pure entry
treats `trait` and `operation` as identifiers. An `invariant` clause may
carry an optional identifier before a colon (`invariant InitializedPrefix: LivePrefix(this.slots, 0usize, this.length)`),
adding a located `name` field to the `contract` node while unnamed `invariant`
clauses omit `name`. An `open` statement names the invariant conjuncts it
temporarily opens (`open (ref this) lifts InitializedPrefix, VacantSuffix { ... }`,
allowing one optional trailing comma). Its `open_invariant` node has `resources`,
a nonempty `lifts` array of located clause identifiers and a `body`; `open`
without `lifts` is refused. `scope (...) { ... }` remains the structured task
scope, whose `scope` node has `resources` and `body` and no `lifts` field.
`open` and `lifts` are reserved keywords in the surface lexer and remain ordinary
identifiers in the pure entry. These forms only preserve
proposed obligations; proving invariant preservation, selective conjunct
independence, lawful grades and operation effects remains an elaboration duty.

The [handler lookup rules](../extensions/handlers-async.md#handler-lookup-capture-and-return)
permit an explicit name for the perform capability of a handler instance:
`handle (body()) as chosen { ... }`. The optional `as NAME` follows the handled
expression and also applies to `handle shallow` and `rehandle`. Each `handle` or
`rehandle` node has a nullable `capability` field holding the located name. Existing
unnamed handlers retain null. Qualified calls such as `chosen.Choose()` reuse
ordinary call/member syntax, without adding another operation primitive.

The capability's intended scope is the handled expression; the handler's clauses
are checked without that capability. Nested bindings, shadowing, forwarding to an
outer capability and rehandling retain distinct syntax identities. Parsing neither
resolves those bindings nor permits an escaping capability, duplicate resumption
or open invariant across capture. Lexical selection, frame identity, `Dup`,
`Dispose` and restoration remain checking obligations under the linked rules.

Independent fixtures must assert operation/container/member contract ownership,
named and unnamed `invariant` clauses, selective `open (...) lifts ...` clause
lists (including trailing commas) beside task `scope` blocks,
dependent reply indices, parameter-grade and resumption-bound attachment, named
and unnamed handler associations, and original UTF-8 byte spans. Compose these
forms with loans, guarded updates, two-step bulk relocation (`CopyRepresentation`
and `TransferType`), indexed outcomes, shallow rehandling and explicit
disposal. Refuse incomplete contract expressions, malformed named invariants
(`invariant : expr`, `invariant Clause:`), named `requires`/`ensures` clauses,
empty or malformed `lifts` lists (`lifts {}`, `lifts , Clause`, `lifts A,, B`),
`open` without `lifts`, `scope (...) lifts ...`, `open` or `lifts` used as a
surface identifier, and incomplete capability binders without
publishing an AST. Syntactically valid violations of capability scope or resource
rules must still parse.

### Type-valued computations and uniform library laws

Type parameters may state a kind using the existing type syntax:
`Box<T : Type<u>, grade q : NatExact>`. A type-mode `generic_parameter`
keeps its `type` field null for a bare binder and records the kind when supplied.
Associated types likewise accept an optional `: TYPE` kind before contracts and
their optional definition; `associated_type.kind_annotation` is null when absent.
Universe formation, conversion and dependent substitution remain checking duties.
Parenthesize a callable kind so its effects stay distinct from declaration contracts.

Explicit `type TYPE` expressions inject structural types into ordinary definitions,
calls and dependent matches. A `type_expression` has a `type` field containing the
located type node. For example, an ordinary type family can return
`match (flag) { true => type (T, T), false => type Unit, }`.
Like lambdas and quantifiers, these forms occupy a complete expression; group them
when used as operator operands. Parenthesize a callable payload, as in
`type (Fn(T value) -> T effects(Read))`, to delimit its effects.
This reuses callable, product and library types
instead of introducing separate type-level function or box primitives.
Bare Boolean, string, character and named-hole generic arguments use their existing
expression nodes, alongside numbers, lifetimes and parenthesized expressions.
Named arguments remain unresolved syntax; this introduces no stable-value judgment.

A callable value may reuse the complete callable type before `=>`:

```text
FnOnce<region 'loan>(scoped ref<'loan> T value @ NatExact(1)) -> T
    captures Environment effects(Read)
    with { requires Open(value); restores Closed(value); }
    => Read(in value)
```

The `typed_lambda` node contains `signature` (the existing `function_type`) and
`body`; its parameters, grades, local regions, captures, effects and contracts
therefore have the same syntax as a callable annotation. Existing inferred lambdas
retain their current nodes. Naming parameters, capture completeness, repeatability,
loan escape and per-call resource transitions require elaboration.

Union, inductive and coinductive declarations accept ordinary declaration contracts
between their generic telescope and body. Constructors accept them after the
optional result type. Pure `definition` and `predicate` declarations accept them
after their parameter telescope and before `=>` (or a predicate's terminating
semicolon). Associated types accept them before an optional `=` definition.
Each of these nodes exposes a `contracts` array, empty when omitted. Thus domain
laws, graded storage, indexed outcomes and type families share the existing
contract language; their laws do not acquire parser authority.
Effects following a bare callable constructor result still belong to that callable;
parenthesize the result to attach an effects contract to the constructor itself.

Independent fixtures must compose kinded binders, type-valued matches, explicit
callable signatures, scoped loans and graded library resources. Assert contract
ownership, signature/body roles, dependent indices, literal spellings and original
UTF-8 byte spans. Refuse incomplete kinds, type expressions, callable signatures
and contracts without an AST; syntax-valid erasure, ownership and grade violations
must still parse.

### Local grades, domain members and disposal clauses

Local value bindings reuse the parameter and field use-grade annotation:
`let value @ q = Make();`, `let T value @ q = Make();` and
`var T value @ q = Make();` (bare `T value @ q = Make();` without `let` or `var`
is refused as syntax). The `let` and `var` nodes
expose a nullable `grade` field alongside `type` and `value`. Both inferred and
explicitly typed bindings accept the same grade expression. Product-pattern
bindings retain their existing form; component modalities belong in their data
types. Checking the binding's allowance, evaluation effects and subsequent uses
remains subject to the [graded foundation](../extensions/graded-foundation.md#functions-and-application).
In particular, zero demand does not erase an effectful initializer.

A named function or method parameter may give callers a stable external label.
In `Nat Read(Nat index as offset)`, the body and contracts refer to `index`
and callers may write `Read(offset: 3)` or `Read(3)`. Without `as`, the local
parameter name supplies the label. Labels in one telescope must be distinct.
Renaming only the local name preserves existing positional and labeled calls.
An interface supplies the labels used by callers. An `impl` may choose its
own local names and may repeat a published label with `as`. A conflicting
explicit label is an error at that label.

The domain roles `carrier`, `zero`, `one`, `add`, `mul`, `admits`, `interpret`
and `laws` introduce entries inside a domain. In value positions they are ordinary
identifiers, including parameter names and member names after a dot. Ordinary paths, type paths
and member expressions can therefore refer to a domain dictionary without new
operator or projection primitives:

```text
definition NatExact.carrier AddZero(NatExact.carrier value) =>
    NatExact.add(value, NatExact.zero);
```

These names preserve the existing located path/member AST forms. For example, `definition Nat add(Nat zero, Nat one) => zero + one;` uses three role names as ordinary values.
Domains also reuse the existing generic telescope and declaration contracts,
for example `domain Product<A : GradeDomain, B : GradeDomain>
where Compatible(A, B) { carrier (A.carrier, B.carrier); ... }`.
Their `generics` and `contracts` arrays are empty when omitted. Compatible product
domains therefore need no separate grammar primitive or assumed algebraic law.

Handlers accept an explicit disposal clause, using the same expression or block
body as their operation and return clauses:

```text
handle (Run()) as chosen {
    Choose() with k => resume k(true),
    return value => value,
    dispose reason => { Cleanup(reason); return (); },
}
```

A `disposal_clause` has a located `name` for the disposal-reason binder and a
`body`. It composes with deep/shallow handlers and rehandlers, sharing their
comma-delimited clause list. The [handler lifecycle](../extensions/handlers-async.md#handler-lookup-capture-and-return)
owns its intended resource context and lexical restrictions: the handler's own
perform capability is absent in its clauses. A disposal clause describes the
declared disposal graph; capture and ordinary return do not invoke it. Parsing neither
invokes cleanup nor supplies a resource-restoration proof; duplicate clauses,
unbound capabilities and invalid disposal bodies still parse as semantic errors.
The existing `dispose continuation` computation retains its separate syntax.

Annotation lookahead must accept callable types inside generic local and lambda
annotations, including nested results, loan modifiers, grades and effects.
Arrows in these types must not close generic argument lists. Independent fixtures
must distinguish local allowance, initializer and lambda-parameter grades, domain
member/path spans, and operation/return/disposal clause ownership. Include nested
handlers, syntax-valid resource violations, malformed neighboring spellings and
bounded-lookahead exhaustion.

### Computed types and uniform elimination

The stable type-valued computations of the [graded foundation](../extensions/graded-foundation.md#stable-telescope-and-dependency-bookkeeping)
can appear wherever a type is expected, through `type[EXPR]`. A `computed_type`
node stores the ordinary expression in its `value` field. This delimited form
reuses calls, dependent matches, local indices and library operations:

```text
definition Type<u> Select<T : Type<u>>(bool pair) =>
    match (pair) { true => type (T, T), false => type T, };
alias Selected<T : Type<u>, ghost bool pair> where Stable(pair) =
    type[Select<T>(pair)];
type[Select<T>(pair)] Read<T : Type<u>>(bool pair);
```

Computed types also work directly as generic arguments, as in
`Box<type[Select<T>(flag)]>`, and in fields, parameters, callable signatures,
local annotations and lambda annotations. The existing `type TYPE` expression
injects structural types into values; `type[EXPR]` uses a type-valued expression
as a type. Parsing establishes neither stability nor purity, universe formation,
conversion, erasure or resource availability. Effectful or ill-kinded type
expressions remain syntax-valid inputs for the future checker.

Aliases accept existing declaration contracts after their generic telescope and
before `=`. Effect families accept them before their opening brace. Their
`contracts` arrays are empty when omitted and distinct from operation or callable
contracts. Grade-domain laws, capture requirements and family invariants therefore
reuse the same contract language as records and other library definitions.

An empty sum's value eliminator uses `match (impossible) as whole : T {}`.
Its `match_expression` node has an empty `cases` array and the existing optional
motive. Like lambdas and type injection, an empty value match occupies a complete
expression; group it when applying operators or postfix operations. A semicolon
distinguishes an empty-match expression statement from the retained bare empty
statement match. Nonempty expression matches use the comma-separated arms above.
Whether the scrutinee has an empty type and which resources can
reach that branch are checking obligations; syntax supplies no inhabitant or
proof. String and character literal patterns reuse their lexical spelling in
`string_pattern` and `character_pattern` nodes, with the same `value` field as
their expression literals; they introduce no decoding or equality operation.

Independent fixtures must compose computed types with kinded parameters,
dependent results, scoped loans, local grades and callable contracts. Assert
expression/type roles, alias/family/member contract ownership, empty-match motive
and statement/expression boundaries, literal pattern spellings and original UTF-8 byte spans.
Include malformed neighbors, bounded nesting and syntactically valid semantic errors.

### Shared operators and local elimination

Parenthesized symbolic operators are ordinary expression atoms. Every binary
operator in the surface precedence table, plus unary `!` and `~`, accepts this
form: `(+)`, `(%)`, `(&)`, `(==>)` and `(!)` are examples. A located `operator`
node retains its located `name`; its span includes parentheses while the name's
span covers only the symbol. Unary and binary uses share `(-)`, `(*)` and `(&)`;
elaboration determines the selected operation and arity under the pointer/loan
rules below and applies the [natural arithmetic boundary](../tooling/elaboration-prototype.md#natural-arithmetic).
Operator values compose with calls,
members, generic application, tuples, lambdas, computed types and ordinary
declaration contracts. Grade-domain entries use these same expressions, including
their existing `(+)` and `(*)` spellings, without a separate domain-value grammar.
Assignment, range, propagation and keyword computations are not operator values.

Local elimination reuses constructor and recursive patterns:
`let Some(value) = optional;` and
`var Ready((owner, receipt)) = outcome;`. Qualified constructors are
accepted. A single parenthesized pattern groups
it, producing `group_pattern` with a `pattern` child; products still require at
least two components. Grouping works in local elimination, match arms and pattern
tests. Local pattern bindings retain `let_pattern`/`var_pattern` with `pattern`
and `value` fields. A bare lowercase local name retains the existing inferred binding form;
a local nullary constructor pattern uses a qualified uppercase path, as in `let Result.Empty = outcome;`.
Union and inductive constructor declarations start with an uppercase letter.
Lowercase or `_` pattern names bind, and uppercase names are constructors; nullary
constructors are written bare without `()`, such as `None`, while empty-argument
constructor patterns `None()` are refused. Component grades remain in their data types. Refutability, constructor arity,
exhaustiveness, ownership and resource disposal are elaboration obligations, so
syntactically valid mistakes still parse.

The grammar shares operator productions between binary expressions and operator
values, and shares recursive type-modifier construction across ordinary,
callable, generic and local-annotation types. Preserve precedence, associativity,
contract ownership, every child in syntax-depth accounting and the pure entry's
schema. Independent fixtures must assert operator and nested pattern roles,
original UTF-8 byte spans, higher-order application and domain compatibility;
exercise every operator spelling and malformed neighboring forms, syntax-valid
resource mistakes and nesting limits.

Equivalent grammar refactors share named-type application, parenthesized type
construction, literal payloads, binary-expression construction, generic-binder
construction and typed local initializers across their existing contexts.
Generic binders retain all six explicit modes and their name/type roles; typed
initializers share their fields and children while the enclosing statement or
expression binding owns its node kind and span. No helper adds a syntax node.
Context-specific tokens and AST roles remain explicit: local
annotations retain lexical disambiguation, literal patterns retain pattern kinds,
and the pure entry retains schema 1. Preserve the exact accepted/refused language,
JSON fields, original byte spans and syntax-depth accounting. Check composed types, literal roles,
quantifiers, lambda boundaries, all generic-binder modes and typed initializer
roles/spans under strict conflict-free generation. Compose erased indices, grade
parameters, callable captures and library-defined resource types in these cases;
syntax-valid name, domain and resource mistakes must remain accepted syntax.

### Expression-local bindings

An ordinary expression may bind a shared subexpression with
`let NAME = EXPR in EXPR`, including the existing optional type and use-grade
annotations. Recursive local patterns use the same constructor/product/group
forms as statement elimination. For example, a type family can compute
`let chosen = Select(flag) in chosen`; a computed type can use
`type[let chosen = Select(flag) in chosen]`. A contract or match arm can bind a
library result without a new type-family, borrow or protocol primitive.

A located `let_expression` contains a `binding` (the existing `let` or
`let_pattern` node) and a `body`. The binding covers `let` through its initializer;
the outer node includes the body. The binder's scope is the body, not the
initializer; name resolution, refutability, grades, effects and resource disposal
remain checking obligations. Bindings associate to the right and occupy a full
expression, like lambdas and quantifiers. Group them for postfix/operator use.
Statement bindings end in a semicolon. Expression-local bindings belong to the
surface entry point.

Independent fixtures must compose nested bindings with dependent types, callable
contracts, grades, constructor patterns, matches and lambdas; distinguish
initializer/body and binder scopes in the AST and preserve UTF-8 byte spans.
Refuse missing initializers, delimiters and bodies; keep syntax-valid resource
errors accepted. Preserve nesting limits, strict conflict-free generation and
every existing surface and pure qualification case.

### Explicit values, loans and absence

The [permanent exclusions](../assurance/verification-strategy.md#permanent-language-exclusions)
fix the semantic design. This syntax-only increment preserves the distinctions
needed to check them; no grammar action performs conversion, proves exhaustive
matching, grants write authority or repairs a missing argument modifier.

Ordinary type-first parameters pass values. Extend the shared type-modifier and
prefix-expression productions with `out`, alongside `in` and `ref`, retaining
modifier order, optional place-named lifetime and original byte spans. The AST
uses the `modified_type` and `unary` nodes. The pure entry diagnoses `out`
as unsupported, alongside the other loan modes.
Add prefix `*` (dereference) and `&` (address/loan derivation) through the shared
unary production, keeping multiplication, bitwise conjunction and parenthesized
operator values distinct. Prefixes associate right; postfix indexing/calls bind
more tightly. Pointer arithmetic uses the existing additive and indexing forms.
Named library types carry pointer representations; no C declarator or `T*` type
suffix is introduced. `->` remains a function-type arrow.

Member calls retain ordinary member/call syntax. The
[receiver rule](../assurance/verification-strategy.md#permanent-language-exclusions) supplies
the selected declaration's receiver loan, including a named view such as
`ref this.Tail`; other arguments retain explicit loan modifiers. Resolution,
once-only receiver evaluation, argument order and overlap remain semantic
obligations. A call rejected for an overlapping argument or an ineligible receiver
still parses; the parser neither chooses a view nor delays a loan.

`let` and `var` locals retain distinct existing AST roles, and bare `T name = value;`
local declarations are refused as syntax (`let` or `var` is mandatory). `Option<T>`, `Some(value)`, `None` and
their constructor patterns use ordinary library syntax. Reserve bare `null` in
the surface lexer and refuse it as syntax, without changing pure tokenization.
Refuse `T?` annotations, null-forgiving postfix `!`, `??` and `?.`. Existing
postfix `?` denotes explicit propagation; prefix `?name` remains a named hole.
Propagation followed by member access uses `(Read()?).Value`.
The contiguous spelling `Read()?.Value` is refused with a diagnostic explaining
that `?` is early-return propagation rather than C# null-conditional `?.` and
offering `(Read()?).Value` (to propagate) or a `match` skeleton (to handle
locally) under the [assist-don't-coerce tooling](../tooling/authoring-tools.md#compiler-verified-assist-dont-coerce-tooling).
The parser still accepts incomplete option matches, immutable writes, mistyped
arithmetic, missing/mismatched loan modifiers and forbidden sharing as located
syntax so the future semantic consumer can report the appropriate obligation.

Use the symbol families consistently:

| Symbols | Syntax roles |
| --- | --- |
| `(...)` | Calls, parameter telescopes, grouping, products and parenthesized operator values; grammar context fixes the role |
| `{...}` | Declaration/statement/proof bodies, match arms, handler clauses and explicitly introduced callable contracts |
| `[...]` | Indexing; `type[...]` explicitly introduces a computed type |
| `<...>`, `::<...>` | Type/generic parameters and arguments, including ordinary generic calls under the token-only rule; explicit generic expression application |
| `->`, `=>`, `==>`, `<==>` | Callable result, lambda/operation/quantifier/match/handler body, implication and equivalence respectively |
| `\|`, `\|\|`, `&`, `&&`, `^`, `~` | Bitwise and Boolean operators with separate fixed precedence; prefix `&` derives an address/loan |
| `*`, `+`, `-` | Multiplication and additive operators; prefix `*` dereferences a pointer and prefix `-` negates |
| `@`, `'place`, `?`, `?name` | Use grade, lifetime identity, propagation and named hole respectively |

Independent fixtures must check default/explicit binding roles, nested
`Option<Option<T>>` and exhaustive constructor matches, value/`in`/`ref`/`out`/
`owned` signatures and arguments, `out` lifetime annotations, unary versus binary
`*`/`&`, pointer arithmetic/indexing, operator values and original UTF-8 spans.
Refuse malformed adjacent forms, C pointer declarators, nullable/null-forgiving
spellings, missing unary operands and chained nonassociative comparisons.
Keep semantically invalid neighbors as positive syntax fixtures, including
partial matches, implicit conversion attempts, immutable reassignment and
overlapping/shared-mutation attempts. Their acceptance is no semantic verdict.

### Concise authoring syntax

- First-class unit types use `Unit`, including `Result<Unit, Error>` and
  `Fn() -> Unit`; the unit value and pattern are `()`. No empty parenthesized
  type spelling is accepted. Ordinary `void` operation declarations retain
  their no-result role and grant no implicit conversion or resource discard.
- Receiver names in declarations, contracts, views, capture sets and
  place-named lifetimes use `this`, including `ref this.Tail` and `'this.text`.
  This is the receiver's source name, not a new authority or permission rule.
- Range iteration uses `foreach (let index in lower..upper)` with a braced
  body and the existing loop contracts. The binder is immutable. Bounds,
  evaluation order/count, representability, decreasing measures, WCET and
  branch/loop-exit loan obligations are unchanged; there is no implicit
  enumerator protocol, allocation, copying, conversion or disposal.
- Calls accept a positional prefix followed by an optional labeled suffix:
  `Copy(in source, target: ref destination, count: length)`. Every label names
  exactly the next declared value parameter; argument slots cannot be skipped,
  reordered, defaulted or repeated. A positional argument after a label is
  refused. Labels on unnamed callable parameters are refused. Explicit generic
  arguments retain their own existing syntax and inference rules.
  The mathematical fragment's partial applications return the remaining
  callable; labels cannot skip its next parameter or supply a default.
  Each argument is evaluated once, left to right, with the same loan timing,
  grades, captures, effects and cleanup obligations as its positional form.
  Dependent application substitutes each argument through the entire remaining
  telescope, including types, grades, captures and exit predicates. Labels
  never supply a conversion, implicit loan, ownership transfer or proof.
  Located `argument` nodes contain an optional `label` and a `value`; label
  names and values retain their original byte spans. Both pure syntax routes
  and mathematical elaboration validate labels against the resolved callable.
- A call argument may declare an output with `out var name`, including after
  an argument label. Its located `out_variable` node spans both keywords and
  the binder. The mathematical elaborator accepts this in standalone calls
  returning `Unit` when it can derive the callee's output value. Each name
  must be fresh in the enclosing local environment and among the call's
  declarations. The mutable locals enter scope together after the call and
  leave scope at the end of its block. Sibling blocks may reuse their names.
- Local bindings use `let name = value` or `let T name = value` for immutable
  bindings, and `var name = value` or `var T name = value` for mutable bindings.
  The optional annotation chooses type inference independently of mutability.
  Bare `T name = value` local declarations without `let` or `var` are refused as
  syntax, directing authors to `let T name = value;` or `var T name = value;`.
  Binding immutability does not prohibit a
  write through an eligible exclusive loan, and the pure prototype reports its
  unsupported mutation boundary without claiming a source borrow judgment.
- Inferred lambda parameters may omit the annotation: `value => value + 1`,
  `(value) => value + 1` and `(left, right) => left + right`. Explicitly typed,
  graded and resource-modified parameters retain their existing forms. An
  omitted annotation is JSON null in the located `lambda_parameter` node;
  existing expected-type inference supplies it or reports an unresolved goal.
  Token shape and delimiters must distinguish lambdas from grouping, products
  and type annotations without consulting names or types.
- Ordinary value-returning functions accept `=> EXPR;` after their signature
  and declaration contracts: `Nat F(Nat x) requires x > 0 => x;`.
  A located `expression_body` node
  contains `value` and covers the arrow through the semicolon. The pure entry
  accepts the same form. Consumers check it as the existing single return,
  preserving evaluation count/order, result type, effects, resources and source
  locations. Mathematical functions use `definition ... => EXPR;` under the
  [body grammar](#bindings-match-arms-and-generic-calls), retaining their distinct declaration
  kind and pure interpretation. An expression body alone does not assert purity.
  Semantic consumers reject
  void shorthand that would discard a result or resource; syntax acceptance
  alone grants no implicit discard.
- Declaration contracts use ordinary operator expressions, such as
  `requires Valid(x)` and `ensures result > x`. A lambda, quantifier, expression-local
  binding or type expression at the root of a clause is parenthesized:
  `requires (forall (Nat n) => Valid(n))` or
  `requires (let n = Limit(x) in n > 0)`. Nested lambdas need no extra grouping,
  as in `requires items.Model.All(x => x > 0)`. The shared operator grammar
  and explicit grouping delimit contracts from a function body's arrow without
  symbol lookup or precedence guesses. The same clause expression rules apply
  to block-bodied functions and other declarations.
- Delimited comma lists for parameters, arguments and generic parameters and
  arguments accept one optional trailing comma after a nonempty list. This
  includes callable, constructor and pattern argument lists. Empty lists with
  a comma and doubled commas are refused. Products keep at least two elements;
  `(value,)` acquires no new tuple or grouping meaning.
- Pattern binders and constructors are distinguished by token shape without
  symbol-table or import-dependent lookup: an unqualified lowercase identifier
  binds a value, `_` remains a discard whose resource admissibility requires
  checking, and an identifier whose final segment begins with an ASCII uppercase
  letter is a constructor (`None`, `BorrowConflict`, `Some(x)`, `Result.Empty`).
  Nullary constructors are written bare without `()` in patterns and expressions;
  empty-argument constructor patterns `Ctor()` (such as `None()`) and uppercase
  pattern binders are refused as syntax. Thus local elimination is
  `let (owner, receipt) = pair;` or `let Ready(buffer, receipt) = outcome;`, and
  both expression and statement matches use `Pattern => ...` arms without `case`
  (`Ok(value) => value,` in an expression match or `Ok(value) => { ... },` /
  `Ok(value) => return value;` in a statement match). The outer local keyword
  selects binding mutability. Located binding/constructor/product nodes have
  distinct roles.

Acceptance requires independently expected AST roles, original UTF-8 spans,
precedence, nesting/resource boundaries and malformed neighbors for every form.
Check labeled and positional call agreement in both pure routes and mathematical
elaboration, including dependent later parameters, callable labels, generics,
shadowing, duplicate/unknown/out-of-order labels, positional-after-label calls
and effectful resource-modified arguments. Check unit values separately from
types, all loop exits and the distinction between rebinding and loan writes.
Compose inferred lambdas with products, calls, explicit generics and dependent
expected types; retain typed/graded loan callbacks and unresolved-inference
refusals. Check expression bodies against equivalent return blocks in both pure
routes and mathematical elaboration, comparing generated terms apart from exact
source provenance. Distinguish lambdas inside declaration contracts from the
expression body. Exercise list forms independently, including nested generic
closers, and distinguish binding names from explicit nullary constructors.
Editor hints follow the [hint contract](../tooling/lsp-prototype.md#authoring-hints).

<a id="familiar-authoring-migration"></a>

### Bindings, match arms, and generic calls

The development parser accepts typed `let`/`var`, comma-separated expression
arms, mathematical `=>` bodies and ordinary generic calls. The pure prototype
checks typed immutable `Nat`/`bool` locals.

**Bindings and aliases.** Local declarations use `let [T] name = value` and
`var [T] name = value` (where `[T]` denotes an optional type annotation), and bare
`T name = value;` declarations are refused. The [primitive contract](first-release.md#primitive-semantics)
owns the exact integer aliases exported by `HoldFast.Numerics`: they require explicit
import or qualification, use ordinary type-name syntax without new keywords,
implicit conversions, suffixes or default integer types, and agree with their
underlying fixed-width types in identity, range, layout and operator selection.

**Match arms and mathematical bodies.** As specified in [Concise authoring syntax](#concise-authoring-syntax),
nonempty expression and statement matches use `PATTERN => ...` arms without
`case` (`case PATTERN:`, `{,}`, doubled commas and missing separators are
refused), and mathematical definitions use `definition ... => EXPR;` while
value initializers, constants, type aliases, associated-type definitions and
grade-domain equations retain `=`.

**Ordinary generic calls.** At a postfix expression followed by `<`, perform a
bounded token-only probe for one complete nonempty generic-argument list ending
in its matching `>`, followed by `(`. Whitespace and comments between these
tokens do not affect the decision. Arguments reuse the existing generic-argument
grammar, including dependent values, lifetimes, explicit structural types,
computed types, optional trailing commas and parenthesized value expressions.
If that complete shape exists, select generic application followed by a call.
Otherwise `<` belongs to the ordinary operator grammar. This is an explicit
lexical classification rule, never a parser conflict default or a choice made
by name resolution, inferred types or import order. Once selected, a malformed
call or semantic error cannot retry as comparisons.

Thus `Outer(F<A, B>(7))` contains one generic call argument, while
`Outer(F < A, B > 7)` contains two comparison arguments. `f < n > (x)` selects a
generic call even if `f` and `n` do not resolve to suitable declarations;
whitespace cannot request another reading. Use parentheses to express the
comparison structure, as in `(f < n) > x`, leaving type validity to checking.
Relational expressions used as generic values remain parenthesized, as in
`Choose<(a < b)>(value)`. Member and computed callees follow the same rule,
including `Library.F<T>(value)` and `factory()<T>(value)`.

`::<...>` remains explicit generic application, including non-call values such
as `Apply(Identity::<Nat>, value)` and explicitly disambiguated calls. Canonical
ordinary calls use `<...>`. Neither spelling changes inference, argument order,
dependent substitution, loans, ownership, effects or evaluation counts. Both
produce the same `generic_application` and enclosing call structure, while
retaining the actual source spelling through original-byte spans. Nested type
closers remain individual `>` tokens; no shift operator is introduced.

Every probe shares the existing source, delimiter, syntax-depth and duration
bounds, plus a declared aggregate token-inspection budget covering unsuccessful
and nested probes. Exhaustion is a resource refusal for the whole parse, never
permission to reinterpret the source as comparisons. No speculative AST or
token rewrite may leak into a failed probe. The implementation freezes the
aggregate bound at 200,000 inspected tokens per parse. Use `F::<T>(...)` to
bypass the prefix probe at that application. The budget is shared across
recursive probes, with boundary fixtures before qualification, retaining the
current source-consumption and diagnostic bounds.

**Qualification.** Independently expected fixtures cover all
four local forms, their AST roles and reassignment diagnostics; aliases versus
underlying types, exact boundary values, explicit conversion refusals, import/name
collisions and alias source identity beside target-type identity; empty,
single and multiple match arms, nested patterns/motives and malformed separators;
mathematical body arrows beside contracts and alias/constant `=`, and both
generic-application spellings beside comparisons. Include nested generic calls,
computed and member callees, higher-order values, parenthesized relational
arguments, all generic-argument modes, trailing commas, comments/newlines,
Unicode byte spans, incomplete delimiters and probe-budget boundaries. Name,
type, purity, grade and resource mistakes must reach their semantic consumer
after successful parsing where their token shape is valid.

### Ergonomic authoring and bounded collection iteration

The parser preserves unsuffixed literals for [contextual inference](first-release.md#contextual-inference).
Collection iteration over represented storage needs the corresponding
[ownership library contracts](first-release.md#ownership-libraries).

**Collection loops.** The following forms select value, shared-read and exclusive
element iteration respectively, with an optional explicit element type:

```text
foreach (let item in values) { ConsumeValue(item); }
foreach (let byte item in values) { ConsumeByte(item); }
foreach (in item in values) { Inspect(in item); }
foreach (ref byte item in values) { Update(ref item); }
```

The element binding is immutable. Value iteration requires permission to copy
each element; it never consumes an owned element implicitly. `in`/`ref` select
the corresponding element loan and its eligible source view. No `out`, `move`
or mutable-rebinding loop binder is introduced. The collection expression is
evaluated once before iteration. A qualified, coherent bounded iterator library
supplies the iteration bound, element access, effects and restoration contract;
there is no ambient enumerator protocol, allocation or implicit disposal.
Checking proves initialization, bounds, representability, termination/WCET and
the resource state on exhaustion, `continue`, `break`, return and propagation.
An element loan cannot escape or overlap the next iteration without a proved
interface permitting it. Mutation cannot invalidate the iteration footprint or
bound. The [ownership library contract](first-release.md#ownership-libraries)
retains all of these semantic obligations.

An unannotated value binder whose source expression is a range retains the
existing `foreach` node and `name`, `range`, `contracts`, `body` fields. Other
forms produce `foreach_collection` with located `name`, nullable `type`, string
`mode` (`value`, `in` or `ref`), `collection`, `contracts` and `body` fields.
Parenthesized range grouping does not change its range role. Explicitly typed
or loan binders over ranges parse as collection syntax; their eligibility is a
checking question. This distinction depends only on syntax, never resolution.
The type, collection, contracts and body all contribute to depth accounting.
Loop contracts retain the range-loop placement before the braced body.

**Sequence model vocabulary in contracts.** In `requires`, `ensures`, `restores`
and `invariant`, a container's logical `.Model` (`Seq<T>`, projected directly or
through `ISequenceModel<T>`) exposes the C#/Kotlin-style pure sequence vocabulary
`.All(x => ...)`, `.Any(x => ...)`, `.Contains(x)`, `.Take(n)`, `.Skip(n)`,
`.Slice(a, b)` and `.Count` alongside `.At(i)`, `.Update(i, v)` and `.Append(x)`.
Authors write `requires items.Model.All(x => x > 0)` rather than raw index
quantifiers. `ISequenceModel<T>` and `IBoundedIterable<T>` reuse ordinary
`interface`, `impl` and `where` syntax to project containers to canonical
`Seq<T>` and connect bounded `foreach` steps to `Model.At(k)`, `Model.Take(k)`
and `Model.Skip(k)`, without importing stateful `IEnumerable<T>` enumerators or
runtime `IQueryable<T>` expression-tree reflection. In the surface grammar these
are ordinary member projections, calls and inferred lambdas inside
`s_contract_expression`, requiring no outer quantifier parentheses and adding no
new reserved words or parser productions. Their standard-library definitions and
pre-proved finite-sequence lemmas belong to the
[ownership library](first-release.md#ownership-libraries) and
[refinement/domain tier](core-design.md#refinement-effects-and-staging).

**Raw string literals and allocation-free checked formatting.** Raw string
literals open with three or more double quotes (`"""..."""`) and close with the
same quote count (`string` in expressions and `string_pattern` in patterns,
retaining the exact authored spelling and original-byte span). Single-line raw
strings contain no line breaks; multi-line raw strings require a newline after
the opening delimiter, a closing delimiter on its own whitespace-indented line,
and at least that closing indentation prefix on every non-empty content line.
Excess closing quotes, missing opening/closing line breaks and under-indented
content lines are syntax refusals. Interpolated format templates `$"..."` parse
as located `interpolated_string` expression nodes with their original-byte
`span` and raw `value` spelling. Holes `{expr}` and `{expr:spec}` require a
non-empty expression, balanced delimiters within the delimiter budget and an
optional non-empty format specifier without whitespace or quotes; literal braces
use `{{` and `}}`. Unterminated templates, empty holes (`{}`), empty or
whitespace-containing specifiers (`{x:}`), unescaped closing braces and `$"..."`
in pattern positions are syntax refusals. Under the
[text and ownership contracts](first-release.md#bytes-and-text), `$"..."` is not
a heap-allocating `string` value: it is elaborated only as the format template
of an explicit buffer-writing operation such as `Format.Write(ref builder, $"...")`
targeting `ref TextBuilder<capacity>` or `ref Span<byte>`, resolving a coherent
static `Format<T>` instance per hole (no runtime reflection, virtual `ToString()`
or ambient locale) and returning `Result<usize, CapacityError>`. Standalone
`$"..."` bindings, missing `Format<T>` instances, unexamined
`Result<usize, CapacityError>` outcomes and hole expressions that conflict with
the active `ref` target loan remain valid syntax for the semantic and borrow
checkers to diagnose.

**Lightweight `by` justifications on `assert`.** Assertions accept an optional
Dafny/Verus-style `by` justification: `assert EXPR;`, `assert EXPR by EXPR;`
(terminated by a semicolon, typically a lemma or proof-carrying call) and
`assert EXPR by { ... }` (a braced block of intermediate `let` bindings and
`assert` steps, requiring no trailing semicolon after `}`). Every `assert` node
exposes located `value` and nullable `by` fields (`null` for a bare assertion,
the located expression node for `by EXPR;`, or the located `block` node for
`by { ... }`). `by` remains a reserved keyword in the surface lexer.

**Conditional expressions, constructor-pattern labels and record updates.**
In expression positions (`let` initializers, `=>` expression bodies, `return`
values, call arguments, contracts and nested expressions), `if (COND) THEN else ELSE`
parses as a located `if_expression` node with `condition`, `then` and mandatory
`else` fields, avoiding ternary `?` ambiguity (where `?` remains postfix error
propagation and prefix typed holes) and desugaring to an exhaustive Boolean
elimination with the same resource join as a two-arm `match`. Statement-start
`if` retains its statement production without LR(1) conflict by restricting
bare statement expressions and assignment targets to `s_statement_expression`.
Constructor patterns `Path(arg, ...)` accept positional sub-patterns or a
positional prefix followed by declaration-order `label: pattern` arguments
(`labeled_pattern` nodes with located `label` and `pattern` fields), matching
call-expression label order without symbol-table lookup during parsing. Postfix
`BASE with { Field = EXPR, ... }` (allowing one trailing comma) parses at unary
precedence as a located `with_expression` node with `value` and nonempty
`updates` (`field_update` nodes carrying `name` and `value`), so `move packet with { ... }`
binds `move packet` as the base `value` expression. It does not conflict with
callable-type `with { requires ...; }` (only in `Fn`/`FnMut`/`FnOnce` types) or
handler `with k =>`. Evaluation proceeds left-to-right in declaration order;
linear or affine records require `move base with { ... }` so unreplaced fields
transfer cleanly and replaced resources are accounted for.

**Scoped early-exit guards, flow-refined `is` and total read-only expression properties.**
Inside blocks, `let [grade] [T] PATTERN = EXPR else { ... }` and `var [grade] [T] PATTERN = EXPR else { ... }`
parse as located `let_else` and `var_else` statement nodes with `grade`,
nullable `type`, `pattern`, `value` and braced `else` block fields (`else`
takes a block without a trailing semicolon). The `else` block must exit the
enclosing scope (`return`, `break`, `continue` or diverging handler/propagation)
and discharge non-matching resources, leaving the pattern's bindings in scope for
the remainder of the enclosing block. In conditional headers, `if (EXPR is PATTERN)`
binds `PATTERN`'s variables in the `then` branch and refines the complement in
`else` under the same exhaustive split. In `if (item is Some(n) && n > limit)`,
a successful match binds `n` for the right operand and the true branch. Further
`&&` operands can introduce additional patterns. Each operand runs only after
all preceding operands succeed. Grouping preserves this scope. Bindings end
at the false branch, the end of the conditional, or a surrounding `||`.
At module, `record`, `struct`, `union`
and `impl` declaration scope, `[visibility] [ghost] T Name [contracts] => EXPR;`
parses as a located `property` declaration with `visibility`, `ghost`,
`attributes`, `modifiers`, `name`, `return_type`, `contracts` (excluding
`effects` clauses) and `body` fields. `async` and `const` modifiers, parameter
lists, `effects` clauses and `set` accessors are syntax refusals on properties,
guaranteeing that `a.B` is always a total, allocation-free, effect-free read of `a`.

**Pure typed locals and binding guidance.** Both pure syntax routes accept
`let Nat count = value;` and `let bool ready = value;`, and refuse bare
`Nat count = value;` and `bool ready = value;` as syntax. The annotation must equal the
initializer's checked type; it grants no coercion or mutation. In schema 1 an
annotated `let` adds a located `type` field to its existing local node; unannotated
`let` keeps its existing shape. The shared pure binding records the optional
annotation independently of its value. Wider types and mutable locals retain
their unsupported-feature diagnostics. The formatter preserves whichever accepted spelling was authored.

**Qualification.** Independently expected fixtures cover both pure local routes,
annotation mismatch, shadowing, original UTF-8 spans, comments/mixed newlines and
unchanged interpreted terms apart from source provenance. Collection fixtures
distinguish all modes, optional qualified/applied types, range/grouped-range
compatibility, nested loops, contracts and exits. Text and formatting fixtures
cover single-line and multi-line raw string literals (including embedded quotes,
backslashes and pattern matching), `Format.Write(ref builder, $"...")`
interpolated templates with expressions, format specifiers and escaped `{{`/`}}`
braces, syntax-valid semantic error neighbors (standalone `$"..."` value
bindings and conflicting receiver reads inside holes), and syntax refusals for
malformed raw-string delimiters/indentation, empty or unclosed interpolation
holes, malformed specifiers, unescaped braces and interpolated patterns.
Expression, pattern, update, guard and property fixtures cover `if_expression`
(including nested conditionals), declaration-order `labeled_pattern` arguments,
`with_expression` record/model updates (including `move base with { ... }` and
trailing commas), `let_else`/`var_else` guards, `if (x is Pattern)` branch
refinements, and read-only `property` declarations (including `ghost` and
`ensures` contracts), alongside syntax refusals for `if` expressions without
`else`, statement-start `if` expressions, empty or colon-written `with {}`
updates, non-block `let ... else`, missing `labeled_pattern` sub-patterns, and
`async`, `const`, `effects` or setter-block properties. Refuse
incomplete binders,
missing `in`, malformed annotations and budget exhaustion without an AST. Keep
syntax-valid borrowing, copying and cleanup violations for the semantic checker
to diagnose. Bind consumer facts to exact source and follow [native qualification](#native-qualification).
Represented inference and iterator acceptance require independent positive and
invalid-neighbor cases through their actual future producers; parser success
and an unsupported-feature refusal supply neither verdict.

### Required-static constants

The compositional constant interface has three placements. `const T F(...)`
declares a function that supports constant evaluation and remains callable with
runtime arguments. `T F(const U input, V value)` requires `input` during
compilation while `value` may be runtime data. `const T Name = EXPR;` requires
the initializer's result during compilation. No separate compile-time-only
function category or `const(expression)` form is introduced.

A constant-compatible function checks its supported pure body symbolically.
Its parameters need not themselves be declared constant: supplied static values
make its ordinary evaluator locals static during that invocation. Existing
admitted total pure functions remain eligible for constant evaluation; the
function modifier records an explicit checked promise without breaking those
calls. Unsupported effects, resources, mutation and opaque external calls retain
their existing refusals, including in dead branches.

A `const` parameter is an immutable, required-static value binder. Its type and
availability are checked at every application, including labeled, generic,
partially applied and higher-order applications. A definition checks symbolically
under that declared availability; a demanded closed instantiation must resolve
its static arguments before evaluation. Local constant initializers may depend
on such binders and earlier constants. An unmarked runtime or ghost binder is
not promoted by an ignored argument, dead branch, inlining or optimization.
Forwarding a static parameter preserves its requirement. Specialization computes
the demanded constant locals while retaining runtime inputs and declaration-order
call-by-value evaluation. An unchanged mathematical template is a logical
definition, not evidence that a production backend erased a static parameter.

Both Menhir entries and the pure Python route preserve these distinctions.
The pure function and parameter nodes carry an optional Boolean `const` field,
omitted for ordinary declarations. Surface function modifiers include `const`;
surface parameter nodes use the same optional Boolean field. Consumers bind the
flag to the source keyword and refuse invented, missing or repeated qualifiers.
Callable parameter requirements survive the mathematical consumer's function
types, explicitly typed lambdas and substitution. Contextual lambdas inherit
the expected static-parameter requirement; a conversion cannot discard it.
Editor signatures identify constant functions and static parameters without
evaluating source in the protocol adapter.

```text
public const Nat Square(Nat value) => value * value;
public const Nat Limit = Square(4);
public Nat Scale(const Nat factor, Nat value) {
    const Nat multiplier = Square(factor);
    return multiplier * value;
}
public Nat Runtime(Nat value) => Scale(factor: Limit, value: value);
```

`Square(value)` is also valid with an ordinary runtime input. `Scale` requires
only its factor statically; its multiplication still processes runtime data.
Passing an unmarked runtime factor is refused at that argument. These examples
use the current mathematical scalar fragment. Its
[static table evaluator](../tooling/elaboration-prototype.md#frozen-static-tables)
also freezes bounded vectors, including string literal bytes. Format plans,
scratch mutation and target materialization retain their frontend and
representation prerequisites. A static initializer value can seed mutable
storage, but local initialization may still copy bytes on each invocation;
placement in a composed image determines static storage initialization.

`const T Name = EXPR;` declares an immutable value whose initializer must be
evaluated during compilation. The explicit type is mandatory. Constants may be
module or container members, with ordinary visibility modifiers, or local
statements. A constant denotes a value, not a zero-parameter function; `Limit`
may index `Vec<Nat, Limit>`, while `Limit()` is a call on a non-callable value.
The unit type is `Unit`; a zero-parameter callable and a callable with an explicit
`Unit` parameter have distinct source arities despite their shared CIC encoding.

Initializers may use earlier constants and admitted total pure functions applied
to static arguments. Surrounding runtime parameters, ordinary `let`/`var`
bindings and unmarked generic or ghost indices are not constant-expression inputs.
Check dependencies before reduction: a dead branch or unused argument cannot
hide a forbidden input, effect, resource or authority. Parameters and ordinary
locals inside a pure function evaluated with static arguments are evaluator
locals; this does not promote surrounding runtime bindings into constants.
Explicit static parameters supply the additional admitted symbolic inputs;
forward and cyclic constant dependencies are refused.

Evaluation has finite work, reduction, numeric and output bounds. Failure,
unavailable input or exhaustion is a located refusal without a runtime fallback.
Use mathematical arithmetic or the selected target's checked representation;
host widths and layouts supply no target constant semantics. Required-static
availability grants no conversion, ownership, duplication, erasure, proof or
unchecked optional extraction, and `ghost` alone supplies no static input.

The pure prototype evaluates `Nat` and `bool` constants in both syntax routes.
The mathematical consumer also admits `Unit`, `char`, represented words and
bounded vectors of static values. Emit the evaluated
value with its declared type; retain source-bound resolution and diagnostics.
Neither evaluator parses emitted Gallina or uses an unchecked host `eval`.

Both parser entries preserve declaration order. The pure `file` has a
`declarations` array containing functions and `constant` nodes, each constant
carrying `name`, `type` and `value`. Local `constant_local` nodes have those same
located fields. The surface declaration also carries its ordinary modifiers.
The checker records constants as distinct resolved symbols; editor navigation,
references, hover and document symbols consume those facts without evaluating
source in the protocol adapter. Explicitly typed constants need no inferred-type
hint. Invalid or changed initializers invalidate the complete snapshot.

Acceptance requires independently expected values and types for literals,
arithmetic, comparisons, earlier constants, named pure calls and function-local
evaluation. Compare both pure routes and mathematical emission, including a
constant used as a dependent index. Refuse wrong types, runtime/erased inputs,
ignored or dead forbidden dependencies, forward/cyclic references, constant
reassignment/calls, missing type/initializer, malformed spans and exhausted
budgets. Check mixed-newline/UTF-8 editor positions and invalidation. Native fixtures must reach the intended semantic diagnostic.

The compositional increment additionally requires runtime and static calls of the
same constant function; static-factor/runtime-data specialization with an
independently expected literal; static-parameter forwarding; declaration-order
labeled calls; dependent and higher-order function-parameter preservation; refusal
of runtime, erased, ignored and dead forbidden dependencies; bounded symbolic
checking and closed evaluation; source-token mutations of every qualifier; and
current-overlay editor signatures and navigation. Native generation remains
strict and conflict-free. No valid literal alone establishes a folding theorem,
source correspondence or production compiler admission.

### Native qualification

Menhir's code backend must generate with `--strict --infer --explain`, with no
unresolved conflicts and no unchecked runtime dependency. Preserve exact locked
generator/compiler checks and fresh-generation comparison. Use independently
authored fixtures covering every row, nested combinations, expected AST roles,
precedence and byte spans. Reject malformed declarations, incomplete input,
trailing tokens and exhaustion without an AST. Lex comments and literals without
changing delimiters or keyword interpretation inside them.

`holdfast-parser qualify` must run both the retained pure cases and the surface cases,
bind all fixture inputs into its receipt, and retain separate syntax verdicts.
See [parser qualification](../tooling/parser.md) for the locked-toolchain checks.
