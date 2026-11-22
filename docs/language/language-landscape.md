# Handler, async and surface design comparisons

These comparisons identify technical approaches relevant to the
[handler and async design](../extensions/handlers-async.md) and the
[Vela surface grammar](surface-grammar.md). Each claim concerns its cited
proposal, implementation or paper.

## Effect-handler disposal routes

OCaml's `discontinue` resumes at the effect site by raising an exception.
An abandoned continuation can retain its captured resources.
[OCaml effect handlers](https://ocaml.org/manual/5.4/effects.html)

Dynamic Wind pairs a suspend clause that releases resources on capture with a
resume clause that reacquires them. Its resource-safety argument concerns a
paper machine instrumented to close resources. That strategy requires
resources that can be released and reacquired, which excludes a loan still
held by a device or in-flight DMA. Vela's handler design requires explicit
[disposal on every relevant exit](../extensions/handlers-async.md#handler-lookup-capture-and-return).
[Dynamic Wind for Effect Handlers](https://pl.cs.uni-tuebingen.de/publications/voigt2025dynamic.pdf)

## Handler scoping and continuation copying

Nearest-handler lookup can intercept an operation in an unrelated dynamically
enclosing handler. Effekt and Lexa instead use lexically scoped capabilities.
Cloning a continuation must also rebind references into its copied frames.
Virtualizing Continuations addresses that with virtual handler addresses.
Vela's [candidate handler representation](../extensions/handlers-async.md#handler-lookup-capture-and-return)
uses delimiter-relative frame references.
[Virtualizing Continuations](https://cs.uwaterloo.ca/~yizhou/papers/multilexa-pldi2026.pdf)

## Automatic resource analysis for handlers

RaML+ annotates operations with potential, uses explicit forwarding and
analyzes linearly typed continuations. Vela can treat an inferred bound for its
one-shot fragment as a candidate for kernel checking. Multi-shot bounds require
separate composition laws. [Handling Exceptions and Effects with Automatic Resource Analysis](https://arxiv.org/abs/2603.02260)

## Async and await design space

Gray, Krishnamurthi and Crichton compare async systems by eagerness, suspension,
extent, reference strength, destruction, propagation and cancellation behavior.
They test a Redex model against language runtimes with generated programs. Vela's
[structured async design](../extensions/handlers-async.md#frames-child-ownership-and-reaction-execution)
uses these dimensions to state its own lifecycle and resource rules.
[A Design Space Exploration of Async/Await](https://arxiv.org/html/2608.20677v1)

## Structured-concurrency runtimes

| System | Relevant behavior in the cited design |
| --- | --- |
| Java | Closing a structured scope waits for subtasks. An unresponsive interrupt can delay closing indefinitely. [JEP 533](https://openjdk.org/jeps/533) |
| Python | `TaskGroup` cancels siblings on failure, waits for them and aggregates non-cancellation exceptions, with special handling for `KeyboardInterrupt` and `SystemExit`. [`asyncio.TaskGroup`](https://docs.python.org/3/library/asyncio-task.html) |
| Swift | A cancellation shield delays observation of cancellation within a lexical block. An awaited `defer` runs before leaving its scope. [Cancellation shields](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0504-task-cancellation-shields.md) · [Awaited `defer`](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0493-defer-async.md) |
| Kotlin | Prompt cancellation can supersede a ready result. A resource in that result needs an explicit cancellation handler. [Prompt cancellation](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/suspend-cancellable-coroutine.html) |
| C++ | Execution distinguishes stopped, value and error completions. An unjoined used `simple_counting_scope` terminates on destruction. [Scope specification](https://eel.is/c++draft/exec.scope) · [Spawn proposal](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p3149r11.html) |
| Rust | The async roadmap describes immovable types and guaranteed destructors as prerequisites for scoped spawn and async drop. [Move-trait project goal](https://goals.rust-lang.org/2026/move-trait.html) |

Vela's [cancellation contract](../extensions/handlers-async.md#cancellation-commit-and-all-exits)
requires accounting for ready results and bounded cancellation. The
[frame rules](../extensions/handlers-async.md#frames-child-ownership-and-reaction-execution)
assign static storage and track each child's exit resources.

## C# unions and Swift spans

C#'s proposed type union `union Pet(Cat, Dog, Bird)` wraps existing case types
and boxes value-type cases. Vela uses [nominal tagged unions](reference.md#declarations)
with explicit cases and exhaustive matching.
[C# union proposal](https://devblogs.microsoft.com/dotnet/csharp-15-union-types/)

Swift's `Span` is a copyable shared view and `MutableSpan` is a noncopyable
exclusive view. Both depend on the lifetime of their source. Vela's
[loan rules](reference.md#loans-and-parameter-modes) similarly distinguish
shared and exclusive views, and name the borrowed place in the lifetime.
[Swift `MutableSpan`](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0467-MutableSpan.md)
