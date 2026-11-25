# Hosted application profile

This proposed profile targets applications that use an existing host runtime,
framework and libraries. The [bounded systems release](first-release.md#release-boundary)
remains the supported-release target. An application can use a bounded library
through its published interface. Its host, scheduler, database driver and other
foreign dependencies each contribute their own assumptions.

## Shared language and hosted libraries

The execution profile selects available runtime services. Independently, the
[assurance preset](../extensions/assurance-profiles.md#the-three-presets) selects
which claims need evidence. Choose both at package composition. A library that
declares an allocator or event loop as a dependency can enter a composition
only if the profile supplies it. A change from Safe to Contracted can require
additional properties while retaining the same executable operations. Authored
exported contracts require evidence under either preset.
Ordinary arithmetic, evaluation order, loan and move semantics, observable
failure and authored contracts have the same meaning in shared code. Compare
the two profiles on admitted inputs with the same represented widths.

The first hosted implementation selects one host and its actual ABI. Its
standard library supplies owned text, growable collections, validated external
data, scoped task and resource management, and adapters to the host ecosystem.
Owned text preserves the [shared UTF-8 semantics](first-release.md#bytes-and-text).
An input decoder validates shape, presence, ranges and text encoding before it
publishes typed application data. Each failure identifies its location and
returns the declared error. If decoding borrows foreign storage, its contract
also establishes stability for the view's lifetime.

Each allocating operation declares its allocation effect and the host policy
for exhaustion, including a process failure if that is what the host provides.
The caller may rely on a recoverable outcome only where the operation provides
one. A bounded caller can use an adapter with caller-supplied storage and
explicit capacity failure. The profile names the lifetime model for shared
graphs, its behavior on cycles, and the runtime costs of allocations, retained
handles and collection. The test graph contains a parent, child and subscribed
callback that refer back to each other. Closing the subscription releases its
registration and permits reclamation under the selected lifetime model. Files,
sockets, subscriptions and tasks each have a deterministic close or join
contract independent of heap reclamation.

## Foreign calls and callbacks

Each binding records the actual foreign ABI, representations, text conversion,
ownership on success and failure, effective authority, error translation and
callback contract. Imported declarations identify assumptions and their owners
under the [mixed-assurance rules](../extensions/assurance-profiles.md#composition-across-mixed-assurance).
A binding can copy data into owned storage, pin a moving object's backing for
the call, or transfer a retained handle with an explicit release operation.
The transfer records which side keeps the object live. A native address may
escape the call only with a contract that keeps it valid for the full retention
period. A foreign exception must be contained at the adapter and represented
according to its declared outcome before control returns to HoldFast.

A binding states whether callbacks can run inline, recur, arrive on another
executor, or arrive after cancellation or unsubscription. Before a reentrant
call, the caller restores invariants the callback may observe and accounts for
any exclusive access it retains. Use the [snapshot rules](../extensions/interior-mutability.md#snapshots-and-dependent-indices)
when a callback can change a value that a refinement mentions. Completion or
explicit quiescence releases retained backing. A runtime incapable of supplying
this guarantee needs a copy, an independently owned handle, or a narrower
interface. Exercise collection or relocation during a foreign call, an inline
callback and a late callback after close, and validate malformed foreign values.

## Cancellation and transactions

Structured tasks follow the [cancellation and resource rules](../extensions/handlers-async.md#cancellation-commit-and-all-exits).
The hosted binding specifies its executor, cancellation checkpoints, backpressure,
scope exit, cleanup and any progress assumptions. A timeout ends a wait. The
scope retains the outstanding operation and its resources until their contractual
terminal state. Extracting work into a sequential async helper must account for
every checkpoint, including on the immediately ready path. Compare the original
and refactored traces with cancellation at entry, during a pending operation and
after commit. A new observable checkpoint requires a declared behavior change.

A transaction library identifies the authority that commits the change, the
durable record, the isolation promised by the provider, and the result a caller
can know after a lost reply. A request cancelled before submission can return
with no external effect. Acknowledged commit returns the committed result.
Lost acknowledgement produces an indeterminate result carrying the operation
identity and a recovery path. Retry is permitted only under a declared replay
contract, for example when the same durable key and request contents recover
the same logical outcome. The contract states the retention interval, detects
conflicting reuse of a key, and bounds retries. Once the interval expires,
an unresolved request needs explicit reconciliation. Closing a local task
cannot roll back a remote commit.

## Application acceptance

Freeze one independently chosen hosted application, its host-native C# or
TypeScript implementation, framework and dependency versions, observable
behavior and acceptance thresholds before implementation. Use a real UI event
or HTTP endpoint, a foreign library, persistent storage, input validation, and
cancellation while work is outstanding. Exercise the same workflow across both
implementations, including installation, running, debugging across the binding,
refactoring a helper and upgrading a dependency. Record proof endpoints and
assumptions separately for application code and the foreign runtime.

| Exercise | Required observation |
| --- | --- |
| Incorrect external input and resource exhaustion | A malformed value never acquires its proposed refinement. Capacity refusal preserves the documented caller state. Host allocation failure follows the declared process or recovery policy. |
| Reentrancy and closure | Retained callbacks use live state. Unsubscribing prevents further authorized effects according to the binding, including callbacks already in flight. Every file and registration has one accountable close. |
| Commit, interruption and restart | Inject loss before submission, after durable commit but before reply, and after process restart. Reconcile by operation identity. Replaying the same key produces at most one durable side effect within the promised interval. |
| Daily use | Record setup and authoring time, first useful diagnostic and edit-to-run latency, annotations, repairs after the two changes, framework glue, allocation or copying at the binding, peak memory and request latency. Include failed and abandoned attempts. |

Use the [adoption protocol](../assurance/workflow-contract.md#first-release-qualification-and-adoption)
to judge usability against the frozen task. A successful host-native run supplies
behavioral evidence. Each stronger proof claim identifies its subject, endpoint
and assumptions, including the implementation of any predicate used to admit a
foreign value.
