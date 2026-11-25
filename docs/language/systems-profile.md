# Systems profile qualification

A systems package declares the operations and guarantees it needs from a
target. Each target supplies their representation, ABI, machine laws and
permitted execution contexts under the [target guarantee contract](../assurance/verification-strategy.md#required-guarantees-not-feature-flags).
The synchronous first release uses [caller-owned bounded storage](first-release.md#release-boundary).
The trials below qualify additional claims for a named client, architecture
and build.

## Device ownership across a foreign boundary

Use a third-party driver's safe interface to submit a buffer and retrieve its
completion. The binding states who owns the allocation, its extents, alignment,
read/write permissions, initialization, address stability and lifetime. Bind
the device mapping and address translation to that same backing. On a target
with capability pointers, carry the required bounds, permissions, provenance
and tag through the ABI. An integer descriptor provided by a peripheral
requires validation through the driver's mapping before it can name storage.
Record which boundary facts follow from a checked implementation, which are
checked at entry, and which depend on hardware enforcement or a named foreign
assumption. Treat a foreign routine's promise to stop using a pointer as an
assumption until its implementation or confinement establishes it.

| Event | Observable ownership contract |
| --- | --- |
| Submission succeeds | The device can access only the authorized range. Its grant keeps the backing and mapping live. The host retains only the access allowed by the protocol. |
| Submission fails | Return the specified unchanged or partially submitted state. A handed-off descriptor retains its grant until retired. |
| Cancellation is requested | Record the request. Device completion or a proved abort-and-drain event determines when the last device access has finished. |
| Completion is observed | Establish the required ordering and visibility of payload writes before reading the declared initialized extent. Bind the event to the outstanding request and its generation. |
| Storage is reused | Consume all live grants, account for outstanding translations or cache maintenance where required, then reissue the backing. A late completion for an earlier generation cannot release the new grant. |

Replay completion racing with cancellation, a second submission using the same
backing too early, a late completion after reuse, a descriptor with the wrong
extent, and a doorbell published before its payload becomes visible. A device
which can continue writing indefinitely permits a timeout result that keeps
the backing unavailable. A reclamation deadline requires a bound on device
quiescence or on a containment mechanism that ends its access. The
[publication and reclamation contract](../extensions/interior-mutability.md#immutable-publication-and-reclamation)
owns the memory-order and quiescence laws.

## Low-level operations and portability

Keep scalar, atomic, device and vector operations distinct in the target
interface. A driver package declares which of the following it uses.

| Operation | Required target facts and failure case |
| --- | --- |
| Pointer arithmetic and layout | Relate source offsets, allocation identity, extent, alignment and permissions to the access. Exercise a valid interior view and an equal numeric address presented with stale ownership. |
| Atomic publication | Bind width, alignment, access kind, order, scope and progress requirements to actual instructions and the memory model. Check that a reader cannot observe publication with stale payload. An emulated lock requires its own cost, blocking and interrupt-safety contract. |
| MMIO and DMA | Specify access width, ordering, visibility, coherence and effects of reads and writes. A register read with side effects occurs the declared number of times. A cached ordinary load cannot stand in for it. |
| Vector or intrinsic operation | State lanes, alignment, feature detection and masking semantics on the chosen ISA. Check a tail at the boundary of a valid region, including inactive lanes. A scalar fallback must satisfy the same public behavior, memory-access, leakage and resource requirements. |

Freeze the client, required properties and public API before selecting a second
architecture. Reuse the same source and client proof where their assumptions
hold. Identify every changed representation, primitive proof, foreign contract
and measured cost. Exercise an unavailable target guarantee and report the first
missing law. The [machine contract](../extensions/unified-source-contract.md#machine-model)
owns the instruction and device semantics.

## Runtime costs and reproducibility

State each cost claim as a comparison on a frozen workload. For example, an
erased loan witness should add zero call operands, stores and branches relative
to the hand-written implementation that establishes the same contract. Follow
the [verified abstraction cost protocol](../assurance/workflow-contract.md#cost-of-the-verified-abstraction)
for the final-image comparison. Compare Rust on the same target when its
guarantees, ABI and backend permit that comparison. Attribute costs of a
different hardware representation or trust boundary separately.

The run record binds exact source and public contract, dependency and tool
revisions, target/ABI/ISA features, compiler options, linked image digest,
input classes and the measurement or proof used for each quantity. For each
successful, rejected and cleanup path, report represented witnesses, validation
branches, code bytes, peak stack and live storage, copies, memory traffic,
synchronization and per-case cycles where available. Count dynamic alias
checks, reclamation and device fences when the client uses them. Include code
growth from specialization. Report the proof and checking costs off device,
including changes after replacing a private representation. Rebuild and compare
the artifact identities or record precisely which part of reproduction failed.
The [measurement protocol](../assurance/workflow-contract.md#measurement-record-and-sampling)
governs repeated runs. A sampled cycle count supports a measurement claim.
A worst-case bound requires coverage of the declared inputs, schedules and
target conditions.

## Secret-processing client

Use fixed-length authentication-tag verification as the first client. An
independent specification accepts exactly when every byte of the submitted tag
equals the expected tag. Treat the expected tag as secret, and length and the
submitted tag as public. The caller receives one declassified Boolean result at
the declared output. A separate proof connects a cryptographic primitive to the
expected tag when a client claims message authentication.

Freeze the allowed attacker observations and execution context alongside the
public signature. For any two invocations with the same public inputs, require
equal control-flow and address traces until the verdict is released. If later
behavior branches on the verdict, compare those observations for equal
verdicts. Check independently expected outputs for an equal tag and
for mismatches at the first, middle and last byte. Pair two distinct mismatch
positions yielding the same verdict. A comparison that exits at the first
mismatch passes all the functional examples and fails that trace obligation.

The claim names the actual instruction, cache and scheduling observations
covered on each target. Check source and final-image traces against the same
policy. If the contract requires data-independent instruction latency, name the
applicable instruction and hardware guarantees. A claim covering speculation
also needs a transient-execution model. Record which physical observations
(for example power or electromagnetic emissions) have evidence. Explicitly
authorize any declassification in the policy, including what may be logged or
returned on failure. [Jasmin's verification models](https://jasmin-lang.readthedocs.io/en/v2026.09.0/tools/ct.html)
provide a comparison for ordinary and speculative constant-time checking.

For a component that promises erasure, specify the storage under its control
and the point by which disposal completes. Inventory represented copies,
registers, spills, temporaries, diagnostic output and shared buffers on every
permitted exit. Inspect the final image for a removed clear and unaccounted
copies. Name any memory retained by the caller, foreign runtime or device in
the assumptions. A nonce-using protocol additionally needs its own freshness
contract across retries and restarts, together with the source and assumptions
for keys and randomness. Each claim reports its evidence independently under
the [assurance policy](../extensions/assurance-profiles.md#what-complete-coverage-must-mean).
