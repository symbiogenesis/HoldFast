# Run the packet validator

A caller gives Vela a packet to read and a separate destination to fill. When
validation fails, can the caller still use the old destination bytes? Run the
same [Vela program](../../examples/first_slice.vela) with three inputs to see
how the answer depends on where validation stops.

Run these commands from the repository root. On Windows, `python tools/run.py`
dispatches to WSL. On Linux, use `python3`. The walkthrough uses the native
Menhir parser, Vela elaborator and a C11 compiler (`cc`). It executes the C
generated from your Vela source on the guest CPU. To try an edit, copy the
validator to another file, pass its relative path with `--source`, and start
each exercise from the original. The command reports source errors and
undischarged packet contracts before it runs the program.

## A short header leaves the destination intact

```console
python tools/run.py vela-parser packet-example "56 02 6B"
```

Each pair is a byte in hexadecimal. The four header bytes hold the magic
value, payload length, checksum and flags. This packet stops just before the
flags. The first guard in `PrepareAndValidatePacket` can reject it using only
the span lengths. The driver fills the working bytes with `CC` and places a
distinct byte, `A5`, immediately past them so writes are visible.

```text
before CC CC CC CC CC CC CC CC A5
Err(FramingShort)
after  CC CC CC CC CC CC CC CC A5
```

**Try breaking the guard.** Change `pkt.Length < 4` in that first `if` to
`pkt.Length < 3`, then rerun the command on your copy. A three-byte packet
can now reach the read of `pkt[3]`. Look for the missing bounds proof.

## A bad checksum clears the working bytes

```console
python tools/run.py vela-parser packet-example "56 02 FF 01 11 22"
```

Here the length and flags pass. The validator copies the two payload bytes
before it checks the checksum. For this payload the checksum is
`5A ^ 02 ^ 11 ^ 22`, or `6B`. The packet supplies `FF`.

```text
Err(ChecksumRejected)
after  00 00 00 00 00 00 00 00 A5
```

**Try clearing one extra byte.** In the checksum rejection branch, change the
count in `Span.Fill(ref dst, 0, 8, 0x00)` to `9`. This would wipe the caller's
`A5` here. It would also exceed the bounds of a destination exactly eight bytes
long. The checker reports that it cannot prove the fill fits.

## Success returns a read-only view of the destination

```console
python tools/run.py vela-parser packet-example "56 02 6B 01 11 22"
```

Only the checksum has changed. The caller can now read the two copied bytes
through the returned view. Its offset is measured from the destination base.

```text
Ok copied=2 offset=4 length=2 read=1 write=0
payload 11 22
after  56 02 6B 01 11 22 00 00 A5
```

**Try writing through the view.** In the last two lines of the validator,
change `let payloadView` to `var payloadView` and insert the following line
before the return. Even when index zero exists and the binding is mutable,
`Span.ReadOnly` has removed write permission. The diagnostic names
`Span.CanWrite`.

```dafny
if (payloadLen > 0) { payloadView[0] = 0x00; }
```

To replay the original source proofs in Rocq and run the Sail capability
controls, use `python tools/run.py vela-parser first-slice`. The
[first-slice qualification](../language/first-release.md#first-slice-qualification)
describes what each check establishes and the evidence still needed for the
target executable.
