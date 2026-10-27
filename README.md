# mqtt: an MQTT 5.0 packet reader and printer, with a proved round trip

An MQTT 5.0 control packet reader and printer in Lean, covering the seven packet types CONNECT, PUBLISH, SUBSCRIBE, SUBACK, PINGREQ, PINGRESP, and DISCONNECT, with their property blocks. The reader reads one packet from the front of a byte list and returns the rest of the input, so a caller can walk a stream of packets. The main claim is proved: parsing what the printer wrote returns the same packet. The tests run the tool against a strict oracle written from the standard and, for the pieces it covers, against the Paho Python library; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Mqtt/Value.lean` (the packet types, the property table, the printer, and the well-formedness rules), `Mqtt/Parse.lean` (the reader), and `Mqtt/Utf8.lean` (a strict UTF-8 codec, carried in from the Proven Commons `jws` slice with its namespace renamed, as the header of that file records). The proofs are in `Proofs/RoundTrip.lean` and `Proofs/Utf8.lean`, and worked examples from the standard are proved in `Proofs/Examples.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed packet, with more stream bytes after it, gives the packet and those bytes back. | `Mqtt.Proofs.parsePacket_print` |
| Parsing the printed form of a well formed packet on its own gives the packet back. | `Mqtt.Proofs.parse_print` |
| Reading a printed variable byte integer gives the number back, for every value below 2^28. | `Mqtt.Proofs.decVBI_printVBI` |
| Decoding the UTF-8 encoding of any text gives the text back. | `Mqtt.Utf8.Proofs.decode_encode` |

Under those, the field and body steps are proved one by one: big endian numbers, byte cuts, string and binary fields, typed property values, single properties, property lists and whole property blocks, the subscription options byte, topic filter lists, and the body of each of the seven packet types.

A packet is well formed when its numbers fit the widths that carry them, its strings obey the string rules and fit the two byte length prefix, its properties match the property table in type and place with no single use property repeated, its packet identifiers stand where the type requires them and are never 0 there, and its whole body is shorter than 2^28, the largest remaining length a variable byte integer can carry. The full list is in `SPEC.md`. `parse_print` checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with `#print axioms Mqtt.Proofs.parse_print`, or by running `lake env lean Mqtt/Verify.lean`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the reader accepts every byte string the standard allows, and rejects every one it forbids. The round trip does not need either, so neither is proved. The oracle differential and the mutation tests check that behaviour instead, and the results file records the outcome.
- Any reading of what a property means. A property is an identifier and a typed value; that a Receive Maximum of 10 asks the peer to hold back after ten packets is broker and session behaviour, and none of it is in this slice.
- Anything about packets outside the seven types, or property identifiers outside the table in `SPEC.md`. Both are rejected, and that rejection is tested, not proved.
- Broker or session behaviour of any kind: connections, subscriptions as state, retained messages, keep alive timing, and what any peer does with a packet.
- The worked examples on the printing side. The examples in `Proofs/Examples.lean` are stated on the reading side, because the printer's variable byte integer is defined by well founded recursion, which the kernel will not evaluate in a `decide` proof here. The round trip theorem covers the printer.
- Reading requests and printing answers in `Main.lean`: splitting lines, and the decimal number reader. The tests cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits proofs, not large packets.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict oracle in the test harness, written from the MQTT 5.0 standard, and Paho's Python library in the parts of the differential it covers. The results file names the version used, and states plainly which oracles were and were not available.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 192,0" | .lake/build/bin/mqtt
```

That request is a PINGREQ, and the answer is `ok:192,0`: the packet read back and reprinted. Bytes the reader rejects, such as a PINGREQ carrying a body (`parse 192,1,0`), answer `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3. The test harness uses the Paho library from the virtual environment in the work directory (`venv`) when it is there, and says so in the results file when it is not.

```
lake build
grep -rn "sorry" --include="*.lean" Mqtt Proofs Main.lean Mqtt.lean Proofs.lean
lake env lean Mqtt/Verify.lean
python3 tests/run_tests.py
```

The grep should print only the one line in `Mqtt/Verify.lean` that explains what a `sorryAx` in its output would mean: there is no `sorry` anywhere. The test script rebuilds the tool, runs the fixed cases, the differential against the strict oracle, the Paho cross-check when the library is importable, and the mutation and rejection cases, and writes the counts to `tests/TEST-RESULTS.md`.
