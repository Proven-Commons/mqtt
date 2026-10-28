# mqtt: an MQTT 5.0 packet reader and printer, with a proved round trip

Status: in-progress

An MQTT 5.0 control packet reader and printer in Lean,
covering the seven packet types CONNECT, PUBLISH, SUBSCRIBE,
SUBACK, PINGREQ, PINGRESP, and DISCONNECT, with their
property blocks. The reader reads one packet from the front
of a byte list and returns the rest of the input, so a
caller can walk a stream of packets. The definitions are in
`Mqtt/Value.lean` (the packet types, the property table,
the printer, and the well-formedness rules), `Mqtt/Parse.lean`
(the reader), and `Mqtt/Utf8.lean` (a strict UTF-8 codec,
carried in from the Proven Commons `jws` slice with its
namespace renamed, as the header of that file records). The
rules are written out in `SPEC.md`. This slice is framing
only: no broker, no client, and no session behaviour.

The statements a reviewer approves are in `Spec.lean`,
with their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line:
the word `parse`, a space, and the packet as
comma-separated decimal byte codes. It answers `ok:` and
the byte codes of the canonical reprint when the bytes are
one packet, `none` when they are rejected, and `error` when
the request itself is malformed.

```
lake build
echo "parse 192,0" | .lake/build/bin/mqtt
```

That request is a PINGREQ, and the answer is `ok:192,0`: the
packet read back and reprinted. A PINGREQ carrying a body
(`parse 192,1,0`) answers `none`. See `SPEC.md` for the full
protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs the
fixed cases, the differential run against the harness
oracle, the Paho cross-check when the library is
importable, and the mutation and rejection cases, and
writes the outcome to `tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed packet, with more stream bytes after it, gives the packet and those bytes back. | `Spec.parsePacket_print` |
| Parsing the printed form of a well formed packet on its own gives the packet back. | `Spec.parse_print` |
| Reading a printed variable byte integer gives the number back, for every value below 2^28. | `Spec.decVBI_printVBI` |
| What the variable byte integer reader `decVBI` accepts is exactly the printer's writing of the value it returns, which is the shortest writing, followed by the bytes it returns; the value is below 2^28. So a writing longer than the value needs, such as 128, 0 for 0, is refused (section 1.5.5, MQTT-1.5.5-1). | `Spec.decVBI_canonical` |
| Every packet the stream reader `parsePacket` takes is a header byte, the shortest writing of the body length, and that many body bytes, all standing in the input; the bytes it returns are exactly the ones after them. | `Spec.parsePacket_frame` |
| The packet 192, 128, 0 (a PINGREQ whose remaining length 0 is written in two bytes) is refused, while 192, 0 is the PINGREQ. | `Spec.rejects_non_minimal_remaining_length` |
| The variable byte integer reader `decVBI` refuses every input whose first four bytes all carry a continuation mark, whatever follows: the value would need a fifth byte, and four is the limit. | `Spec.decVBI_four_byte_cap` |
| A packet whose remaining length has a continuation mark on each of its first four bytes is refused, by the stream reader `parsePacket` and by the whole input reader `parse`, whatever the header byte and whatever follows. | `Spec.parsePacket_four_byte_cap` |
| A SUBSCRIBE packet with flags 0000 is refused: the value the standard fixes is 0010. | `Spec.rejects_subscribe_flags` |
| A PUBLISH packet with the reserved QoS value 3 is refused. | `Spec.rejects_publish_qos3` |
| A PUBLISH with the DUP flag set at QoS 0 is refused: here the packet 56, 4, 0, 1, 97, 0 (header 0x38). The same packet with header 0x30 is accepted. | `Spec.rejects_dup_at_qos0` |
| A PUBLISH with an empty topic name and a Topic Alias (here 48, 6, 0, 0, 3, 35, 0, 1, alias 1) is accepted, and the same packet with no Topic Alias (48, 3, 0, 0, 0) is refused. | `Spec.empty_topic_needs_alias` |
| A PUBLISH topic name holding a wildcard is refused. | `Spec.rejects_wildcard_topic` |
| A CONNECT whose protocol name is not `MQTT` is refused. | `Spec.rejects_wrong_protocol_name` |
| A CONNECT with the reserved bit of the connect flags byte set is refused. | `Spec.rejects_reserved_connect_flag` |
| A CONNECT whose will flag is clear but whose will QoS or will retain bit is set is refused: here the connect flags 0x0A and 0x22 on an otherwise valid CONNECT. | `Spec.rejects_will_bits_without_will` |
| A property standing on a packet type that does not allow it, here a subscription identifier on a CONNECT, is refused. | `Spec.rejects_property_wrong_type` |
| A single use property standing twice in one block, here the topic alias on a PUBLISH, is refused. | `Spec.rejects_repeated_property` |
| SUBSCRIBE topic filters that break the standard's filter rules are refused, one example input each: `a/#/b` (`#` not last), `a+` (`+` not alone in its level), the empty filter, `$share/g/t` with No Local set, and `$share/g` (no filter after the ShareName). The filters `a/+/#` and `$share/g/t` with No Local clear are accepted. | `Spec.rejects_bad_topic_filters` |
| A SUBSCRIBE with packet identifier 0 is refused. | `Spec.rejects_subscribe_id_zero` |
| Property values the standard calls a Protocol Error are refused, one example input each: a Subscription Identifier of 0 on a SUBSCRIBE, a Topic Alias of 0 on a PUBLISH, a Receive Maximum of 0, a Maximum Packet Size of 0, a Request Problem Information of 2, a Request Response Information of 2, and Authentication Data with no Authentication Method on a CONNECT, and a Response Topic `#` and an empty Response Topic on a PUBLISH. | `Spec.rejects_property_value_rules` |
| The DISCONNECT 224, 1, 0 (a reason code with no property block) reads as that form and prints back as the same three bytes, and the DISCONNECT 224, 2, 0, 0 (a reason code and an empty property block) reads as that form and prints back as the same four bytes. | `Spec.disconnect_short_form` |
| A PINGREQ with a body is refused: its remaining length must be 0. | `Spec.rejects_pingreq_body` |
| A packet type outside the seven in this slice, here type 2, is refused. | `Spec.rejects_unknown_type` |

A packet is well formed when its numbers fit the widths
that carry them, its strings obey the string rules and fit
the two byte length prefix, its properties match the
property table in type and place, keep the value rules
the standard sets (no Subscription Identifier, Topic
Alias, Receive Maximum or Maximum Packet Size of 0, and
so on, as `SPEC.md` lists), and repeat no single use
property, its packet identifiers stand where the
type requires them and are never 0 there, a PUBLISH at
QoS 0 has DUP clear, and its whole
body is shorter than 2^28, the largest remaining length a
variable byte integer can carry. The full list is in
`SPEC.md`.

The round trip theorems rest on the proofs in
`Proofs/RoundTrip.lean`, where they are
`Mqtt.Proofs.parsePacket_print`, `Mqtt.Proofs.parse_print`,
and `Mqtt.Proofs.decVBI_printVBI`. All three check against
the standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms`, or by running
`lake env lean Mqtt/Verify.lean`. The refusal theorems are
single inputs checked in the kernel with `decide +kernel`.
Under the round trips, the field and body steps are proved
one by one in the same file: big endian numbers, byte cuts,
string and binary fields, typed property values, single
properties, property lists and whole property blocks, the
subscription options byte, topic filter lists, and the body
of each of the seven packet types. The UTF-8 round trip,
`Mqtt.Utf8.Proofs.decode_encode`, is proved in
`Proofs/Utf8.lean`, and worked examples from the standard
are proved in `Proofs/Examples.lean`.

The command line tool in `Main.lean` calls `Mqtt.parse`
and `Mqtt.print` directly, the same functions the theorems
are about.

## What is not proved

- That the reader accepts every byte string the standard
  allows, and rejects every one it forbids. The round trips
  do not need either. The variable byte integer, frame and
  four byte cap theorems hold for every input, but the other
  refusal theorems pin single inputs only, so neither holds
  in general as a proof. The
  oracle differential and the mutation tests in `tests/`
  check that behaviour instead, and the results file
  records the outcome, including any failure.
- Any reading of what a property means. A property is an
  identifier and a typed value; that a Receive Maximum of
  10 asks the peer to hold back after ten packets is broker
  and session behaviour, and none of it is in this slice.
- Anything about packets outside the seven types, or
  property identifiers outside the table in `SPEC.md`.
  Both are rejected, and that rejection is tested, apart
  from the single inputs the refusal theorems pin.
- Broker or session behaviour of any kind: connections,
  subscriptions as state, retained messages, keep alive
  timing, and what any peer does with a packet.
- The worked examples on the printing side. The examples
  in `Proofs/Examples.lean` are stated on the reading side,
  because the printer's variable byte integer is defined
  by well founded recursion, which the kernel will not
  evaluate in a `decide` proof here. The round trip
  theorems cover the printer.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, and the decimal number reader. The tests
  cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits
  proofs, not large packets.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker
  shipped with it, which turns the proved definitions into
  the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of the MQTT 5.0
  standard you intend. The proofs are about the reader and
  printer in this repo following each other exactly; the
  fidelity of the spec to the standard is a reading, pinned
  in `SPEC.md` where the standard leaves a choice open.
- The strict oracle in `tests/run_tests.py`, written from
  the standard, and Paho's Python library in the parts of
  the differential it covers. Both are evidence, not proof.
  The results file names the versions used, and states
  plainly which oracles were and were not available.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes). The tests drive it, and no
  proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   differential against the strict oracle, the Paho
   cross-check when the library is importable, and the
   mutation and rejection cases, with counts and any
   failures written to `tests/TEST-RESULTS.md`. The
   harness uses the Paho library from the virtual
   environment in the work directory (`venv`) when it is
   there, and says so in the results file when it is not.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Mqtt/Verify.lean`
   prints the axiom list for the round trip theorems.
4. Read `SPEC.md` against the MQTT 5.0 standard and check
   the pinned readings are the ones you want.
