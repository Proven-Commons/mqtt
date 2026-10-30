# mqtt: an MQTT 5.0 packet reader and printer, with a proved round trip

Status: in progress

An MQTT 5.0 control packet reader and printer in Lean,
covering the seven packet types CONNECT, PUBLISH, SUBSCRIBE,
SUBACK, PINGREQ, PINGRESP, and DISCONNECT, with their
property blocks. The reader reads one packet from the front
of a byte list and returns the rest of the input, so a
caller can walk a stream of packets. The definitions are in
`Mqtt/Value.lean` (the packet types, the property table,
the printer, and the well-formedness rules), `Mqtt/Parse.lean`
(the reader), and `Mqtt/Utf8.lean` (a strict UTF-8 codec,
copied from Proven-Commons/jws#2, a draft pull request not
yet merged, with its namespace renamed; its proof is
included here as `Mqtt/Proofs/Utf8.lean`). The
rules are written out in `SPEC.md`. This slice is framing
only: no broker, no client, and no session behaviour.

The statements a reviewer approves are in `Mqtt/Spec.lean`,
with their proofs in `Mqtt/Proofs/SpecProofs.lean`. No reviewer
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
importable, the mutation and rejection cases, and random
packets of each forbidden class drawn from the seed, and
writes the outcome to `tests/TEST-RESULTS.md`: the
oracle, the seed, the input count and the failures.

`python3 tests/plant_bugs.py` plants small bugs in the
reader and its rules, one at a time in a scratch copy of
the repo: a five byte cap, longer writings of a variable
byte integer accepted, short input padded with zeros,
partial weakenings of the filter and value rules, and
more. For each it names the approved statement the plant
makes false, checks that the test harness reports a
failure and that the proofs no longer build, and writes
the outcome to `tests/PLANTED-BUGS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Mqtt/Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Mqtt/Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them. A claim that names
its input, or says "one example input", is a theorem
about that input alone, which a reader can check by
evaluation; the rule it illustrates is stated for every
input by the theorem it names after "every input". The
rules those theorems state are written in
`Mqtt/Spec/Defs.lean`, one of the spec files an approval
covers.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed packet, with more stream bytes after it, gives the packet and those bytes back. | `Mqtt.Spec.parsePacket_print` |
| Parsing the printed form of a well formed packet on its own gives the packet back. | `Mqtt.Spec.parse_print` |
| Every packet the whole input reader `parse` accepts is well formed, and printing it gives back exactly the bytes it read. With the row above, `parse` accepts a byte list exactly when it is the printing of a well formed packet, and refuses every other byte list. | `Mqtt.Spec.parse_sound` |
| Every packet the stream reader `parsePacket` takes from the front of a byte list is well formed, and the bytes it took are exactly its printing, followed by the bytes it returns: it never takes a byte the input does not hold. | `Mqtt.Spec.parsePacket_sound` |
| Reading a printed variable byte integer gives the number back, for every value below 2^28. | `Mqtt.Spec.decVBI_printVBI` |
| What the variable byte integer reader `decVBI` accepts is exactly the printer's writing of the value it returns, followed by the bytes it returns; the value is below 2^28. So each value has one writing the reader accepts. | `Mqtt.Spec.decVBI_canonical` |
| The printer writes every value below 2^28 in `Mqtt.Spec.vbiSize` bytes, the fewest that carry it: one byte below 2^7, two below 2^14, three below 2^21, four below 2^28 (`Mqtt.Spec.vbiSize` is written in `Mqtt/Spec/Defs.lean`). | `Mqtt.Spec.printVBI_length` |
| For every input, what `decVBI` accepts uses exactly `Mqtt.Spec.vbiSize` bytes for the value it returns. So a writing longer than the value needs, such as 128, 0 for 0 or 128, 129, 0 for 128, is refused (section 1.5.5, MQTT-1.5.5-1). | `Mqtt.Spec.decVBI_length` |
| Every packet the stream reader `parsePacket` takes is a header byte, the printer's writing of the body length (the shortest, by the row above), and that many body bytes, all standing in the input; the bytes it returns are exactly the ones after them. | `Mqtt.Spec.parsePacket_frame` |
| The packet 192, 128, 0 (a PINGREQ whose remaining length 0 is written in two bytes) is refused, while 192, 0 is the PINGREQ (every input: `Mqtt.Spec.decVBI_length` with `Mqtt.Spec.parsePacket_frame`). | `Mqtt.Spec.rejects_non_minimal_remaining_length` |
| A writing longer than the value needs is refused in the other places a variable byte integer stands, one example input each: the PUBLISH 48, 5, 0, 1, 97, 128, 0 (property length 0 written 128, 0), the PUBLISH 48, 7, 0, 1, 97, 3, 129, 0, 1 (property identifier 1 written 129, 0), and the SUBSCRIBE 130, 11, 0, 1, 3, 11, 129, 128, 0, 0, 1, 97, 0 (Subscription Identifier 1 written 129, 128, 0); the same packets with the shortest writing are accepted. No statement covers every input in these places (see What is not proved). | `Mqtt.Spec.rejects_non_minimal_property_vbis` |
| The printer writes each value of the standard's worked table in section 1.5.5 as the bytes the table gives: 0 as 0, 127 as 127, 128 as 128, 1, 16383 as 255, 127, 16384 as 128, 128, 1, 2097151 as 255, 255, 127, 2097152 as 128, 128, 128, 1, and 268435455 as 255, 255, 255, 127; and `decVBI` reads each of those writings as its value. These rows only. | `Mqtt.Spec.vbi_worked_table` |
| The variable byte integer reader `decVBI` refuses every input whose first four bytes all carry a continuation mark, whatever follows: the value would need a fifth byte, and four is the limit. | `Mqtt.Spec.decVBI_four_byte_cap` |
| A packet whose remaining length has a continuation mark on each of its first four bytes is refused, by the stream reader `parsePacket` and by the whole input reader `parse`, whatever the header byte and whatever follows. | `Mqtt.Spec.parsePacket_four_byte_cap` |
| The whole input reader `parse` accepts a byte list, and returns a packet, exactly when the stream reader `parsePacket` takes that packet from it and leaves no byte after it. So each rule below, stated for `parsePacket`, holds for `parse` too. | `Mqtt.Spec.parse_whole` |
| For every input, each packet `parsePacket` takes starts with one of the sixteen header bytes of `Mqtt.Spec.headerBytes`: 0x10, 0x30 to 0x35, 0x3A to 0x3D, 0x82, 0x90, 0xC0, 0xD0 and 0xE0. So a SUBSCRIBE whose flags are not 0010, another type whose flags are not 0000, a PUBLISH with QoS 3 or with DUP set at QoS 0, and every packet type outside the seven of this slice are refused. | `Mqtt.Spec.header_rule` |
| For every input, each CONNECT `parsePacket` takes is the byte 0x10, the body length, and a body that starts with the protocol name `MQTT` (0, 4, 77, 81, 84, 84), the level 5, and a connect flags byte that keeps `Mqtt.Spec.ConnectFlagsRule`: the reserved bit 0 clear, a will QoS other than 3, and, when the will flag is clear, the will QoS and will retain bits clear. A will topic is not empty and holds no `+` or `#`. | `Mqtt.Spec.connect_rule` |
| For every input, each PUBLISH `parsePacket` takes has a topic name with no `+` or `#`, which is empty only when its properties carry a Topic Alias; its packet identifier stands exactly when the QoS is not 0, and is never 0. | `Mqtt.Spec.publish_rule` |
| For every input, each SUBSCRIBE `parsePacket` takes has a packet identifier other than 0 and at least one topic filter, and each filter keeps `Mqtt.Spec.FilterRule`. A filter is not empty; split at each `/`, a level that holds `+` is `+` alone, and a level that holds `#` is `#` alone and the last level. A filter that starts with `$share/` has a ShareName of at least one character with no `/`, `+` or `#`, then a `/` and a filter that keeps those rules, and its No Local option is clear. | `Mqtt.Spec.subscribe_rule` |
| For every input, every property block of every packet `parsePacket` takes keeps `Mqtt.Spec.BlockRule`. Each property is allowed on its block (Table 2-4) and has its identifier's value type. Each value keeps the value rules: no Subscription Identifier, Topic Alias, Receive Maximum or Maximum Packet Size of 0, a Request Problem Information and Request Response Information of 0 or 1, and a Response Topic that is not empty and holds no `+` or `#`. No single use property repeats in a block, and Authentication Data stands only with an Authentication Method. | `Mqtt.Spec.property_rule` |
| For every input, each PINGREQ `parsePacket` takes is the two bytes 192, 0, and each PINGRESP the two bytes 208, 0. | `Mqtt.Spec.empty_body_rule` |
| The SUBSCRIBE 128, 7, 0, 1, 0, 0, 1, 97, 0, whose flags are 0000 rather than the 0010 the standard fixes, is refused (one example input; every input: `Mqtt.Spec.header_rule`). | `Mqtt.Spec.rejects_subscribe_flags` |
| A PUBLISH with the reserved QoS value 3 is refused (one example input, header 0x36; every input: `Mqtt.Spec.header_rule`). | `Mqtt.Spec.rejects_publish_qos3` |
| A PUBLISH with the DUP flag set at QoS 0 is refused: here the packet 56, 4, 0, 1, 97, 0 (header 0x38). The same packet with header 0x30 is accepted (every input: `Mqtt.Spec.header_rule`). | `Mqtt.Spec.rejects_dup_at_qos0` |
| A PUBLISH with an empty topic name and a Topic Alias (here 48, 6, 0, 0, 3, 35, 0, 1, alias 1) is accepted, and the same packet with no Topic Alias (48, 3, 0, 0, 0) is refused (every input: `Mqtt.Spec.publish_rule`). | `Mqtt.Spec.empty_topic_needs_alias` |
| A PUBLISH whose topic name is `a/#` is refused (one example input; every input: `Mqtt.Spec.publish_rule`). | `Mqtt.Spec.rejects_wildcard_topic` |
| A CONNECT whose protocol name is `MQTU`, not `MQTT`, is refused (one example input; every input: `Mqtt.Spec.connect_rule`). | `Mqtt.Spec.rejects_wrong_protocol_name` |
| A CONNECT whose connect flags byte is 0x03, with the reserved bit 0 set, is refused (one example input; every input: `Mqtt.Spec.connect_rule`). | `Mqtt.Spec.rejects_reserved_connect_flag` |
| A CONNECT whose will flag is clear but whose will QoS or will retain bit is set is refused: here the connect flags 0x0A and 0x22 on an otherwise valid CONNECT (every input: `Mqtt.Spec.connect_rule`). | `Mqtt.Spec.rejects_will_bits_without_will` |
| A CONNECT carrying a Subscription Identifier, which its property block does not allow, is refused (one example input; every input: `Mqtt.Spec.property_rule`). | `Mqtt.Spec.rejects_property_wrong_type` |
| A PUBLISH carrying the single use Topic Alias twice is refused (one example input; every input: `Mqtt.Spec.property_rule`). | `Mqtt.Spec.rejects_repeated_property` |
| SUBSCRIBE topic filters that break the standard's filter rules are refused, one example input each: `a/#/b` (`#` not last), `a+` (`+` not alone in its level), the empty filter, `$share/g/t` with No Local set, and `$share/g` (no filter after the ShareName). The filters `a/+/#` and `$share/g/t` with No Local clear are accepted (every input: `Mqtt.Spec.subscribe_rule`). | `Mqtt.Spec.rejects_bad_topic_filters` |
| A SUBSCRIBE with packet identifier 0 is refused (one example input; every input: `Mqtt.Spec.subscribe_rule`). | `Mqtt.Spec.rejects_subscribe_id_zero` |
| Property values the standard calls a Protocol Error are refused, one example input each: a Subscription Identifier of 0 on a SUBSCRIBE, a Topic Alias of 0 on a PUBLISH, a Receive Maximum of 0, a Maximum Packet Size of 0, a Request Problem Information of 2, a Request Response Information of 2, and Authentication Data with no Authentication Method on a CONNECT, and a Response Topic `#` and an empty Response Topic on a PUBLISH (every input: `Mqtt.Spec.property_rule`). | `Mqtt.Spec.rejects_property_value_rules` |
| The DISCONNECT 224, 1, 0 (a reason code with no property block) reads as that form and prints back as the same three bytes, and the DISCONNECT 224, 2, 0, 0 (a reason code and an empty property block) reads as that form and prints back as the same four bytes. | `Mqtt.Spec.disconnect_short_form` |
| The PINGREQ 192, 1, 0, which carries a one byte body, is refused (one example input; every input: `Mqtt.Spec.empty_body_rule`). | `Mqtt.Spec.rejects_pingreq_body` |
| The packet 32, 0, of type 2, outside the seven in this slice, is refused (one example input; every input: `Mqtt.Spec.header_rule`). | `Mqtt.Spec.rejects_unknown_type` |

A packet is well formed when its numbers fit the widths
that carry them, its strings obey the string rules and fit
the two byte length prefix, its properties match the
property table in type and place, keep the value rules
the standard sets (no Subscription Identifier, Topic
Alias, Receive Maximum or Maximum Packet Size of 0, and
so on, as `SPEC.md` lists), and repeat no single use
property, its packet identifiers stand where the
type requires them and are never 0 there, a PUBLISH at
QoS 0 has DUP clear, a PUBLISH topic name holds no
wildcard and is empty only beside a Topic Alias, its
SUBSCRIBE topic filters keep the filter rules, and its
whole body is shorter than 2^28, the largest remaining
length a variable byte integer can carry. The full list is in
`SPEC.md`. Well formedness is `Mqtt.PacketWF` in
`Mqtt/Value.lean`, which is code under proof: an approval
pins the statements that use it, not its text. So each
rule a claim above depends on is also written in
`Mqtt/Spec/Defs.lean`, part of the specification, and proved
for every input from there (`Mqtt.Spec.header_rule` through
`Mqtt.Spec.empty_body_rule`). The well formedness rules with
no such statement are listed under What is not proved.

The round trip theorems rest on the proofs in
`Mqtt/Proofs/RoundTrip.lean`, where they are
`Mqtt.Proofs.parsePacket_print`, `Mqtt.Proofs.parse_print`,
and `Mqtt.Proofs.decVBI_printVBI`. The soundness theorems
rest on `Mqtt/Proofs/Sound.lean`, where they are
`Mqtt.Proofs.parse_inv` and `Mqtt.Proofs.parsePacket_inv`,
built from one inverse lemma per field reader, and on the
inverse of the strict UTF-8 decoder,
`Mqtt.Utf8.Proofs.decode_inv` in `Mqtt/Proofs/Utf8Inv.lean`.
The rule theorems, and the byte count of a variable byte
integer, rest on `Mqtt/Proofs/Rules.lean`, which derives each
rule in `Mqtt/Spec/Defs.lean` from what the soundness theorems
say the reader accepts.
All of them check against the standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`), which a
reader can confirm with `#print axioms`, or by running
`lake env lean Mqtt/Verify.lean`. The theorems about
single inputs are checked in the kernel with
`decide +kernel`.
Under the round trips, the field and body steps are proved
one by one in the same file: big endian numbers, byte cuts,
string and binary fields, typed property values, single
properties, property lists and whole property blocks, the
subscription options byte, topic filter lists, and the body
of each of the seven packet types. The UTF-8 round trip,
`Mqtt.Utf8.Proofs.decode_encode`, is proved in
`Mqtt/Proofs/Utf8.lean`, and worked examples from the standard
are proved in `Mqtt/Proofs/Examples.lean`.

The command line tool in `Main.lean` calls `Mqtt.parse`
and `Mqtt.print` directly, the same functions the theorems
are about.

## What is not proved

- That well formedness and the printer match the MQTT 5.0
  standard. The proofs show that the reader accepts exactly
  the printings of well formed packets (`Mqtt.Spec.parse_print`
  with `Mqtt.Spec.parse_sound`). That this set is the set of byte
  strings the standard allows for these seven packet types
  is a reading of the standard: `SPEC.md` states it, a
  reviewer checks it against the standard, and the oracle
  differential and the mutation tests in `tests/` probe it,
  with the outcome in the results file. It is not proved.
- Where each field sits in the bytes. The rules in
  `Mqtt/Spec/Defs.lean` are stated on the header byte, on the
  start of a CONNECT body, and on the fields of the packet
  the reader returns. The round trip and soundness theorems
  tie those fields to the bytes through the printer,
  `Mqtt.print`, whose text is code under proof; beyond the
  example inputs, no statement fixes the layout byte by
  byte.
- The well formedness rules that `Mqtt/Spec/Defs.lean` does not
  restate. The reader keeps them on every input
  (`Mqtt.Spec.parse_sound`), but they are written only in
  `Mqtt/Value.lean` and `Mqtt/Parse.lean`, code under proof
  whose text an approval does not pin. They are: the string
  rules (strict UTF-8, no U+0000, at most 65535 bytes) and
  the binary length limit; the subscription options byte
  (bits 6 and 7 clear, QoS and Retain Handling not 3); a
  SUBACK with a packet identifier other than 0 and at least
  one reason code; and the three DISCONNECT body forms. The tests in
  `tests/` check them, and the example theorems in
  `Mqtt/Proofs/Examples.lean` check some on single inputs.
- The shortest writing of a variable byte integer inside a
  property block, for every input. `Mqtt.Spec.decVBI_length`
  states it for the variable byte integer reader, and
  `Mqtt.Spec.parsePacket_frame` with it for the remaining length
  of every packet. For the property length, property
  identifiers and variable byte integer property values, the
  packet reader calls the same reader, but no statement says
  so for every input: `Mqtt.Spec.rejects_non_minimal_property_vbis`
  covers one example input in each place, and the tests in
  `tests/run_tests.py` check the cases named "vbi non-minimal
  ... as property length", "... as property identifier" and
  "... as subscription identifier".
- The bytes of a variable byte integer for values outside the
  standard's worked table. The statements pin how many bytes
  the printer writes (`Mqtt.Spec.printVBI_length`) and that the
  reader reads them back (`Mqtt.Spec.decVBI_printVBI`,
  `Mqtt.Spec.decVBI_canonical`), and `Mqtt.Spec.vbi_worked_table` pins
  the bytes of the table's eight rows; that every other value
  is written seven bits per byte, low groups first, rests on
  the text of `Mqtt.printVBI` and on the tests: the tool
  reads and prints back Paho's writing of 120 random values
  below 2^28 as Subscription Identifiers, and the writings of
  the oracle encoder, written from the standard, in the
  generated packets.
- Any reading of what a property means. A property is an
  identifier and a typed value; that a Receive Maximum of
  10 asks the peer to hold back after ten packets is broker
  and session behaviour, and none of it is in this slice.
- Anything about packets outside the seven types, or
  property identifiers outside the table in `SPEC.md`,
  beyond their refusal (`Mqtt.Spec.header_rule` and
  `Mqtt.Spec.property_rule`).
- Broker or session behaviour of any kind: connections,
  subscriptions as state, retained messages, keep alive
  timing, and what any peer does with a packet.
- Worked examples on the printing side, beyond the two
  DISCONNECT packets of `Mqtt.Spec.disconnect_short_form`. The
  examples in `Mqtt/Proofs/Examples.lean` are stated on the
  reading side. The round trip and soundness theorems
  cover the printer in general.
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
  the standard and `SPEC.md` beside the reader, and Paho's
  Python library in the parts of the differential it
  covers. The oracle shares the reader's reading of the
  standard, though some of its checks are written another
  way (it checks the shortest variable byte integer by
  writing the value again, and topic filters by splitting
  at `/`). Both are evidence, not proof. The results file
  names the versions used, and states plainly which
  oracles were and were not available. In the Paho
  cross-check, Paho judges answers of the Lean tool: its
  encoder's writings of variable byte integers, and
  property blocks of all six kinds, accepted and refused,
  judged by `Properties.unpack`. It does not judge whole
  packets. Paho departs from the standard in places, and
  the run checks those apart as named differences rather
  than take Paho's answer there: its decoder accepts
  variable byte integers longer than the value needs
  (section 1.5.5 forbids them), it refuses a Payload
  Format Indicator above 1 and a Maximum Packet Size above
  268435455 (the standard does not), and it accepts a
  Response Topic with a wildcard or empty, Authentication
  Data without a Method, and a repeated Subscription
  Identifier on SUBSCRIBE (the standard calls each a
  Protocol Error).
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes). The tests drive it, and no
  proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Mqtt/Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   differential against the strict oracle, the Paho
   cross-check when the library is importable, and the
   mutation and rejection cases, and the forbidden classes
   drawn from the seed, with counts and any
   failures written to `tests/TEST-RESULTS.md`. The Paho
   cross-check runs when the interpreter can import
   `paho-mqtt` (for example from a virtual environment),
   and the results file says when it could not. Its inputs
   are counted apart, so the recorded input count is the
   same either way.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Mqtt/Verify.lean`
   prints the axiom list for the round trip and
   soundness theorems.
4. Read `SPEC.md` against the MQTT 5.0 standard and check
   the pinned readings are the ones you want.
