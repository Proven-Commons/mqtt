# MQTT packet codec: specification

This is the specification of the first slice for the `mqtt`
package: MQTT 5.0 control packet framing at the level of bytes,
in Lean, with the round trip proved. The format itself is
defined by the OASIS MQTT Version 5.0 standard; section numbers
below are that standard's. This file states what the slice does
with it, including the points where the standard leaves a
reading open and this slice pins one.

What the slice is: a reader and a printer for one control
packet of seven types, and a reader that can walk a stream of
packets one at a time. What it is not: a broker, a client, or
any session behaviour. Nothing here opens a connection, keeps
state between packets, acts on a packet's meaning, or checks a
packet against a subscription or a session.

## The packet on the wire

A packet is three parts, in order:

1. One fixed header byte: the packet type in the high four
   bits, and type specific flags in the low four bits.
2. The remaining length: a variable byte integer (below) that
   counts the bytes of the third part.
3. The body: the variable header and the payload for the type,
   exactly as many bytes as the remaining length says.

The packet types in this slice are CONNECT (1), PUBLISH (3),
SUBSCRIBE (8), SUBACK (9), PINGREQ (12), PINGRESP (13), and
DISCONNECT (14). A fixed header byte whose type nibble is any
other value is rejected in this slice.

## The variable byte integer

A variable byte integer (section 2.1.4) carries seven bits per
byte, low groups first. The top bit of a byte is a continuation
mark: it is set on every byte but the last. At most four bytes
are used, so the largest value is 268435455 (2^28 - 1). The
standard's worked table:

| Value | Bytes |
| --- | --- |
| 0 | 0 |
| 127 | 127 |
| 128 | 128, 1 |
| 16383 | 255, 127 |
| 16384 | 128, 128, 1 |
| 2097151 | 255, 255, 127 |
| 2097152 | 128, 128, 128, 1 |
| 268435455 | 255, 255, 255, 127 |

The reader rejects a value whose fourth byte still carries a
continuation mark (a fifth byte would be needed), whatever
follows, and rejects a value cut off by the end of the input.
The first rule is proved for every input, for the variable
byte integer reader and for the remaining length of a packet.

Shortest writing (section 1.5.5): "The encoded value MUST use
the minimum number of bytes necessary to represent the value
[MQTT-1.5.5-1]". The reader rejects a writing that uses more
bytes than its value needs, which is one whose last byte is 0
after a continuation byte. So 0 written as 128, 0 is rejected,
and so is 128 written as 128, 129, 0. The same rule applies to
every variable byte integer in a packet: the remaining length,
property lengths, property identifiers, and variable byte
integer property values. It is proved for every input: what
the reader accepts is exactly the printer's writing of the
value it returns, and the packet reader takes exactly a header
byte, the shortest writing of the body length, and the body.

Paho's Python library (paho-mqtt 2.1.0) accepts the longer
writings, for example 128, 0 as 0. The test harness records
this as a named difference from that library.

## Fixed header flags

For every type in this slice except PUBLISH, the flags nibble
must be exactly the value the standard fixes (section 2.1.2):
0010 for SUBSCRIBE, and 0000 for CONNECT, SUBACK, PINGREQ,
PINGRESP, and DISCONNECT. Any other nibble is rejected.

PUBLISH flags carry meaning and are part of the packet value:
the DUP flag at bit 3, the QoS level at bits 2 and 1, and the
RETAIN flag at bit 0. The QoS value 3 is reserved and is
rejected. The DUP flag set at QoS 0 is rejected: "The DUP flag
MUST be set to 0 for all QoS 0 messages [MQTT-3.3.1-2]"
(section 3.3.1.1).

## Strings and binary data

A UTF-8 string field (section 1.5.4) is a two byte length,
counting bytes, then that many bytes of UTF-8 text. The reader
decodes the bytes with a strict UTF-8 decoder: it rejects
stray continuation bytes, overlong forms, lead bytes above
F4, encodings of the surrogate values D800 to DFFF, values
above 10FFFF, and truncated sequences. It also rejects the
null character U+0000, which the standard forbids in strings.
Nothing else about the text is checked.

A binary data field (section 1.5.3) is a two byte length, then
that many bytes, with no check on the bytes.

## Properties

Most packet types carry a property block (section 2.2.2): a
property length as a variable byte integer, then that many
bytes of properties. Each property is an identifier, written
as a variable byte integer, and a value whose shape is fixed
by the identifier's row in the standard's property table
(Table 2-4). The block must be filled exactly: a property that
runs past the end of the block, and bytes left over inside the
block after the last whole property, are both rejected.

The table as implemented in this slice:

| Id | Name | Value type | Blocks it may stand on |
| --- | --- | --- | --- |
| 0x01 | Payload Format Indicator | byte | will, PUBLISH |
| 0x02 | Message Expiry Interval | four byte integer | will, PUBLISH |
| 0x03 | Content Type | UTF-8 string | will, PUBLISH |
| 0x08 | Response Topic | UTF-8 string | will, PUBLISH |
| 0x09 | Correlation Data | binary data | will, PUBLISH |
| 0x0B | Subscription Identifier | variable byte integer | PUBLISH, SUBSCRIBE |
| 0x11 | Session Expiry Interval | four byte integer | CONNECT, DISCONNECT |
| 0x12 | Assigned Client Identifier | UTF-8 string | none in this slice |
| 0x13 | Server Keep Alive | two byte integer | none in this slice |
| 0x15 | Authentication Method | UTF-8 string | CONNECT |
| 0x16 | Authentication Data | binary data | CONNECT |
| 0x17 | Request Problem Information | byte | CONNECT |
| 0x18 | Will Delay Interval | four byte integer | will |
| 0x19 | Request Response Information | byte | CONNECT |
| 0x1A | Response Information | UTF-8 string | none in this slice |
| 0x1C | Server Reference | UTF-8 string | DISCONNECT |
| 0x1F | Reason String | UTF-8 string | SUBACK, DISCONNECT |
| 0x21 | Receive Maximum | two byte integer | CONNECT |
| 0x22 | Topic Alias Maximum | two byte integer | CONNECT |
| 0x23 | Topic Alias | two byte integer | PUBLISH |
| 0x24 | Maximum QoS | byte | none in this slice |
| 0x25 | Retain Available | byte | none in this slice |
| 0x26 | User Property | UTF-8 string pair | CONNECT, will, PUBLISH, SUBSCRIBE, SUBACK, DISCONNECT |
| 0x27 | Maximum Packet Size | four byte integer | CONNECT |
| 0x28 | Wildcard Subscription Available | byte | none in this slice |
| 0x29 | Subscription Identifier Available | byte | none in this slice |
| 0x2A | Shared Subscription Available | byte | none in this slice |

Rows marked "none in this slice" name properties the standard
assigns to packet types this slice does not read (chiefly
CONNACK). The identifier has a known value type, but it is on
no allowed list here, so the reader rejects it everywhere in
this slice.

These property checks reject a packet:

- An identifier with no row in the table is rejected.
- A property standing on a block whose allowed list does not
  include it is rejected. For example, a Subscription
  Identifier on a CONNECT packet is rejected.
- A repeated single use property is rejected. Two properties
  may repeat: the User Property (0x26) may repeat on any block
  that allows it, and the Subscription Identifier (0x0B) may
  repeat on PUBLISH, where one message can match several
  subscriptions (section 3.3.4). Every other allowed property
  may stand at most once in one block.
- A value the standard calls a Protocol Error is rejected
  (`propValOK` in `Mqtt/Value.lean`):
  - a Response Topic (0x08) that is empty or holds `+` or `#`:
    it is used as a Topic Name (sections 3.3.2.3.5
    [MQTT-3.3.2-14], 4.7.0 [MQTT-4.7.0-1], 4.7.3
    [MQTT-4.7.3-1]), on PUBLISH and in the will alike;
  - a Subscription Identifier (0x0B) of 0 (sections 3.3.2.3.8
    and 3.8.2.1.2);
  - a Request Problem Information (0x17) or Request Response
    Information (0x19) other than 0 or 1 (sections 3.1.2.11.7
    and 3.1.2.11.6);
  - a Receive Maximum (0x21) of 0 (section 3.1.2.11.3);
  - a Topic Alias (0x23) of 0 (section 3.3.2.3.4,
    [MQTT-3.3.2-8]);
  - a Maximum Packet Size (0x27) of 0 (section 3.1.2.11.4).
- Authentication Data (0x16) in a block with no Authentication
  Method (0x15) is rejected (section 3.1.2.11.10; `authOK`).

Other values of the right type are accepted. In particular a
Payload Format Indicator (0x01) other than 0 or 1 is accepted:
section 3.3.2.3.2 names the two values but, unlike the rules
above, does not call another value a Protocol Error. Rules
that depend on the session, such as a Topic Alias above the
peer's Topic Alias Maximum, are outside this slice.

## The seven packet types

### CONNECT (section 3.1)

The body is: the protocol name as a string field, which must
be exactly the text "MQTT"; one protocol level byte, which
must be 5; one connect flags byte; the keep alive as two
bytes; the CONNECT property block; then the payload.

The connect flags byte is: username flag at bit 7, password
flag at bit 6, will retain at bit 5, will QoS at bits 4 and 3,
will flag at bit 2, clean start at bit 1, and a reserved bit
at bit 0. The reader rejects a packet whose reserved bit is
set, and rejects a will QoS field of 3. The will QoS and will
retain bits are part of the packet value only when the will
flag is set. When it is clear, both must be 0 (sections
3.1.2.6 [MQTT-3.1.2-11] and 3.1.2.7 [MQTT-3.1.2-13]): the
reader rejects a packet with the will flag clear and any of
bits 3, 4 or 5 set, and the printer writes them as 0.

The payload is: the client identifier as a string field
(always present, and it may be empty); then, when the will
flag is set, the will property block, the will topic as a
string field, and the will payload as a binary data field;
then the username as a string field when the username flag is
set; then the password as a binary data field when the
password flag is set. The fields stand exactly when the flags
say they stand, and the body must be consumed exactly: bytes
left over, or a field the flags demand but the bytes do not
hold, are rejected. The will topic must pass the topic name
check below, like a PUBLISH topic.

### PUBLISH (section 3.3)

The body is: the topic name as a string field; the packet
identifier as two bytes, present exactly when the QoS is 1 or
2 and never present at QoS 0; the PUBLISH property block;
then the payload, which is all the bytes that remain in the
body, and may be empty.

The topic name must contain neither wildcard character, `+`
or `#` (section 3.3.2.1, [MQTT-3.3.2-2]). It may be empty only
when the PUBLISH property block carries a Topic Alias (0x23):
"It is a Protocol Error if the Topic Name is zero length and
there is no Topic Alias" (section 3.3.2.1). The topic the
alias stands for is session state, which this slice does not
keep, so an empty topic with an alias is accepted whatever the
alias value (other than 0, which the value rules above
reject). A packet identifier, where one stands, must not be
0.

### SUBSCRIBE (section 3.8)

The body is: the packet identifier as two bytes, which must
not be 0; the SUBSCRIBE property block; then a list of topic
filters that fills the rest of the body exactly. The list
must be nonempty. Each filter is a filter string as a string
field, then one subscription options byte. A filter string
follows the string rules above, and the filter rules of the
standard (`filterOK` in `Mqtt/Value.lean`):

- It is at least one character long [MQTT-4.7.3-1].
- Split at each `/` into levels, a `+` must be a whole level
  [MQTT-4.7.1-2], and a `#` must be a whole level and the last
  one [MQTT-4.7.1-1]. So `a/+/#`, `#`, `+` and `/` are filters,
  and `a/#/b`, `a#` and `a+` are not.
- A filter that starts with `$share/` is a shared subscription
  (section 4.8.2): after `$share/` comes a ShareName at least
  one character long with no `+` or `#` [MQTT-4.8.2-1], then a
  `/` and a filter that keeps the two rules above
  [MQTT-4.8.2-2]. Its No Local option must be clear
  [MQTT-3.8.3-4]. A filter that starts `$share` with no `/`
  after it is an ordinary filter.

A filter that breaks a rule is rejected, and so is the whole
packet.

The subscription options byte is: the maximum QoS at bits 0
and 1, the no local flag at bit 2, the retain as published
flag at bit 3, and the retain handling choice at bits 4 and
5. The reader rejects a byte of 64 or more (the reserved bits
6 and 7 must be clear), a QoS field of 3, and a retain
handling field of 3.

### SUBACK (section 3.9)

The body is: the packet identifier as two bytes, which must
not be 0; the SUBACK property block; then the list of reason
codes, one byte each, filling the rest of the body. The list
must be nonempty. Reason code values are not checked beyond
being bytes.

### PINGREQ (section 3.12) and PINGRESP (section 3.13)

Both packets have an empty body: the remaining length must be
0, and any body byte is rejected.

### DISCONNECT (section 3.14)

Three body forms are legal:

- A remaining length of 0: a normal disconnection with no
  body.
- A remaining length of 1: one reason code byte and no
  property block. "If the Remaining Length is less than 2, a
  value of 0 is used" for the property length (section
  3.14.2.2.1), so this form is accepted.
- A remaining length of 2 or more: one reason code byte, then
  a DISCONNECT property block that fills the rest of the body
  exactly.

The packet value keeps which form arrived: no body, a reason
code alone, or a reason code and a property block. The
printer writes each form back as it came, so the one byte
form with reason code 0 prints as remaining length 1, reason
0, and the form with an empty property block prints as
remaining length 2, reason 0, property length 0. Reason code
values are not checked beyond being bytes.

## The reader

The reader reads one packet from the front of a byte list and
returns the packet together with the rest of the input, so a
caller can walk a stream of packets: trailing bytes are not
an error at that level. The whole input form of the reader
adds the check that nothing follows the packet.

Safety: the reader never reads past the end of its input. It
first cuts the body out by the remaining length, and each
field reader checks its length against the bytes that
actually remain before taking any of them. Any shortfall, at
any point, is a rejection, not a partial read. Each type's
reader must consume its body cut exactly.

Soundness, proved for every input: what the reader accepts is
exactly the printed form of a well formed packet. The whole
input reader accepts a byte list only when it is the printing
of a well formed packet, and returns that packet; the stream
reader takes from the front of its input exactly the printing
of the well formed packet it returns, and returns the rest
untouched. With the round trip, the reader and the printer
are inverse to each other: the byte lists the reader accepts
are exactly the printings of well formed packets. So every
rule of well formedness below, and every fixed byte the
printer writes, is a rule the reader enforces on every
input.

## Well formed values

The round trip claim holds for well formed packets: the
fields the printer can write exactly. Every packet the reader
accepts is well formed. In outline:

- Every number fits the width that carries it: keep alive and
  packet identifiers and two byte property values below
  65536, four byte property values below 2^32, variable byte
  integer values and any single property block's printed
  length below 2^28, and the whole body below 2^28, the
  largest remaining length four bytes can carry.
- Strings obey the string rules and their UTF-8 byte length
  fits the two byte length prefix; binary data fields fit the
  same prefix.
- Properties match the table in type and in place, keep the
  value rules above, and no single use property repeats in one
  block; Authentication Data stands only with an
  Authentication Method.
- CONNECT: the will, when one stands, has QoS at most 2, a
  well formed will property block, a topic that passes the
  topic name check, and a payload that fits its prefix.
- PUBLISH: QoS at most 2; DUP clear at QoS 0; a topic with no
  wildcard, empty only when a Topic Alias stands in the
  properties; a packet identifier standing exactly when the
  QoS is 1 or 2, and never 0.
- SUBSCRIBE: a nonzero packet identifier, a nonempty filter
  list, options with QoS and retain handling at most 2, and
  each filter keeping the filter rules above.
- SUBACK: a nonzero packet identifier and a nonempty reason
  list of byte values.
- DISCONNECT with a body: a reason code below 256, and a well
  formed property block when one stands.

## The printer

The printer writes a packet as the fixed header byte, the
remaining length as a minimal variable byte integer, and the
body in the layouts above. Property blocks are written with a
minimal property length, and property identifiers and
variable byte integer values in their minimal form, which is
the only form the reader accepts. Every packet the reader
accepts reprints byte for byte: the printer's form is the
only form the reader accepts.

## The line protocol

The command line tool reads one request per line: the
operation and a payload, parted by one space. The payload is
decimal byte numbers parted by commas, with no spaces. A
number is plain decimal: no sign, no leading zeros (the
number 0 itself is written `0`), at most twenty digits. An
empty line gets no answer. A request that breaks these rules
prints `error`, as does an unknown operation.

The one operation is `parse`. It parses the bytes as exactly
one whole packet and prints `ok:` followed by the bytes of
the canonical reprint, comma parted, when the bytes are one
packet this slice reads. It prints `none` when the bytes are
well formed as a request but are not one packet this slice
reads. The empty payload is the empty byte list and answers
`none`.

Example: the request `parse 192,0` is a PINGREQ. The answer
is `ok:192,0`. The request `parse 224,1,0` is the one byte
body form of DISCONNECT with reason code 0. The answer is
`ok:224,1,0`: the same packet, reprinted in the form it came
in.

The tool prints only the re-encoded bytes. It does not print
a rendering of the packet, so test harnesses check the parsed
structure through the re-encoding together with their own
oracle.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean` and
proved in `Proofs/SpecProofs.lean`. The round trip, soundness,
variable byte integer, frame and four byte cap theorems hold
for every input. A row marked "one example input", or one that
names its inputs, is a theorem about those inputs alone; the
test harness has a named case for each such rule. The rule it
illustrates holds for every input through `Spec.parse_sound`:
an accepted input is the printing of a well formed packet, and
no well formed packet prints in the refused way, as the
sections above describe. The tests in `tests/` also check each
rule on many more inputs.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed packet, with more stream bytes after it, gives the packet and those bytes back | `Spec.parsePacket_print` |
| Parsing the printed form of a well formed packet on its own gives the packet back | `Spec.parse_print` |
| Every packet the whole input reader accepts is well formed, and printing it gives back exactly the bytes it read; so the reader refuses every byte list that is not the printing of a well formed packet | `Spec.parse_sound` |
| Every packet the stream reader takes is well formed, and the bytes it took are exactly its printing, followed by the bytes it returns | `Spec.parsePacket_sound` |
| Reading a printed variable byte integer gives the number back, below 2^28 | `Spec.decVBI_printVBI` |
| What the variable byte integer reader accepts is the printer's writing of the value it returns, the shortest one, so a longer writing is refused; the value is below 2^28 | `Spec.decVBI_canonical` |
| Every packet the stream reader takes is a header byte, the shortest writing of the body length, and that many body bytes, all in the input; the bytes it returns are the ones after them | `Spec.parsePacket_frame` |
| The remaining length 128, 0 (a two byte writing of 0) is refused, while 0 gives the PINGREQ | `Spec.rejects_non_minimal_remaining_length` |
| A variable byte integer whose first four bytes all carry a continuation mark is refused, whatever follows | `Spec.decVBI_four_byte_cap` |
| A packet whose remaining length has a continuation mark on each of its first four bytes is refused, whatever the header byte and whatever follows | `Spec.parsePacket_four_byte_cap` |
| A SUBSCRIBE with flags 0000 rather than 0010 is refused (one example input) | `Spec.rejects_subscribe_flags` |
| A PUBLISH with the reserved QoS value 3 is refused (one example input) | `Spec.rejects_publish_qos3` |
| A PUBLISH with DUP set at QoS 0 is refused (one example input, header 0x38), while the same packet with header 0x30 is accepted | `Spec.rejects_dup_at_qos0` |
| An empty PUBLISH topic name is accepted with a Topic Alias and refused without one (one example input each) | `Spec.empty_topic_needs_alias` |
| A PUBLISH whose topic name is `a/#` is refused (one example input) | `Spec.rejects_wildcard_topic` |
| A CONNECT whose protocol name is `MQTU` is refused (one example input) | `Spec.rejects_wrong_protocol_name` |
| A CONNECT with connect flags 0x03, the reserved bit set, is refused (one example input) | `Spec.rejects_reserved_connect_flag` |
| A CONNECT with the will flag clear and the will QoS or will retain bit set is refused (example inputs: connect flags 0x0A and 0x22) | `Spec.rejects_will_bits_without_will` |
| A CONNECT carrying a Subscription Identifier, which its block does not allow, is refused (one example input) | `Spec.rejects_property_wrong_type` |
| A PUBLISH carrying the Topic Alias twice is refused (one example input) | `Spec.rejects_repeated_property` |
| SUBSCRIBE topic filters that break the filter rules are refused, one example input each: `a/#/b`, `a+`, the empty filter, `$share/g/t` with No Local, and `$share/g`; `a/+/#` and `$share/g/t` without No Local are accepted | `Spec.rejects_bad_topic_filters` |
| A SUBSCRIBE with packet identifier 0 is refused (one example input) | `Spec.rejects_subscribe_id_zero` |
| Property values the standard calls a Protocol Error are refused, one example input each: a Subscription Identifier, Topic Alias, Receive Maximum or Maximum Packet Size of 0, a Request Problem Information or Request Response Information of 2, Authentication Data without an Authentication Method, and a Response Topic that holds a wildcard or is empty | `Spec.rejects_property_value_rules` |
| A DISCONNECT with a one byte body reads as a reason code with no property block and prints back as the same bytes; one with a reason code and an empty property block does the same in its own form (one example of each) | `Spec.disconnect_short_form` |
| A PINGREQ with a one byte body is refused (one example input) | `Spec.rejects_pingreq_body` |
| The packet 32, 0, of type 2, is refused (one example input) | `Spec.rejects_unknown_type` |
