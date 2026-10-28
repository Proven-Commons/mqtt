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

Pinned reading, non-minimal encodings: a value may be written
with more bytes than it needs, as long as the writing uses at
most four bytes and the value fits. The reader accepts such
encodings. So 0 written as 128, 0 reads as 0. This matches the
behaviour of common libraries, including Paho. The printer
always writes the minimal form, so a packet that arrived with
a non-minimal remaining length is reprinted with the minimal
one. The same rule applies to every variable byte integer in
a packet, including property lengths and variable byte
integer property values.

## Fixed header flags

For every type in this slice except PUBLISH, the flags nibble
must be exactly the value the standard fixes (section 2.1.2):
0010 for SUBSCRIBE, and 0000 for CONNECT, SUBACK, PINGREQ,
PINGRESP, and DISCONNECT. Any other nibble is rejected.

PUBLISH flags carry meaning and are part of the packet value:
the DUP flag at bit 3, the QoS level at bits 2 and 1, and the
RETAIN flag at bit 0. The QoS value 3 is reserved and is
rejected.

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

Three property checks reject a packet:

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
flag is set; when it is clear, the printer writes them as 0.

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

The topic name must be nonempty and must contain neither
wildcard character, `+` or `#` (section 4.7.1). A packet
identifier, where one stands, must not be 0.

### SUBSCRIBE (section 3.8)

The body is: the packet identifier as two bytes, which must
not be 0; the SUBSCRIBE property block; then a list of topic
filters that fills the rest of the body exactly. The list
must be nonempty. Each filter is a filter string as a string
field, then one subscription options byte. A filter string
follows the string rules above; wildcards are allowed in it,
as the standard allows. The reader adds no nonemptiness check
of its own to a single filter string.

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
  property block. The standard omits the property length when
  the remaining length is 1 (section 3.14.2), so this form is
  accepted, and reads as that reason code with an empty
  property block.
- A remaining length of 2 or more: one reason code byte, then
  a DISCONNECT property block that fills the rest of the body
  exactly.

The printer always writes the second kind of packet with an
explicit property block, so a packet read from the one byte
form is reprinted in the longer form: the packet with reason
code 0 and no properties prints as remaining length 2, reason
0, property length 0. Reason code values are not checked
beyond being bytes.

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

## Well formed values

The round trip claim holds for well formed packets: the
fields the printer can write exactly. In outline:

- Every number fits the width that carries it: keep alive and
  packet identifiers and two byte property values below
  65536, four byte property values below 2^32, variable byte
  integer values and any single property block's printed
  length below 2^28, and the whole body below 2^28, the
  largest remaining length four bytes can carry.
- Strings obey the string rules and their UTF-8 byte length
  fits the two byte length prefix; binary data fields fit the
  same prefix.
- Properties match the table in type and in place, and no
  single use property repeats in one block.
- CONNECT: the will, when one stands, has QoS at most 2, a
  well formed will property block, a topic that passes the
  topic name check, and a payload that fits its prefix.
- PUBLISH: QoS at most 2; a topic that passes the topic name
  check; a packet identifier standing exactly when the QoS is
  1 or 2, and never 0.
- SUBSCRIBE: a nonzero packet identifier, a nonempty filter
  list, and options with QoS and retain handling at most 2.
- SUBACK: a nonzero packet identifier and a nonempty reason
  list of byte values.
- DISCONNECT with a body: a reason code below 256 and a well
  formed property block.

## The printer

The printer writes a packet as the fixed header byte, the
remaining length as a minimal variable byte integer, and the
body in the layouts above. Property blocks are written with a
minimal property length. A packet read by the reader and
printed again is in this canonical form; a packet that
arrived already in canonical form reprints byte for byte.

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
`ok:224,2,0,0`: the same packet reprinted with its explicit
property block.

The tool prints only the re-encoded bytes. It does not print
a rendering of the packet, so test harnesses check the parsed
structure through the re-encoding together with their own
oracle.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The four byte cap
theorems hold for every input. The other refusal theorems are
single inputs, one for each named rejection case in the test
harness; the tests in `tests/` cover each rule on many more
inputs.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed packet, with more stream bytes after it, gives the packet and those bytes back | `Spec.parsePacket_print` |
| Parsing the printed form of a well formed packet on its own gives the packet back | `Spec.parse_print` |
| Reading a printed variable byte integer gives the number back, below 2^28 | `Spec.decVBI_printVBI` |
| A variable byte integer whose first four bytes all carry a continuation mark is refused, whatever follows | `Spec.decVBI_four_byte_cap` |
| A packet whose remaining length has a continuation mark on each of its first four bytes is refused, whatever the header byte and whatever follows | `Spec.parsePacket_four_byte_cap` |
| A SUBSCRIBE with flags other than 0010 is refused | `Spec.rejects_subscribe_flags` |
| A PUBLISH with the reserved QoS value 3 is refused | `Spec.rejects_publish_qos3` |
| A PUBLISH topic name holding a wildcard is refused | `Spec.rejects_wildcard_topic` |
| A CONNECT with a protocol name other than `MQTT` is refused | `Spec.rejects_wrong_protocol_name` |
| A CONNECT with the reserved connect flag bit set is refused | `Spec.rejects_reserved_connect_flag` |
| A property on a packet type that does not allow it is refused | `Spec.rejects_property_wrong_type` |
| A single use property standing twice in one block is refused | `Spec.rejects_repeated_property` |
| A SUBSCRIBE with packet identifier 0 is refused | `Spec.rejects_subscribe_id_zero` |
| A PINGREQ with a body is refused | `Spec.rejects_pingreq_body` |
| A packet type outside the seven in this slice is refused | `Spec.rejects_unknown_type` |
