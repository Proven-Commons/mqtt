/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Mqtt.Proofs`
  (`Mqtt/Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use the definitions in `Mqtt/Value.lean`,
  `Mqtt/Parse.lean`, and `Mqtt/Utf8.lean`, the code under proof
  named in `bar.toml`, and the definitions in `Mqtt/Spec/Defs.lean`,
  which are part of the specification: the rules a statement
  holds the reader to are written there, from the standard.
-/

import Mqtt
import Mqtt.Spec.Defs

open Mqtt

/-! ## The round trips

The statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Mqtt/Proofs/RoundTrip.lean`
(printing, then reading) or `Mqtt/Proofs/Sound.lean` (reading, then
printing), over the same well formedness predicate,
`Mqtt.PacketWF`. -/

/-- Parsing the printed form of a well formed packet, with more
    stream bytes after it, gives the packet and those bytes back.
    So a printer that wrote nothing, or wrote something shorter,
    fails this statement. -/
theorem Mqtt.Spec.parsePacket_print (p : Packet) (rest : List UInt8)
    (h : PacketWF p) :
    parsePacket (print p ++ rest) = some (p, rest) := sorry

/-- Parsing the printed form of a well formed packet on its own
    gives the packet back. -/
theorem Mqtt.Spec.parse_print (p : Packet) (h : PacketWF p) :
    parse (print p) = some p := sorry

/-- Every packet the whole input reader accepts is well formed,
    and printing it gives back exactly the bytes it read. With
    `Mqtt.Spec.parse_print`, the reader accepts a byte list exactly
    when it is the printing of a well formed packet, and returns
    that packet. So it refuses every byte list that is not such a
    printing. -/
theorem Mqtt.Spec.parse_sound (bs : List UInt8) (p : Packet)
    (h : parse bs = some p) : PacketWF p ∧ print p = bs := sorry

/-- Every packet the stream reader takes from the front of a byte
    list is well formed, and the bytes it took are exactly its
    printing, with the bytes it returns after them. -/
theorem Mqtt.Spec.parsePacket_sound (bs : List UInt8) (p : Packet)
    (r : List UInt8) (h : parsePacket bs = some (p, r)) :
    PacketWF p ∧ bs = print p ++ r := sorry

/-- Reading a printed variable byte integer gives the number
    back, for every value below 2^28, the most four bytes carry. -/
theorem Mqtt.Spec.decVBI_printVBI (n : Nat) (rest : List UInt8)
    (hn : n < 268435456) :
    decVBI (printVBI n ++ rest) = some (n, rest) := sorry

/-! ## Variable byte integers and the packet frame

Section 1.5.5 of the standard: "The encoded value MUST use the
minimum number of bytes necessary to represent the value". -/

/-- What the variable byte integer reader accepts is the
    printer's writing of the value it returns, followed by the
    bytes it returns; and the value is below 2^28. So every
    value has one writing the reader accepts. That this writing
    is the shortest is `Mqtt.Spec.printVBI_length` and
    `Mqtt.Spec.decVBI_length`. -/
theorem Mqtt.Spec.decVBI_canonical (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) :
    n < 268435456 ∧ bs = printVBI n ++ r := sorry

/-- The printer writes every value below 2^28 in
    `Mqtt.Spec.vbiSize` bytes, the fewest that carry it: one byte
    below 2^7, two below 2^14, three below 2^21, four below
    2^28. -/
theorem Mqtt.Spec.printVBI_length (n : Nat) (hn : n < 268435456) :
    (printVBI n).length = Mqtt.Spec.vbiSize n := sorry

/-- What the variable byte integer reader accepts uses exactly
    `Mqtt.Spec.vbiSize` bytes for the value it returns, the fewest
    that carry it, for every input. So a longer writing, such
    as `[128, 0]` for 0 or `[128, 129, 0]` for 128, is refused
    (section 1.5.5, [MQTT-1.5.5-1]). -/
theorem Mqtt.Spec.decVBI_length (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) :
    bs.length = r.length + Mqtt.Spec.vbiSize n := sorry

/-- Every packet the stream reader takes is a header byte, the
    printer's writing of the body's length (the shortest, by
    `Mqtt.Spec.printVBI_length`), and that many body bytes, all
    standing in the input; the bytes it returns are exactly the
    ones after them. -/
theorem Mqtt.Spec.parsePacket_frame (bs : List UInt8) (p : Packet)
    (r : List UInt8) (h : parsePacket bs = some (p, r)) :
    ∃ (b : UInt8) (body : List UInt8), body.length < 268435456
      ∧ bs = b :: (printVBI body.length ++ body) ++ r := sorry

/-- The remaining length `[128, 0]`, a two byte writing of 0, is
    refused, while its shortest writing `[0]` gives the PINGREQ.
    For every input: `Mqtt.Spec.decVBI_length` with
    `Mqtt.Spec.parsePacket_frame`. -/
theorem Mqtt.Spec.rejects_non_minimal_remaining_length :
    (parse ([192, 128, 0] : List UInt8)).isSome = false
      ∧ parse ([192, 0] : List UInt8) = some .pingreq := sorry

/-- A writing longer than its value needs is refused in each other
    place a variable byte integer stands in a packet, one example
    input each, while the same packet with the shortest writing is
    accepted: the property length 0 of a PUBLISH written `[128, 0]`,
    the property identifier 1 (Payload Format Indicator) written
    `[129, 0]`, and the Subscription Identifier value 1 of a
    SUBSCRIBE written `[129, 128, 0]`. These are single inputs: no
    statement here covers every input in these places. -/
theorem Mqtt.Spec.rejects_non_minimal_property_vbis :
    (parse ([48, 5, 0, 1, 97, 128, 0] : List UInt8)).isSome = false
      ∧ (parse ([48, 4, 0, 1, 97, 0] : List UInt8)).isSome = true
      ∧ (parse ([48, 7, 0, 1, 97, 3, 129, 0, 1] : List UInt8)).isSome = false
      ∧ (parse ([48, 6, 0, 1, 97, 2, 1, 1] : List UInt8)).isSome = true
      ∧ (parse ([130, 11, 0, 1, 3, 11, 129, 128, 0, 0, 1, 97, 0]
          : List UInt8)).isSome = false
      ∧ (parse ([130, 9, 0, 1, 2, 11, 1, 0, 1, 97, 0]
          : List UInt8)).isSome = true := sorry

/-- The standard's worked table of variable byte integers
    (section 1.5.5): the printer writes each boundary value as the
    bytes the table gives, and the reader reads those bytes as that
    value. These are single inputs; for other values the bytes are
    pinned by the byte count (`Mqtt.Spec.printVBI_length`) and the round
    trip (`Mqtt.Spec.decVBI_printVBI`), not by a statement of their
    contents. -/
theorem Mqtt.Spec.vbi_worked_table :
    printVBI 0 = [0] ∧ printVBI 127 = [127]
      ∧ printVBI 128 = [128, 1] ∧ printVBI 16383 = [255, 127]
      ∧ printVBI 16384 = [128, 128, 1]
      ∧ printVBI 2097151 = [255, 255, 127]
      ∧ printVBI 2097152 = [128, 128, 128, 1]
      ∧ printVBI 268435455 = [255, 255, 255, 127]
      ∧ decVBI [0] = some (0, []) ∧ decVBI [127] = some (127, [])
      ∧ decVBI [128, 1] = some (128, [])
      ∧ decVBI [255, 127] = some (16383, [])
      ∧ decVBI [128, 128, 1] = some (16384, [])
      ∧ decVBI [255, 255, 127] = some (2097151, [])
      ∧ decVBI [128, 128, 128, 1] = some (2097152, [])
      ∧ decVBI [255, 255, 255, 127] = some (268435455, []) := sorry

/-! ## The four byte cap

The standard carries a variable byte integer in at most four
bytes (section 1.5.5). These statements hold for every input, so
a reader with a higher cap, or none, fails them: on
`[128, 128, 128, 128, 1]` such a reader returns 2^28. -/

/-- A variable byte integer whose first four bytes all carry a
    continuation mark is refused, whatever follows. -/
theorem Mqtt.Spec.decVBI_four_byte_cap (b0 b1 b2 b3 : UInt8) (rest : List UInt8)
    (h0 : 128 ≤ b0.toNat) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat)
    (h3 : 128 ≤ b3.toNat) :
    decVBI (b0 :: b1 :: b2 :: b3 :: rest) = none := sorry

/-- A packet whose remaining length has a continuation mark on
    each of its first four bytes is refused, by the stream reader
    and by the whole input reader, whatever the header byte and
    whatever follows. -/
theorem Mqtt.Spec.parsePacket_four_byte_cap (h b0 b1 b2 b3 : UInt8)
    (rest : List UInt8)
    (h0 : 128 ≤ b0.toNat) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat)
    (h3 : 128 ≤ b3.toNat) :
    parsePacket (h :: b0 :: b1 :: b2 :: b3 :: rest) = none
      ∧ parse (h :: b0 :: b1 :: b2 :: b3 :: rest) = none := sorry

/-! ## The refusal rules, for every input

Each statement here holds the reader to a rule written in
`Mqtt/Spec/Defs.lean`, part of the specification, for every input.
They are stated for the stream reader `parsePacket`. By
`Mqtt.Spec.parse_whole`, the whole input reader `parse` accepts a
byte list exactly when `parsePacket` takes one packet from it
and leaves nothing, so each holds for `parse` as well. -/

/-- The whole input reader accepts a byte list, and returns a
    packet, exactly when the stream reader takes that packet
    from it and leaves no byte after it. -/
theorem Mqtt.Spec.parse_whole (bs : List UInt8) (p : Packet) :
    parse bs = some p ↔ parsePacket bs = some (p, []) := sorry

/-- Every packet the stream reader takes starts with one of the
    sixteen header bytes of `Mqtt.Spec.headerBytes`. So a SUBSCRIBE
    whose flags are not 0010, any other type with flags other
    than 0000, a PUBLISH with QoS 3 or with DUP set at QoS 0,
    and every packet type outside the seven of this slice are
    refused. -/
theorem Mqtt.Spec.header_rule (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) :
    ∃ (b : UInt8) (tl : List UInt8), bs = b :: tl ∧ b ∈ Mqtt.Spec.headerBytes := sorry

/-- Every CONNECT the stream reader takes is the header byte
    0x10, the length of the body, and a body that starts with
    the protocol name `MQTT` as a string field (the bytes 0, 4,
    77, 81, 84, 84; section 3.1.2.1), the protocol level 5
    (section 3.1.2.2), and a connect flags byte that keeps
    `Mqtt.Spec.ConnectFlagsRule`. When a will stands, its topic is not
    empty and keeps `Mqtt.Spec.TopicNameRule` (sections 3.1.3.3 and
    4.7). -/
theorem Mqtt.Spec.connect_rule (bs r : List UInt8) (c : Connect)
    (h : parsePacket bs = some (.connect c, r)) :
    (∃ (f : UInt8) (tail : List UInt8),
      bs = 16 :: (printVBI (8 + tail.length) ++ ([0, 4, 77, 81, 84, 84, 5, f] ++ tail)) ++ r
      ∧ Mqtt.Spec.ConnectFlagsRule f.toNat)
    ∧ ∀ w, c.will = some w → w.topic ≠ [] ∧ Mqtt.Spec.TopicNameRule w.topic := sorry

/-- Every PUBLISH the stream reader takes has a topic name that
    keeps `Mqtt.Spec.TopicNameRule`, and that is empty only when its
    properties carry a Topic Alias, 0x23 (section 3.3.2.1: "It is
    a Protocol Error if the Topic Name is zero length and there
    is no Topic Alias"). Its packet identifier stands exactly
    when the QoS is not 0 [MQTT-2.2.1-2], and is never 0
    [MQTT-2.2.1-3]. -/
theorem Mqtt.Spec.publish_rule (bs r : List UInt8) (m : Publish)
    (h : parsePacket bs = some (.publish m, r)) :
    Mqtt.Spec.TopicNameRule m.topic ∧ (m.topic = [] → ∃ q ∈ m.props, q.id = 0x23)
    ∧ (m.packetId = none ↔ m.qos = 0) ∧ (∀ i, m.packetId = some i → i ≠ 0) := sorry

/-- Every SUBSCRIBE the stream reader takes has a packet
    identifier other than 0 [MQTT-2.2.1-3], at least one topic
    filter [MQTT-3.8.3-2], and every topic filter, with its
    options, keeps `Mqtt.Spec.FilterRule`. -/
theorem Mqtt.Spec.subscribe_rule (bs r : List UInt8) (i : Nat) (ps : List Property)
    (fs : List (List Char × SubOpts))
    (h : parsePacket bs = some (.subscribe i ps fs, r)) :
    i ≠ 0 ∧ fs ≠ [] ∧ ∀ fo ∈ fs, Mqtt.Spec.FilterRule fo.1 fo.2 := sorry

/-- Every property block of every packet the stream reader
    takes, as `Mqtt.Spec.blocks` lists them, keeps `Mqtt.Spec.BlockRule`:
    each property is allowed on its block, has its identifier's
    value type and keeps the value rules of `Mqtt.Spec.ValueRule`, no
    single use property repeats, and Authentication Data stands
    only with an Authentication Method. -/
theorem Mqtt.Spec.property_rule (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) :
    ∀ b ∈ Mqtt.Spec.blocks p, Mqtt.Spec.BlockRule b.1 b.2 := sorry

/-- Every PINGREQ the stream reader takes is the two bytes 192,
    0, and every PINGRESP the two bytes 208, 0: neither carries
    a body (sections 3.12 and 3.13). -/
theorem Mqtt.Spec.empty_body_rule (bs r : List UInt8) :
    (parsePacket bs = some (.pingreq, r) → bs = [192, 0] ++ r)
    ∧ (parsePacket bs = some (.pingresp, r) → bs = [208, 0] ++ r) := sorry

/-! ## Example inputs

Single inputs the reader refuses or accepts, for the headline
rules of `SPEC.md`; the test harness has a named case for each
rule. Each statement is about its own inputs only, so a reader
of the specification can check each rule against a concrete
case. The rule each one illustrates is stated for every input
in the section above, by the statement its docstring names. -/

/-- A SUBSCRIBE packet with flags 0000 is refused: the value the
    standard fixes for SUBSCRIBE is 0010. For every input:
    `Mqtt.Spec.header_rule`. -/
theorem Mqtt.Spec.rejects_subscribe_flags :
    (parse ([128, 7, 0, 1, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := sorry

/-- A PUBLISH packet with QoS 3, header 0x36, is refused: that
    QoS value is reserved. For every input: `Mqtt.Spec.header_rule`. -/
theorem Mqtt.Spec.rejects_publish_qos3 :
    (parse ([54, 7, 0, 1, 97, 0, 1, 0, 120] : List UInt8)).isSome
      = false := sorry

/-- A PUBLISH with the DUP flag set at QoS 0 is refused (section
    3.3.1.1, [MQTT-3.3.1-2]): the header byte 0x38. The same
    packet with DUP clear, header 0x30, is accepted. For every
    input: `Mqtt.Spec.header_rule`. -/
theorem Mqtt.Spec.rejects_dup_at_qos0 :
    (parse ([56, 4, 0, 1, 97, 0] : List UInt8)).isSome = false
    ∧ parse ([48, 4, 0, 1, 97, 0] : List UInt8)
      = some (.publish ⟨false, 0, false, ['a'], none, [], []⟩) := sorry

/-- A PUBLISH with an empty topic name is accepted when its
    properties carry a Topic Alias, which stands for the topic
    (sections 3.3.2.1 and 3.3.2.3.4): here Topic Alias 1. The same
    packet with no property is refused, since "It is a Protocol
    Error if the Topic Name is zero length and there is no Topic
    Alias" (section 3.3.2.1). For every input:
    `Mqtt.Spec.publish_rule`. -/
theorem Mqtt.Spec.empty_topic_needs_alias :
    parse ([48, 6, 0, 0, 3, 35, 0, 1] : List UInt8)
      = some (.publish ⟨false, 0, false, [], none, [⟨35, .twoByte 1⟩], []⟩)
    ∧ (parse ([48, 3, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A PUBLISH topic name holding a wildcard is refused: `a/#` is
    a filter, not a topic name. For every input:
    `Mqtt.Spec.publish_rule`. -/
theorem Mqtt.Spec.rejects_wildcard_topic :
    (parse ([48, 7, 0, 3, 97, 47, 35, 0, 120] : List UInt8)).isSome
      = false := sorry

/-- A CONNECT whose protocol name is not `MQTT` is refused. For
    every input: `Mqtt.Spec.connect_rule`. -/
theorem Mqtt.Spec.rejects_wrong_protocol_name :
    (parse ([16, 14, 0, 4, 77, 81, 84, 85, 5, 2, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := sorry

/-- A CONNECT with the reserved bit of the connect flags byte
    set is refused. For every input: `Mqtt.Spec.connect_rule`. -/
theorem Mqtt.Spec.rejects_reserved_connect_flag :
    (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 3, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := sorry

/-- A CONNECT whose will flag is clear but whose will QoS or will
    retain bit is set is refused (sections 3.1.2.6
    [MQTT-3.1.2-11] and 3.1.2.7 [MQTT-3.1.2-13]): here the
    connect flags 0x0A (will QoS 1) and 0x22 (will retain). With
    the flags 0x02 the same bytes are the CONNECT of
    `Mqtt.Examples.parse_connect`. For every input:
    `Mqtt.Spec.connect_rule`. -/
theorem Mqtt.Spec.rejects_will_bits_without_will :
    (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 10, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false
    ∧ (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 34, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := sorry

/-- A CONNECT carrying a Subscription Identifier, a property its
    block does not allow, is refused. For every input:
    `Mqtt.Spec.property_rule`. -/
theorem Mqtt.Spec.rejects_property_wrong_type :
    (parse ([16, 16, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 2, 11, 5, 0,
      1, 120] : List UInt8)).isSome = false := sorry

/-- A PUBLISH carrying the single use Topic Alias twice in one
    block is refused. For every input: `Mqtt.Spec.property_rule`. -/
theorem Mqtt.Spec.rejects_repeated_property :
    (parse ([50, 12, 0, 1, 97, 0, 3, 6, 35, 0, 1, 35, 0, 2]
      : List UInt8)).isSome = false := sorry

/-- SUBSCRIBE topic filters that break the filter rules are
    refused, one example input each (sections 4.7.1, 4.7.3,
    4.8.2 and 3.8.3.1): `#` before the last level, `+` sharing
    its level, an empty filter, a shared subscription with No
    Local set, and `$share/` with no filter after the ShareName.
    Two filters that keep the rules are accepted: `a/+/#`, and
    `$share/g/t` with No Local clear. For every input:
    `Mqtt.Spec.subscribe_rule`. -/
theorem Mqtt.Spec.rejects_bad_topic_filters :
    -- `a/#/b`: `#` not in the last level
    (parse ([130, 11, 0, 1, 0, 0, 5, 97, 47, 35, 47, 98, 0]
      : List UInt8)).isSome = false
    -- `a+`: `+` not alone in its level
    ∧ (parse ([130, 8, 0, 1, 0, 0, 2, 97, 43, 0] : List UInt8)).isSome = false
    -- the empty filter
    ∧ (parse ([130, 6, 0, 1, 0, 0, 0, 0] : List UInt8)).isSome = false
    -- `$share/g/t` with No Local set
    ∧ (parse ([130, 16, 0, 1, 0, 0, 10, 36, 115, 104, 97, 114, 101, 47, 103,
        47, 116, 4] : List UInt8)).isSome = false
    -- `$share/g`: no `/` and filter after the ShareName
    ∧ (parse ([130, 14, 0, 1, 0, 0, 8, 36, 115, 104, 97, 114, 101, 47, 103, 0]
        : List UInt8)).isSome = false
    -- `a/+/#` is accepted
    ∧ parse ([130, 11, 0, 1, 0, 0, 5, 97, 47, 43, 47, 35, 0] : List UInt8)
      = some (.subscribe 1 [] [(['a', '/', '+', '/', '#'], ⟨0, false, false, 0⟩)])
    -- `$share/g/t` with No Local clear is accepted
    ∧ parse ([130, 16, 0, 1, 0, 0, 10, 36, 115, 104, 97, 114, 101, 47, 103, 47,
        116, 0] : List UInt8)
      = some (.subscribe 1 []
          [(['$', 's', 'h', 'a', 'r', 'e', '/', 'g', '/', 't'],
            ⟨0, false, false, 0⟩)]) := sorry

/-- A SUBSCRIBE with packet identifier 0 is refused:
    identifiers are never 0. For every input:
    `Mqtt.Spec.subscribe_rule`. -/
theorem Mqtt.Spec.rejects_subscribe_id_zero :
    (parse ([130, 7, 0, 0, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := sorry

/-- Property values the standard calls a Protocol Error are
    refused, one input each: a Subscription Identifier of 0, a
    Topic Alias of 0, a Receive Maximum of 0, a Maximum Packet
    Size of 0, a Request Problem Information or Request Response
    Information of 2, Authentication Data with no Authentication
    Method, and a Response Topic that holds a wildcard or is
    empty. Changing the offending value byte (to 1, or to `b`
    for the Response Topic) gives an input the reader accepts.
    For every input: `Mqtt.Spec.property_rule`. -/
theorem Mqtt.Spec.rejects_property_value_rules :
    -- Subscription Identifier 0, on a SUBSCRIBE
    (parse ([130, 9, 0, 1, 2, 11, 0, 0, 1, 97, 0] : List UInt8)).isSome = false
    -- Topic Alias 0, on a PUBLISH
    ∧ (parse ([48, 7, 0, 1, 97, 3, 35, 0, 0] : List UInt8)).isSome = false
    -- Receive Maximum 0, on a CONNECT
    ∧ (parse ([16, 17, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 3, 33, 0, 0, 0, 1,
        120] : List UInt8)).isSome = false
    -- Maximum Packet Size 0, on a CONNECT
    ∧ (parse ([16, 19, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 5, 39, 0, 0, 0, 0, 0,
        1, 120] : List UInt8)).isSome = false
    -- Request Problem Information 2, on a CONNECT
    ∧ (parse ([16, 16, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 2, 23, 2, 0, 1, 120]
        : List UInt8)).isSome = false
    -- Request Response Information 2, on a CONNECT
    ∧ (parse ([16, 16, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 2, 25, 2, 0, 1, 120]
        : List UInt8)).isSome = false
    -- Authentication Data with no Authentication Method, on a CONNECT
    ∧ (parse ([16, 17, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 3, 22, 0, 0, 0, 1,
        120] : List UInt8)).isSome = false
    -- Response Topic `#`, on a PUBLISH
    ∧ (parse ([48, 8, 0, 1, 97, 4, 8, 0, 1, 35] : List UInt8)).isSome = false
    -- an empty Response Topic, on a PUBLISH
    ∧ (parse ([48, 7, 0, 1, 97, 3, 8, 0, 0] : List UInt8)).isSome = false := sorry

/-- The two DISCONNECT forms with a reason code are kept apart
    (section 3.14.2.2.1: with a remaining length below 2 there is
    no property length): the one byte body `[0]` reads as the
    reason code alone and prints back as the same three bytes,
    and the body `[0, 0]` reads as the reason code with an empty
    property block and prints back as the same four bytes. -/
theorem Mqtt.Spec.disconnect_short_form :
    parse ([224, 1, 0] : List UInt8) = some (.disconnect (some (0, none)))
    ∧ print (.disconnect (some (0, none))) = [224, 1, 0]
    ∧ parse ([224, 2, 0, 0] : List UInt8)
      = some (.disconnect (some (0, some [])))
    ∧ print (.disconnect (some (0, some []))) = [224, 2, 0, 0] := sorry

/-- A PINGREQ with a body is refused: its remaining length must
    be 0. For every input: `Mqtt.Spec.empty_body_rule`. -/
theorem Mqtt.Spec.rejects_pingreq_body :
    (parse ([192, 1, 0] : List UInt8)).isSome = false := sorry

/-- The packet `[32, 0]`, of type 2, outside the seven in this
    slice, is refused. For every input: `Mqtt.Spec.header_rule`. -/
theorem Mqtt.Spec.rejects_unknown_type :
    (parse ([32, 0] : List UInt8)).isSome = false := sorry
