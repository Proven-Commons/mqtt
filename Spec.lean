/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `Mqtt/Value.lean`,
  `Mqtt/Parse.lean`, and `Mqtt/Utf8.lean`, the code under proof
  named in `bar.toml`. No definition of their own is needed, so
  this project has no `Spec/Defs.lean`.
-/

import Mqtt

open Mqtt

/-! ## The round trips

The statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Proofs/RoundTrip.lean`,
over the same well formedness predicate, `Mqtt.PacketWF`. -/

/-- Parsing the printed form of a well formed packet, with more
    stream bytes after it, gives the packet and those bytes back.
    So a printer that wrote nothing, or wrote something shorter,
    fails this statement. -/
theorem Spec.parsePacket_print (p : Packet) (rest : List UInt8)
    (h : PacketWF p) :
    parsePacket (print p ++ rest) = some (p, rest) := sorry

/-- Parsing the printed form of a well formed packet on its own
    gives the packet back. -/
theorem Spec.parse_print (p : Packet) (h : PacketWF p) :
    parse (print p) = some p := sorry

/-- Reading a printed variable byte integer gives the number
    back, for every value below 2^28, the most four bytes carry. -/
theorem Spec.decVBI_printVBI (n : Nat) (rest : List UInt8)
    (hn : n < 268435456) :
    decVBI (printVBI n ++ rest) = some (n, rest) := sorry

/-! ## Refused inputs

Single inputs the reader refuses, one for each headline rule of
`SPEC.md`. Each input is one of the named rejection cases in the
test harness. The differential tests cover these rules on many
more inputs; these statements pin them so a reader of the
specification can check each rule against one concrete case. -/

/-- A remaining length whose fourth byte carries a continuation
    mark is refused: the value would need a fifth byte, and four
    is the limit. -/
theorem Spec.rejects_five_byte_remaining_length :
    (parse ([192, 255, 255, 255, 255, 127] : List UInt8)).isSome
      = false := sorry

/-- A SUBSCRIBE packet with flags 0000 is refused: the value the
    standard fixes for SUBSCRIBE is 0010. -/
theorem Spec.rejects_subscribe_flags :
    (parse ([128, 7, 0, 1, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := sorry

/-- A PUBLISH packet with QoS 3 is refused: that QoS value is
    reserved. -/
theorem Spec.rejects_publish_qos3 :
    (parse ([54, 7, 0, 1, 97, 0, 1, 0, 120] : List UInt8)).isSome
      = false := sorry

/-- A PUBLISH topic name holding a wildcard is refused: `a/#` is
    a filter, not a topic name. -/
theorem Spec.rejects_wildcard_topic :
    (parse ([48, 7, 0, 3, 97, 47, 35, 0, 120] : List UInt8)).isSome
      = false := sorry

/-- A CONNECT whose protocol name is not `MQTT` is refused. -/
theorem Spec.rejects_wrong_protocol_name :
    (parse ([16, 14, 0, 4, 77, 81, 84, 85, 5, 2, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := sorry

/-- A CONNECT with the reserved bit of the connect flags byte
    set is refused. -/
theorem Spec.rejects_reserved_connect_flag :
    (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 3, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := sorry

/-- A property standing on a packet type that does not allow it
    is refused: here a subscription identifier on a CONNECT. -/
theorem Spec.rejects_property_wrong_type :
    (parse ([16, 16, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 2, 11, 5, 0,
      1, 120] : List UInt8)).isSome = false := sorry

/-- A single use property standing twice in one block is
    refused: here the topic alias on a PUBLISH, twice. -/
theorem Spec.rejects_repeated_property :
    (parse ([50, 12, 0, 1, 97, 0, 3, 6, 35, 0, 1, 35, 0, 2]
      : List UInt8)).isSome = false := sorry

/-- A SUBSCRIBE with packet identifier 0 is refused:
    identifiers are never 0. -/
theorem Spec.rejects_subscribe_id_zero :
    (parse ([130, 7, 0, 0, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := sorry

/-- A PINGREQ with a body is refused: its remaining length must
    be 0. -/
theorem Spec.rejects_pingreq_body :
    (parse ([192, 1, 0] : List UInt8)).isSome = false := sorry

/-- A packet type outside the seven in this slice is refused:
    here type 2. -/
theorem Spec.rejects_unknown_type :
    (parse ([32, 0] : List UInt8)).isSome = false := sorry
