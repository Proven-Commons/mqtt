/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The round trips are the theorems proved in
  `Proofs/RoundTrip.lean`. The refusals are single inputs,
  checked in the kernel with `decide +kernel`: no native
  evaluation, which the bar forbids.
-/

import Mqtt
import Proofs.RoundTrip

open Mqtt

theorem Spec.parsePacket_print (p : Packet) (rest : List UInt8)
    (h : PacketWF p) :
    parsePacket (print p ++ rest) = some (p, rest) :=
  Mqtt.Proofs.parsePacket_print p rest h

theorem Spec.parse_print (p : Packet) (h : PacketWF p) :
    parse (print p) = some p :=
  Mqtt.Proofs.parse_print p h

theorem Spec.decVBI_printVBI (n : Nat) (rest : List UInt8)
    (hn : n < 268435456) :
    decVBI (printVBI n ++ rest) = some (n, rest) :=
  Mqtt.Proofs.decVBI_printVBI n rest hn


theorem Spec.decVBI_canonical (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) :
    n < 268435456 ∧ bs = printVBI n ++ r :=
  Mqtt.Proofs.decVBI_canonical bs n r h

theorem Spec.parsePacket_frame (bs : List UInt8) (p : Packet)
    (r : List UInt8) (h : parsePacket bs = some (p, r)) :
    ∃ (b : UInt8) (body : List UInt8), body.length < 268435456
      ∧ bs = b :: (printVBI body.length ++ body) ++ r :=
  Mqtt.Proofs.parsePacket_frame bs p r h

theorem Spec.rejects_non_minimal_remaining_length :
    (parse ([192, 128, 0] : List UInt8)).isSome = false
      ∧ parse ([192, 0] : List UInt8) = some .pingreq := by
  decide +kernel

theorem Spec.decVBI_four_byte_cap (b0 b1 b2 b3 : UInt8) (rest : List UInt8)
    (h0 : 128 ≤ b0.toNat) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat)
    (h3 : 128 ≤ b3.toNat) :
    decVBI (b0 :: b1 :: b2 :: b3 :: rest) = none :=
  Mqtt.Proofs.decVBI_four_byte_cap b0 b1 b2 b3 rest h0 h1 h2 h3

theorem Spec.parsePacket_four_byte_cap (h b0 b1 b2 b3 : UInt8)
    (rest : List UInt8)
    (h0 : 128 ≤ b0.toNat) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat)
    (h3 : 128 ≤ b3.toNat) :
    parsePacket (h :: b0 :: b1 :: b2 :: b3 :: rest) = none
      ∧ parse (h :: b0 :: b1 :: b2 :: b3 :: rest) = none :=
  Mqtt.Proofs.parsePacket_four_byte_cap h b0 b1 b2 b3 rest h0 h1 h2 h3


theorem Spec.rejects_subscribe_flags :
    (parse ([128, 7, 0, 1, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_publish_qos3 :
    (parse ([54, 7, 0, 1, 97, 0, 1, 0, 120] : List UInt8)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_wildcard_topic :
    (parse ([48, 7, 0, 3, 97, 47, 35, 0, 120] : List UInt8)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_wrong_protocol_name :
    (parse ([16, 14, 0, 4, 77, 81, 84, 85, 5, 2, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_reserved_connect_flag :
    (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 3, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_will_bits_without_will :
    (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 10, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false
    ∧ (parse ([16, 14, 0, 4, 77, 81, 84, 84, 5, 34, 0, 0, 0, 0, 1, 120]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_property_wrong_type :
    (parse ([16, 16, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 2, 11, 5, 0,
      1, 120] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_repeated_property :
    (parse ([50, 12, 0, 1, 97, 0, 3, 6, 35, 0, 1, 35, 0, 2]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_subscribe_id_zero :
    (parse ([130, 7, 0, 0, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_property_value_rules :
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
    ∧ (parse ([48, 7, 0, 1, 97, 3, 8, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_pingreq_body :
    (parse ([192, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_unknown_type :
    (parse ([32, 0] : List UInt8)).isSome = false := by
  decide +kernel
