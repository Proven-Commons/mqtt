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


theorem Spec.rejects_pingreq_body :
    (parse ([192, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_unknown_type :
    (parse ([32, 0] : List UInt8)).isSome = false := by
  decide +kernel
