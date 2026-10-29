/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The round trips are the theorems proved in
  `Proofs/RoundTrip.lean`, the soundness of the reader the
  ones proved in `Proofs/Sound.lean`, and the statements whose
  rules stand in `Spec/Defs.lean` the ones proved in
  `Proofs/Rules.lean`. The example refusals are single inputs,
  checked in the kernel with `decide +kernel`: no native
  evaluation, which the bar forbids.
-/

import Mqtt
import Spec.Defs
import Proofs.RoundTrip
import Proofs.Sound
import Proofs.Rules

open Mqtt

theorem Spec.parsePacket_print (p : Packet) (rest : List UInt8)
    (h : PacketWF p) :
    parsePacket (print p ++ rest) = some (p, rest) :=
  Mqtt.Proofs.parsePacket_print p rest h

theorem Spec.parse_print (p : Packet) (h : PacketWF p) :
    parse (print p) = some p :=
  Mqtt.Proofs.parse_print p h

theorem Spec.parse_sound (bs : List UInt8) (p : Packet)
    (h : parse bs = some p) : PacketWF p ∧ print p = bs :=
  Mqtt.Proofs.parse_inv bs p h

theorem Spec.parsePacket_sound (bs : List UInt8) (p : Packet)
    (r : List UInt8) (h : parsePacket bs = some (p, r)) :
    PacketWF p ∧ bs = print p ++ r :=
  Mqtt.Proofs.parsePacket_inv bs p r h

theorem Spec.decVBI_printVBI (n : Nat) (rest : List UInt8)
    (hn : n < 268435456) :
    decVBI (printVBI n ++ rest) = some (n, rest) :=
  Mqtt.Proofs.decVBI_printVBI n rest hn


theorem Spec.decVBI_canonical (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) :
    n < 268435456 ∧ bs = printVBI n ++ r :=
  Mqtt.Proofs.decVBI_canonical bs n r h

theorem Spec.printVBI_length (n : Nat) (hn : n < 268435456) :
    (printVBI n).length = Spec.vbiSize n :=
  Mqtt.Proofs.printVBI_length n hn

theorem Spec.decVBI_length (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) :
    bs.length = r.length + Spec.vbiSize n :=
  Mqtt.Proofs.decVBI_length bs n r h

theorem Spec.parsePacket_frame (bs : List UInt8) (p : Packet)
    (r : List UInt8) (h : parsePacket bs = some (p, r)) :
    ∃ (b : UInt8) (body : List UInt8), body.length < 268435456
      ∧ bs = b :: (printVBI body.length ++ body) ++ r :=
  Mqtt.Proofs.parsePacket_frame bs p r h

theorem Spec.rejects_non_minimal_remaining_length :
    (parse ([192, 128, 0] : List UInt8)).isSome = false
      ∧ parse ([192, 0] : List UInt8) = some .pingreq := by
  decide +kernel

/-- A writing longer than its value needs is refused in each other
    place a variable byte integer stands in a packet, one example
    input each, while the same packet with the shortest writing is
    accepted: the property length 0 of a PUBLISH written `[128, 0]`,
    the property identifier 1 (Payload Format Indicator) written
    `[129, 0]`, and the Subscription Identifier value 1 of a
    SUBSCRIBE written `[129, 128, 0]`. These are single inputs: no
    statement here covers every input in these places. -/
theorem Spec.rejects_non_minimal_property_vbis :
    (parse ([48, 5, 0, 1, 97, 128, 0] : List UInt8)).isSome = false
      ∧ (parse ([48, 4, 0, 1, 97, 0] : List UInt8)).isSome = true
      ∧ (parse ([48, 7, 0, 1, 97, 3, 129, 0, 1] : List UInt8)).isSome = false
      ∧ (parse ([48, 6, 0, 1, 97, 2, 1, 1] : List UInt8)).isSome = true
      ∧ (parse ([130, 11, 0, 1, 3, 11, 129, 128, 0, 0, 1, 97, 0]
          : List UInt8)).isSome = false
      ∧ (parse ([130, 9, 0, 1, 2, 11, 1, 0, 1, 97, 0]
          : List UInt8)).isSome = true := by
  decide +kernel

/-- The standard's worked table of variable byte integers
    (section 1.5.5): the printer writes each boundary value as the
    bytes the table gives, and the reader reads those bytes as that
    value. These are single inputs; for other values the bytes are
    pinned by the byte count (`Spec.printVBI_length`) and the round
    trip (`Spec.decVBI_printVBI`), not by a statement of their
    contents. -/
theorem Spec.vbi_worked_table :
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
      ∧ decVBI [255, 255, 255, 127] = some (268435455, []) := by
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

theorem Spec.parse_whole (bs : List UInt8) (p : Packet) :
    parse bs = some p ↔ parsePacket bs = some (p, []) :=
  Mqtt.Proofs.parse_iff bs p

theorem Spec.header_rule (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) :
    ∃ (b : UInt8) (tl : List UInt8), bs = b :: tl ∧ b ∈ Spec.headerBytes :=
  Mqtt.Proofs.header_rule bs p r h

theorem Spec.connect_rule (bs r : List UInt8) (c : Connect)
    (h : parsePacket bs = some (.connect c, r)) :
    (∃ (f : UInt8) (tail : List UInt8),
      bs = 16 :: (printVBI (8 + tail.length) ++ ([0, 4, 77, 81, 84, 84, 5, f] ++ tail)) ++ r
      ∧ Spec.ConnectFlagsRule f.toNat)
    ∧ ∀ w, c.will = some w → w.topic ≠ [] ∧ Spec.TopicNameRule w.topic :=
  Mqtt.Proofs.connect_rule bs r c h

theorem Spec.publish_rule (bs r : List UInt8) (m : Publish)
    (h : parsePacket bs = some (.publish m, r)) :
    Spec.TopicNameRule m.topic ∧ (m.topic = [] → ∃ q ∈ m.props, q.id = 0x23)
    ∧ (m.packetId = none ↔ m.qos = 0) ∧ (∀ i, m.packetId = some i → i ≠ 0) :=
  Mqtt.Proofs.publish_rule bs r m h

theorem Spec.subscribe_rule (bs r : List UInt8) (i : Nat) (ps : List Property)
    (fs : List (List Char × SubOpts))
    (h : parsePacket bs = some (.subscribe i ps fs, r)) :
    i ≠ 0 ∧ fs ≠ [] ∧ ∀ fo ∈ fs, Spec.FilterRule fo.1 fo.2 :=
  Mqtt.Proofs.subscribe_rule bs r i ps fs h

theorem Spec.property_rule (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) :
    ∀ b ∈ Spec.blocks p, Spec.BlockRule b.1 b.2 :=
  Mqtt.Proofs.property_rule bs r p h

theorem Spec.empty_body_rule (bs r : List UInt8) :
    (parsePacket bs = some (.pingreq, r) → bs = [192, 0] ++ r)
    ∧ (parsePacket bs = some (.pingresp, r) → bs = [208, 0] ++ r) :=
  Mqtt.Proofs.empty_body_rule bs r

theorem Spec.rejects_subscribe_flags :
    (parse ([128, 7, 0, 1, 0, 0, 1, 97, 0] : List UInt8)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_publish_qos3 :
    (parse ([54, 7, 0, 1, 97, 0, 1, 0, 120] : List UInt8)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_dup_at_qos0 :
    (parse ([56, 4, 0, 1, 97, 0] : List UInt8)).isSome = false
    ∧ parse ([48, 4, 0, 1, 97, 0] : List UInt8)
      = some (.publish ⟨false, 0, false, ['a'], none, [], []⟩) := by
  decide +kernel


theorem Spec.empty_topic_needs_alias :
    parse ([48, 6, 0, 0, 3, 35, 0, 1] : List UInt8)
      = some (.publish ⟨false, 0, false, [], none, [⟨35, .twoByte 1⟩], []⟩)
    ∧ (parse ([48, 3, 0, 0, 0] : List UInt8)).isSome = false := by
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


theorem Spec.rejects_bad_topic_filters :
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
            ⟨0, false, false, 0⟩)]) := by
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


theorem Spec.disconnect_short_form :
    parse ([224, 1, 0] : List UInt8) = some (.disconnect (some (0, none)))
    ∧ print (.disconnect (some (0, none))) = [224, 1, 0]
    ∧ parse ([224, 2, 0, 0] : List UInt8)
      = some (.disconnect (some (0, some [])))
    ∧ print (.disconnect (some (0, some []))) = [224, 2, 0, 0] := by
  decide +kernel


theorem Spec.rejects_pingreq_body :
    (parse ([192, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_unknown_type :
    (parse ([32, 0] : List UInt8)).isSome = false := by
  decide +kernel
