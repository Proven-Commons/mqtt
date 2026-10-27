/-
  Proofs for the strict UTF-8 codec in Mqtt/Utf8.lean: the one
  claim the packet round trip needs is that decoding the
  encoding of any text gives the text back.

  Carried in with the codec from the Proven Commons jws slice,
  where this proof was first written, and adapted to the
  renamed namespace.
-/

import Mqtt.Utf8

namespace Mqtt.Utf8.Proofs

open Mqtt.Utf8

/-- A number below 256 written as a byte reads back as itself. -/
theorem toNat_toUInt8 {k : Nat} (h : k < 256) : k.toUInt8.toNat = k := by
  simp; omega

/-- A character value is below 110000, and no character value
    lies in the surrogate gap D800 to DFFF: the Unicode scalar
    range every `Char` lives in. -/
theorem char_bounds (c : Char) :
    c.toNat < 0x110000 ∧ ¬ (0xD800 ≤ c.toNat ∧ c.toNat < 0xE000) := by
  have h := c.valid
  show c.val.toNat < 0x110000 ∧ ¬ (0xD800 ≤ c.val.toNat ∧ c.val.toNat < 0xE000)
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩

/-- A byte whose value is known to be a continuation byte reads
    back as its payload value. -/
theorem contVal_of_toNat {b : UInt8} {k : Nat} (h : b.toNat = 0x80 + k) (hk : k < 64) :
    contVal b = some k := by
  unfold contVal
  rw [h, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- One step of the decoder on a plain byte. -/
theorem decode_one (b : UInt8) (bs : List UInt8) (hb : b.toNat < 0x80) :
    decode (b :: bs) = (decode bs).map (Char.ofNat b.toNat :: ·) := by
  cases bs with
  | nil => rw [decode.eq_3, if_pos hb]
  | cons b1 bs' => rw [decode.eq_2, if_pos hb]

/-- One step of the decoder on a two byte form. -/
theorem decode_two (b b1 : UInt8) (bs : List UInt8) (v : Nat)
    (hb : 0xC2 ≤ b.toNat ∧ b.toNat < 0xE0) (hv : contVal b1 = some v) :
    decode (b :: b1 :: bs) =
      (decode bs).map (Char.ofNat ((b.toNat - 0xC0) * 64 + v) :: ·) := by
  rw [decode.eq_2, if_neg (by omega : ¬ b.toNat < 0x80),
    if_neg (by omega : ¬ b.toNat < 0xC2), if_pos (by omega : b.toNat < 0xE0), hv]

/-- One step of the decoder on a three byte form. -/
theorem decode_three (b b1 b2 : UInt8) (bs : List UInt8) (v1 v2 : Nat)
    (hb : 0xE0 ≤ b.toNat ∧ b.toNat < 0xF0)
    (hside : (b.toNat = 0xE0 → 0x20 ≤ v1) ∧ (b.toNat = 0xED → v1 < 0x20))
    (hv1 : contVal b1 = some v1) (hv2 : contVal b2 = some v2) :
    decode (b :: b1 :: b2 :: bs) =
      (decode bs).map (Char.ofNat ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) :: ·) := by
  rw [decode.eq_2, if_neg (by omega : ¬ b.toNat < 0x80),
    if_neg (by omega : ¬ b.toNat < 0xC2), if_neg (by omega : ¬ b.toNat < 0xE0),
    if_pos (by omega : b.toNat < 0xF0)]
  dsimp only
  rw [hv1, hv2]
  dsimp only
  rw [if_pos hside]

/-- One step of the decoder on a four byte form. -/
theorem decode_four (b b1 b2 b3 : UInt8) (bs : List UInt8) (v1 v2 v3 : Nat)
    (hb : 0xF0 ≤ b.toNat ∧ b.toNat < 0xF5)
    (hside : (b.toNat = 0xF0 → 0x10 ≤ v1) ∧ (b.toNat = 0xF4 → v1 < 0x10))
    (hv1 : contVal b1 = some v1) (hv2 : contVal b2 = some v2)
    (hv3 : contVal b3 = some v3) :
    decode (b :: b1 :: b2 :: b3 :: bs) =
      (decode bs).map
        (Char.ofNat ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) :: ·) := by
  rw [decode.eq_2, if_neg (by omega : ¬ b.toNat < 0x80),
    if_neg (by omega : ¬ b.toNat < 0xC2), if_neg (by omega : ¬ b.toNat < 0xE0),
    if_neg (by omega : ¬ b.toNat < 0xF0), if_pos (by omega : b.toNat < 0xF5)]
  dsimp only
  rw [hv1, hv2, hv3]
  dsimp only
  rw [if_pos hside]

/-- Decoding one encoded character in front of any bytes decodes
    the character and then the bytes. The four cases are the
    four lengths; each one applies the step lemma for its
    length, checks the side conditions with arithmetic, and
    rebuilds the character value. -/
theorem decode_append_char (c : Char) (bs : List UInt8) :
    decode (encodeChar c ++ bs) = (decode bs).map (c :: ·) := by
  obtain ⟨hmax, hnsur⟩ := char_bounds c
  by_cases h1 : c.toNat < 0x80
  · rw [encodeChar, if_pos h1, List.cons_append, List.nil_append,
      decode_one _ _ (by rw [toNat_toUInt8 (by omega)]; exact h1),
      toNat_toUInt8 (by omega), Char.ofNat_toNat]
  · rw [encodeChar, if_neg h1]
    by_cases h2 : c.toNat < 0x800
    · have hlead : (0xC0 + c.toNat / 64).toUInt8.toNat = 0xC0 + c.toNat / 64 :=
        toNat_toUInt8 (by omega)
      rw [if_pos h2, List.cons_append, List.cons_append, List.nil_append,
        decode_two _ _ _ _ ⟨by omega, by omega⟩
          (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide))),
        hlead,
        show (0xC0 + c.toNat / 64 - 0xC0) * 64 + c.toNat % 64 = c.toNat by omega,
        Char.ofNat_toNat]
    · rw [if_neg h2]
      by_cases h3 : c.toNat < 0x10000
      · have hlead : (0xE0 + c.toNat / 4096).toUInt8.toNat = 0xE0 + c.toNat / 4096 :=
          toNat_toUInt8 (by omega)
        rw [if_pos h3, List.cons_append, List.cons_append, List.cons_append,
          List.nil_append,
          decode_three _ _ _ _ _ _ ⟨by omega, by omega⟩
            ⟨fun hb => by rw [hlead] at hb; omega,
             fun hb => by rw [hlead] at hb; omega⟩
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide)))
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide))),
          hlead,
          show (0xE0 + c.toNat / 4096 - 0xE0) * 4096 + (c.toNat / 64) % 64 * 64 +
            c.toNat % 64 = c.toNat by omega,
          Char.ofNat_toNat]
      · have hlead : (0xF0 + c.toNat / 262144).toUInt8.toNat = 0xF0 + c.toNat / 262144 :=
          toNat_toUInt8 (by omega)
        rw [if_neg h3, List.cons_append, List.cons_append, List.cons_append,
          List.cons_append, List.nil_append,
          decode_four _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩
            ⟨fun hb => by rw [hlead] at hb; omega,
             fun hb => by rw [hlead] at hb; omega⟩
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide)))
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide)))
            (contVal_of_toNat (toNat_toUInt8 (by omega)) (Nat.mod_lt _ (by decide))),
          hlead,
          show (0xF0 + c.toNat / 262144 - 0xF0) * 262144 + (c.toNat / 4096) % 64 * 4096 +
            (c.toNat / 64) % 64 * 64 + c.toNat % 64 = c.toNat by omega,
          Char.ofNat_toNat]

/-- Decoding the encoding of any text gives the text back. -/
theorem decode_encode : ∀ cs : List Char, decode (encode cs) = some cs := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show decode (encodeChar c ++ encode cs) = some (c :: cs)
    rw [decode_append_char, ih]
    rfl

end Mqtt.Utf8.Proofs
