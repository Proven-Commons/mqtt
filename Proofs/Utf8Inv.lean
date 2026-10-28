/-
  The other direction of the strict UTF-8 codec: what the decoder
  accepts is the encoding of the text it returns. Together with
  `Mqtt.Utf8.Proofs.decode_encode` in `Proofs/Utf8.lean`, the
  decoder is exactly the inverse of the encoder. The packet
  reader's soundness (`Proofs/Sound.lean`) rests on it for every
  string field.
-/

import Proofs.Utf8

namespace Mqtt.Utf8.Proofs

open Mqtt.Utf8

/-- A number in the Unicode scalar range, outside the surrogate
    gap, is the value of the character it names. -/
theorem char_ofNat_toNat (n : Nat) (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left h]
  simp [Char.ofNatAux, Char.toNat, UInt32.toNat_ofNatLT]

/-- What a continuation byte's payload says about the byte. -/
theorem contVal_inv {b : UInt8} {v : Nat} (h : contVal b = some v) :
    b.toNat = 0x80 + v ∧ v < 64 := by
  unfold contVal at h
  by_cases hc : 0x80 ≤ b.toNat ∧ b.toNat < 0xC0
  · rw [ite_eq_left hc] at h
    simp only [Option.some.injEq] at h
    omega
  · rw [ite_eq_right hc] at h
    cases h

/-- A number equal to a byte's value, written as a byte, is that
    byte. -/
theorem byte_of_toNat {b : UInt8} {n : Nat} (h : b.toNat = n) : n.toUInt8 = b := by
  rw [← h]; exact UInt8.ofNat_toNat

/-- The encoding of a text with a first character. -/
theorem encode_cons (c : Char) (cs : List Char) :
    encode (c :: cs) = encodeChar c ++ encode cs := by
  simp [encode, List.flatMap_cons]

/-- What the strict decoder accepts is the encoding of the text
    it returns. -/
theorem decode_inv (bs : List UInt8) : ∀ (cs : List Char),
    decode bs = some cs → encode cs = bs := by
  induction bs using decode.induct with
  | case1 =>
    intro cs h
    rw [decode.eq_1] at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  | case2 b rest hb ih =>
    intro cs h
    rw [decode_one b rest hb] at h
    obtain ⟨cs', h1, h2⟩ := Option.map_eq_some_iff.mp h
    subst h2
    rw [encode_cons, ih cs' h1]
    have hn := char_ofNat_toNat b.toNat (Or.inl (by omega))
    unfold encodeChar
    simp only [hn]
    rw [ite_eq_left hb, byte_of_toNat rfl]
    rfl
  | case4 b h1 h2 h3 b1 rest1 v1 hv1 ih =>
    intro cs h
    obtain ⟨hb1, hv⟩ := contVal_inv hv1
    rw [decode_two b b1 rest1 v1 ⟨by omega, h3⟩ hv1] at h
    obtain ⟨cs', h1', h2'⟩ := Option.map_eq_some_iff.mp h
    subst h2'
    rw [encode_cons, ih cs' h1']
    have hn := char_ofNat_toNat ((b.toNat - 0xC0) * 64 + v1) (Or.inl (by omega))
    unfold encodeChar
    simp only [hn]
    rw [ite_eq_right (by omega), ite_eq_left (by omega),
      byte_of_toNat (by omega : b.toNat = 0xC0 + ((b.toNat - 0xC0) * 64 + v1) / 64),
      byte_of_toNat (by omega : b1.toNat = 0x80 + ((b.toNat - 0xC0) * 64 + v1) % 64)]
    rfl
  | case7 b h1 h2 h3 h4 b1 b2 rest1 v1 v2 hv2 hv1 hside ih =>
    intro cs h
    obtain ⟨hb1, hv1'⟩ := contVal_inv hv1
    obtain ⟨hb2, hv2'⟩ := contVal_inv hv2
    rw [decode_three b b1 b2 rest1 v1 v2 ⟨by omega, h4⟩ hside hv1 hv2] at h
    obtain ⟨cs', h1', h2'⟩ := Option.map_eq_some_iff.mp h
    subst h2'
    rw [encode_cons, ih cs' h1']
    obtain ⟨hs1, hs2⟩ := hside
    have hn := char_ofNat_toNat ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) (by
      by_cases he : b.toNat = 0xE0
      · have := hs1 he; omega
      · by_cases hd : b.toNat = 0xED
        · have := hs2 hd; omega
        · by_cases hl : b.toNat < 0xED
          · omega
          · omega)
    have hlow : 0x800 ≤ (b.toNat - 0xE0) * 4096 + v1 * 64 + v2 := by
      by_cases he : b.toNat = 0xE0
      · have := hs1 he; omega
      · omega
    unfold encodeChar
    simp only [hn]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      byte_of_toNat (by omega :
        b.toNat = 0xE0 + ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) / 4096),
      byte_of_toNat (by omega :
        b1.toNat = 0x80 + ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) / 64 % 64),
      byte_of_toNat (by omega :
        b2.toNat = 0x80 + ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) % 64)]
    rfl
  | case11 b h1 h2 h3 h4 h5 b1 b2 b3 rest1 v1 v2 v3 hv3 hv2 hv1 hside ih =>
    intro cs h
    obtain ⟨hb1, hv1'⟩ := contVal_inv hv1
    obtain ⟨hb2, hv2'⟩ := contVal_inv hv2
    obtain ⟨hb3, hv3'⟩ := contVal_inv hv3
    rw [decode_four b b1 b2 b3 rest1 v1 v2 v3 ⟨by omega, h5⟩ hside hv1 hv2 hv3] at h
    obtain ⟨cs', h1', h2'⟩ := Option.map_eq_some_iff.mp h
    subst h2'
    rw [encode_cons, ih cs' h1']
    obtain ⟨hs1, hs2⟩ := hside
    have hlow : 0x10000 ≤ (b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3 := by
      by_cases he : b.toNat = 0xF0
      · have := hs1 he; omega
      · omega
    have hhigh : (b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3 < 0x110000 := by
      by_cases he : b.toNat = 0xF4
      · have := hs2 he; omega
      · omega
    have hn := char_ofNat_toNat ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3)
      (Or.inr ⟨by omega, hhigh⟩)
    unfold encodeChar
    simp only [hn]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      byte_of_toNat (by omega :
        b.toNat = 0xF0 + ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) / 262144),
      byte_of_toNat (by omega :
        b1.toNat = 0x80 + ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) / 4096 % 64),
      byte_of_toNat (by omega :
        b2.toNat = 0x80 + ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) / 64 % 64),
      byte_of_toNat (by omega :
        b3.toNat = 0x80 + ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) % 64)]
    rfl
  | case8 b h1 h2 h3 h4 b1 b2 rest1 v1 v2 hv2 hv1 hside =>
    intro cs h
    rw [decode.eq_def] at h
    simp only [hv1, hv2] at h
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4,
      ite_eq_right hside] at h
    cases h
  | case12 b h1 h2 h3 h4 h5 b1 b2 b3 rest1 v1 v2 v3 hv3 hv2 hv1 hside =>
    intro cs h
    rw [decode.eq_def] at h
    simp only [hv1, hv2, hv3] at h
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
      ite_eq_left h5, ite_eq_right hside] at h
    cases h
  | _ =>
    intro cs h
    rw [decode.eq_def] at h
    simp only at h
    repeat' (split at h)
    all_goals (first | (simp_all; done) | (simp_all; omega) | omega | (exfalso; simp_all))

end Mqtt.Utf8.Proofs
