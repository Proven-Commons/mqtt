/-
  Soundness of the packet reader: what it accepts is exactly the
  printed form of a well formed packet. The main claims are
  `Mqtt.Proofs.parse_inv`, for the whole input reader, and
  `Mqtt.Proofs.parsePacket_inv`, for the stream reader.

  Together with the round trip in `Mqtt/Proofs/RoundTrip.lean`, this
  makes the reader and the printer exact inverses between well
  formed packets and the byte lists the reader accepts: a byte
  list is accepted if and only if it is the printing of a well
  formed packet, and the packet read is that packet. Each lemma
  below is the inverse of one field reader, in the shape "what
  the reader accepts is the printed field, followed by the bytes
  it returns, and the field is well formed".
-/

import Mqtt.Proofs.RoundTrip
import Mqtt.Proofs.Utf8Inv

namespace Mqtt.Proofs

open Mqtt

/-- What the big endian reader accepts is the writing of the
    number it returns, at its width, with the returned bytes
    after it. -/
theorem readNat_inv : ∀ (k : Nat) (bs : List UInt8) (n : Nat) (r : List UInt8),
    readNat k bs = some (n, r) → n < 256 ^ k ∧ bs = writeBE k n ++ r := by
  intro k
  induction k with
  | zero =>
    intro bs n r h
    rw [readNat] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact ⟨by decide, rfl⟩
  | succ k ih =>
    intro bs n r h
    cases bs with
    | nil => rw [readNat] at h; cases h
    | cons b bs =>
      rw [readNat_succ_cons] at h
      obtain ⟨⟨u, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨hn, hr⟩ := h2
      subst hn
      subst hr
      obtain ⟨hu, hbs⟩ := ih bs u r' h1
      have hP : 0 < 256 ^ k := Nat.pow_pos (by decide)
      have hb : b.toNat < 256 := UInt8.toNat_lt b
      refine ⟨?_, ?_⟩
      · have e1 : b.toNat * 256 ^ k + u < (b.toNat + 1) * 256 ^ k := by
          rw [Nat.succ_mul]; omega
        have e2 : (b.toNat + 1) * 256 ^ k ≤ 256 * 256 ^ k :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256]
        omega
      · rw [writeBE_succ, hbs]
        have hdiv : (b.toNat * 256 ^ k + u) / 256 ^ k = b.toNat := by
          rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hu]
          omega
        have hmod : (b.toNat * 256 ^ k + u) % 256 ^ k = u := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
        rw [hdiv, hmod, Nat.mod_eq_of_lt hb, byte_eq_toUInt8]
        rfl

/-- A one byte writing of a number below 256 is that byte. -/
theorem writeBE_one (n : Nat) (h : n < 256) : writeBE 1 n = [n.toUInt8] := by
  rw [writeBE_succ]
  simp only [Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.mod_eq_of_lt h]
  rfl

/-- What the single byte reader accepts is one byte. -/
theorem readByte_inv (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : readByte bs = some (n, r)) : n < 256 ∧ bs = n.toUInt8 :: r := by
  cases bs with
  | nil => cases h
  | cons b bs =>
    rw [readByte_cons] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact ⟨UInt8.toNat_lt b, by rw [byte_eq_toUInt8]⟩

/-- The null character check passes only on a text without the
    null character. -/
theorem checkChars_inv {cs s : List Char} (h : checkChars cs = some s) :
    s = cs ∧ '\u0000' ∉ cs := by
  unfold checkChars at h
  by_cases hn : hasNul cs = true
  · rw [ite_eq_left hn] at h; cases h
  · rw [ite_eq_right hn] at h
    simp only [Option.some.injEq] at h
    refine ⟨h.symm, ?_⟩
    intro hm
    apply hn
    simp only [hasNul, List.any_eq_true]
    exact ⟨_, hm, by simp⟩

/-- What the string reader accepts is the printed form of a well
    formed string, with the returned bytes after it. -/
theorem readStr_inv (bs : List UInt8) (s : List Char) (r : List UInt8)
    (h : readStr bs = some (s, r)) : StrWF s ∧ bs = printStr s ++ r := by
  rw [readStr_step] at h
  obtain ⟨⟨len, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨chunk, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s', h3, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, hr⟩ := h
  subst hs
  subst hr
  obtain ⟨cs, h4, h5⟩ := Option.bind_eq_some_iff.mp h3
  obtain ⟨hsc, hnul⟩ := checkChars_inv h5
  subst hsc
  obtain ⟨hlen, hbs⟩ := readNat_inv 2 bs len r1 h1
  obtain ⟨hcl, hr1⟩ := readBytes_inv len r1 chunk r2 h2
  have henc := Mqtt.Utf8.Proofs.decode_inv chunk s' h4
  refine ⟨⟨hnul, ?_⟩, ?_⟩
  · rw [henc, hcl]
    have : (256 : Nat) ^ 2 = 65536 := by decide
    omega
  · rw [hbs, hr1, printStr, henc, hcl, List.append_assoc]

/-- What the binary reader accepts is the printed form of binary
    data that fits its prefix, with the returned bytes after it. -/
theorem readBin_inv (bs : List UInt8) (d : List UInt8) (r : List UInt8)
    (h : readBin bs = some (d, r)) : BinWF d ∧ bs = printBin d ++ r := by
  rw [readBin_step] at h
  obtain ⟨⟨len, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hlen, hbs⟩ := readNat_inv 2 bs len r1 h1
  obtain ⟨hcl, hr1⟩ := readBytes_inv len r1 d r h
  refine ⟨?_, ?_⟩
  · show d.length ≤ 65535
    have : (256 : Nat) ^ 2 = 65536 := by decide
    omega
  · rw [hbs, hr1, printBin, hcl, List.append_assoc]


/-- What the property value reader accepts is the printed form
    of a well formed value of the type asked for. -/
theorem readPropVal_inv (t : PropType) (bs : List UInt8) (v : PropVal) (r : List UInt8)
    (h : readPropVal t bs = some (v, r)) :
    valType v = t ∧ ValWF v ∧ bs = printPropVal v ++ r := by
  cases t with
  | byte =>
    simp only [readPropVal] at h
    obtain ⟨⟨n, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hv, hr⟩ := h2
    subst hv
    subst hr
    obtain ⟨hn, hbs⟩ := readNat_inv 1 bs n r' h1
    have hn' : n < 256 := by simpa using hn
    exact ⟨rfl, hn', by rw [hbs, writeBE_one n hn']; rfl⟩
  | twoByte =>
    simp only [readPropVal] at h
    obtain ⟨⟨n, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hv, hr⟩ := h2
    subst hv
    subst hr
    obtain ⟨hn, hbs⟩ := readNat_inv 2 bs n r' h1
    exact ⟨rfl, show n < 65536 by simpa using hn, hbs⟩
  | fourByte =>
    simp only [readPropVal] at h
    obtain ⟨⟨n, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hv, hr⟩ := h2
    subst hv
    subst hr
    obtain ⟨hn, hbs⟩ := readNat_inv 4 bs n r' h1
    exact ⟨rfl, show n < 4294967296 by simpa using hn, hbs⟩
  | varByte =>
    simp only [readPropVal] at h
    obtain ⟨⟨n, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hv, hr⟩ := h2
    subst hv
    subst hr
    obtain ⟨hn, hbs⟩ := decVBI_canonical bs n r' h1
    exact ⟨rfl, hn, hbs⟩
  | utf8 =>
    simp only [readPropVal] at h
    obtain ⟨⟨s, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hv, hr⟩ := h2
    subst hv
    subst hr
    obtain ⟨hs, hbs⟩ := readStr_inv bs s r' h1
    exact ⟨rfl, hs, hbs⟩
  | utf8Pair =>
    rw [readPropVal_pair_step] at h
    obtain ⟨⟨k, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨w, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, hr⟩ := h
    subst hv
    subst hr
    obtain ⟨hk, hb1⟩ := readStr_inv bs k r1 h1
    obtain ⟨hw, hb2⟩ := readStr_inv r1 w r2 h2
    refine ⟨rfl, ⟨hk, hw⟩, ?_⟩
    rw [hb1, hb2]
    show _ = (printStr k ++ printStr w) ++ _
    rw [List.append_assoc]
  | binary =>
    simp only [readPropVal] at h
    obtain ⟨⟨d, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hv, hr⟩ := h2
    subst hv
    subst hr
    obtain ⟨hd, hbs⟩ := readBin_inv bs d r' h1
    exact ⟨rfl, hd, hbs⟩

/-- What the property reader accepts is the printed form of a
    property that stands where it was read: allowed on the
    block, of the table's type, well formed, keeping the value
    rules, and not a repeat of a single use property. -/
theorem readEntry_inv (s : PropSet) (seen : List Nat) (bs : List UInt8)
    (p : Property) (r : List UInt8) (h : readEntry s seen bs = some (p, r)) :
    p.id ∈ allowedOf s ∧ propTypeOf p.id = some (valType p.val) ∧ ValWF p.val
      ∧ propValOK p.id p.val = true ∧ (repeatableIn s p.id = true ∨ p.id ∉ seen)
      ∧ bs = printProperty p ++ r := by
  rw [readEntry_step] at h
  obtain ⟨⟨id, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, hbs⟩ := decVBI_canonical bs id r1 h1
  simp only at h
  by_cases hc : ((allowedOf s).contains id && (repeatableIn s id || !seen.contains id)) = true
  · rw [ite_eq_left hc] at h
    cases ht : propTypeOf id with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      simp only at h
      obtain ⟨⟨v, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
      simp only at h
      by_cases hok : propValOK id v = true
      · rw [ite_eq_left hok] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hp, hr⟩ := h
        subst hp
        subst hr
        obtain ⟨hty, hval, hr1⟩ := readPropVal_inv t r1 v r2 h2
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
        refine ⟨List.contains_iff_mem.mp hc.1, by rw [ht, hty], hval, hok, ?_, ?_⟩
        · cases hc.2 with
          | inl h => exact Or.inl h
          | inr h =>
            exact Or.inr (fun hm => by rw [List.contains_iff_mem.mpr hm] at h; cases h)
        · rw [hbs, hr1, printProperty, List.append_assoc]
      · rw [ite_eq_right hok] at h
        cases h
  · rw [ite_eq_right hc] at h
    cases h

/-- What the property list reader accepts is the printed form of
    a well formed list, and it reads to the end. -/
theorem readEntriesGo_inv : ∀ (fuel : Nat) (s : PropSet) (seen : List Nat)
    (bs : List UInt8) (ps : List Property) (r : List UInt8),
    readEntriesGo fuel s seen bs = some (ps, r) →
      r = [] ∧ PropsWF s seen ps ∧ bs = printPropsList ps := by
  intro fuel
  induction fuel with
  | zero =>
    intro s seen bs ps r h
    rw [readEntriesGo] at h
    by_cases he : bs.isEmpty = true
    · rw [ite_eq_left he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have : bs = [] := List.isEmpty_iff.mp he
      subst this
      exact ⟨rfl, trivial, rfl⟩
    · rw [ite_eq_right he] at h
      cases h
  | succ fuel ih =>
    intro s seen bs ps r h
    rw [readEntriesGo] at h
    by_cases he : bs.isEmpty = true
    · rw [ite_eq_left he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have : bs = [] := List.isEmpty_iff.mp he
      subst this
      exact ⟨rfl, trivial, rfl⟩
    · rw [ite_eq_right he] at h
      cases h1 : readEntry s seen bs with
      | none => rw [h1] at h; cases h
      | some pr =>
        obtain ⟨p, r1⟩ := pr
        rw [h1] at h
        simp only at h
        cases h2 : readEntriesGo fuel s (p.id :: seen) r1 with
        | none => rw [h2] at h; cases h
        | some qr =>
          obtain ⟨ps', r2⟩ := qr
          rw [h2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hps, hr⟩ := h
          subst hps
          subst hr
          obtain ⟨hid, hty, hval, hok, hrep, hbs⟩ := readEntry_inv s seen bs p r1 h1
          obtain ⟨hr2, hwf, hr1⟩ := ih s (p.id :: seen) r1 ps' r2 h2
          exact ⟨hr2, ⟨hid, hty, hval, hok, hrep, hwf⟩, by rw [hbs, hr1]; rfl⟩

/-- What the block insides reader accepts is the printed form of
    a well formed list that keeps the block rule. -/
theorem readEntries_inv (s : PropSet) (seg : List UInt8) (ps : List Property)
    (h : readEntries s seg = some ps) :
    PropsWF s [] ps ∧ authOK ps = true ∧ seg = printPropsList ps := by
  unfold readEntries at h
  cases h1 : readEntriesGo seg.length s [] seg with
  | none => rw [h1] at h; cases h
  | some pr =>
    obtain ⟨ps', r⟩ := pr
    obtain ⟨hr, hwf, hseg⟩ := readEntriesGo_inv _ _ _ _ _ _ h1
    subst hr
    rw [h1] at h
    simp only at h
    by_cases ha : authOK ps' = true
    · rw [ite_eq_left ha] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hwf, ha, hseg⟩
    · rw [ite_eq_right ha] at h
      cases h

/-- What the property block reader accepts is the printed form
    of a block fit to print, with the returned bytes after it. -/
theorem readProps_inv (s : PropSet) (bs : List UInt8) (ps : List Property)
    (r : List UInt8) (h : readProps s bs = some (ps, r)) :
    PropsBlockWF s ps ∧ bs = printProps ps ++ r := by
  rw [readProps_step] at h
  obtain ⟨⟨len, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨seg, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ps', h3, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hp, hr⟩ := h
  subst hp
  subst hr
  obtain ⟨hlen, hbs⟩ := decVBI_canonical bs len r1 h1
  obtain ⟨hsl, hr1⟩ := readBytes_inv len r1 seg r2 h2
  obtain ⟨hwf, hauth, hseg⟩ := readEntries_inv s seg ps' h3
  refine ⟨⟨hwf, by rw [← hseg, hsl]; exact hlen, hauth⟩, ?_⟩
  rw [hbs, hr1, printProps, ← hseg, hsl, List.append_assoc]


/-- What the options byte reader accepts is the printed form of
    well formed options. -/
theorem readOptsByte_inv (b : Nat) (o : SubOpts) (h : readOptsByte b = some o) :
    OptsWF o ∧ (printOptsByte o).toNat = b := by
  unfold readOptsByte at h
  by_cases hc : b < 64 ∧ b % 4 ≠ 3 ∧ (b / 16) % 4 ≠ 3
  · rw [ite_eq_left hc] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
    unfold printOptsByte
    dsimp only
    by_cases h4 : (b / 4) % 2 = 1 <;> by_cases h8 : (b / 8) % 2 = 1 <;>
      simp only [h4, h8, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  · rw [ite_eq_right hc] at h
    cases h

/-- A flag bit as a number. -/
theorem if_bit (n k m : Nat) : (if flagBit n k then m else 0) = m * (n / 2 ^ k % 2) := by
  unfold flagBit
  by_cases h : n / 2 ^ k % 2 = 1
  · simp [h]
  · have h0 : n / 2 ^ k % 2 = 0 := by omega
    simp [h0]

/-- A clear flag bit. -/
theorem bit_false {n k : Nat} (h : flagBit n k = false) : n / 2 ^ k % 2 = 0 := by
  unfold flagBit at h
  have := of_decide_eq_false h
  omega

/-- A set flag bit. -/
theorem bit_true {n k : Nat} (h : flagBit n k = true) : n / 2 ^ k % 2 = 1 := by
  unfold flagBit at h
  exact of_decide_eq_true h

/-- The connect flags byte the printer writes for a CONNECT is the
    flags byte it was read from, when the fields carry the flags'
    bits and the bits the printer always clears are clear. -/
theorem flags_eq (flags : Nat) (c : Connect) (hf : flags < 256) (h0 : flags % 2 = 0)
    (hu : c.username.isSome = flagBit flags 7) (hp : c.password.isSome = flagBit flags 6)
    (hcs : c.cleanStart = flagBit flags 1)
    (hw : c.will.isSome = flagBit flags 2)
    (hws : ∀ w, c.will = some w → w.qos = (flags / 8) % 4 ∧ w.retain = flagBit flags 5)
    (hwn : c.will = none → (flags / 8) % 8 = 0) :
    connectFlags c = flags := by
  unfold connectFlags
  rw [hu, hp, hcs, if_bit flags 7 128, if_bit flags 6 64, if_bit flags 1 2]
  cases hwc : c.will with
  | none =>
    rw [hwc] at hw
    have h8 := hwn hwc
    have h2 := bit_false hw.symm
    dsimp only
    simp only [Nat.reducePow] at h2 ⊢
    omega
  | some w =>
    rw [hwc] at hw
    obtain ⟨hq, hr⟩ := hws w hwc
    have h2 := bit_true hw.symm
    dsimp only
    rw [hq, hr, if_bit flags 5 32]
    simp only [Nat.reducePow] at h2 ⊢
    omega

/-- What the filter list reader accepts is the printed form of a
    well formed filter list, and it reads to the end. -/
theorem readFiltersGo_inv : ∀ (fuel : Nat) (bs : List UInt8)
    (fs : List (List Char × SubOpts)) (r : List UInt8),
    readFiltersGo fuel bs = some (fs, r) → r = [] ∧ FiltersWF fs ∧ bs = printFilters fs := by
  intro fuel
  induction fuel with
  | zero =>
    intro bs fs r h
    rw [readFiltersGo] at h
    by_cases he : bs.isEmpty = true
    · rw [ite_eq_left he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have : bs = [] := List.isEmpty_iff.mp he
      subst this
      exact ⟨rfl, trivial, rfl⟩
    · rw [ite_eq_right he] at h
      cases h
  | succ fuel ih =>
    intro bs fs r h
    rw [readFiltersGo] at h
    by_cases he : bs.isEmpty = true
    · rw [ite_eq_left he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have : bs = [] := List.isEmpty_iff.mp he
      subst this
      exact ⟨rfl, trivial, rfl⟩
    · rw [ite_eq_right he] at h
      cases h1 : readStr bs with
      | none => rw [h1] at h; cases h
      | some fr =>
        obtain ⟨f, rest⟩ := fr
        cases rest with
        | nil => rw [h1] at h; cases h
        | cons ob r2 =>
          rw [h1] at h
          simp only at h
          cases h2 : readOptsByte ob.toNat with
          | none => rw [h2] at h; cases h
          | some o =>
            rw [h2] at h
            simp only at h
            by_cases hok : filterOK f o = true
            · rw [ite_eq_left hok] at h
              cases h3 : readFiltersGo fuel r2 with
              | none => rw [h3] at h; cases h
              | some qr =>
                obtain ⟨fs', r3⟩ := qr
                rw [h3] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hfs, hr⟩ := h
                subst hfs
                subst hr
                obtain ⟨hf, hbs⟩ := readStr_inv bs f (ob :: r2) h1
                obtain ⟨ho, hob⟩ := readOptsByte_inv ob.toNat o h2
                obtain ⟨hr3, hwf, hr2⟩ := ih r2 fs' r3 h3
                refine ⟨hr3, ⟨hf, ho, hok, hwf⟩, ?_⟩
                have hobe : printOptsByte o = ob := UInt8.toNat_inj.mp hob
                rw [hbs, hr2, ← hobe]
                simp [printFilters, printFilter]
            · rw [ite_eq_right hok] at h
              cases h

/-- The topic name check passes only a topic name it would print. -/
theorem checkTopic_inv {s t : List Char} (h : checkTopic s = some t) :
    t = s ∧ s ≠ [] ∧ '+' ∉ s ∧ '#' ∉ s := by
  unfold checkTopic at h
  by_cases hc : (s.isEmpty || s.any (fun c => decide (c = '+'))
      || s.any (fun c => decide (c = '#'))) = true
  · rw [ite_eq_left hc] at h
    cases h
  · rw [ite_eq_right hc] at h
    simp only [Option.some.injEq] at h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.isEmpty_eq_false_iff,
      List.any_eq_false, decide_eq_true_eq] at hc
    obtain ⟨⟨hne, hp⟩, hh⟩ := hc
    exact ⟨h.symm, hne, fun hm => hp _ hm rfl, fun hm => hh _ hm rfl⟩

/-- The wildcard check passes only a text with no wildcard. -/
theorem checkNoWildcards_inv {s t : List Char} (h : checkNoWildcards s = some t) :
    t = s ∧ '+' ∉ s ∧ '#' ∉ s := by
  unfold checkNoWildcards at h
  by_cases hc : (s.any (fun c => decide (c = '+'))
      || s.any (fun c => decide (c = '#'))) = true
  · rw [ite_eq_left hc] at h
    cases h
  · rw [ite_eq_right hc] at h
    simp only [Option.some.injEq] at h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true,
      List.any_eq_false, decide_eq_true_eq] at hc
    obtain ⟨hp, hh⟩ := hc
    exact ⟨h.symm, fun hm => hp _ hm rfl, fun hm => hh _ hm rfl⟩

/-- What the will step accepts: a will exactly when the will flag
    is set, with the flags' QoS and retain, well formed parts,
    and its printed form in front of the returned bytes. -/
theorem readWillPart_inv (flags : Nat) (r6 : List UInt8) (will : Option Will)
    (r7 : List UInt8) (h : readWillPart flags r6 = some (will, r7)) :
    will.isSome = flagBit flags 2 ∧ r6 = printWillPart will ++ r7
      ∧ (∀ w, will = some w → w.qos = (flags / 8) % 4 ∧ w.retain = flagBit flags 5
          ∧ PropsBlockWF .will w.props ∧ TopicWF w.topic ∧ BinWF w.payload) := by
  unfold readWillPart at h
  by_cases hw : flagBit flags 2 = true
  · rw [ite_eq_left hw] at h
    obtain ⟨⟨wprops, s1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨wtopic, s2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨wtopic', h3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨wpay, s3⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hwill, hr⟩ := h
    subst hwill
    subst hr
    obtain ⟨hps, hb1⟩ := readProps_inv .will r6 wprops s1 h1
    obtain ⟨hts, hb2⟩ := readStr_inv s1 wtopic s2 h2
    obtain ⟨ht, hne, hp, hh⟩ := checkTopic_inv h3
    subst ht
    obtain ⟨hpay, hb3⟩ := readBin_inv s2 wpay s3 h4
    refine ⟨by rw [hw]; rfl, ?_, ?_⟩
    · rw [hb1, hb2, hb3]
      show _ = (printProps wprops ++ (printStr wtopic' ++ printBin wpay)) ++ s3
      simp only [List.append_assoc]
    · intro w hw'
      simp only [Option.some.injEq] at hw'
      subst hw'
      exact ⟨rfl, rfl, hps, ⟨hts, hne, hp, hh⟩, hpay⟩
  · rw [ite_eq_right hw] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hwill, hr⟩ := h
    subst hwill
    subst hr
    refine ⟨?_, rfl, fun w hw' => by cases hw'⟩
    cases hb : flagBit flags 2
    · rfl
    · exact absurd hb hw

/-- What an optional string field step accepts. -/
theorem readOptStrField_inv (cond : Bool) (r : List UInt8) (u : Option (List Char))
    (r' : List UInt8) (h : readOptStrField cond r = some (u, r')) :
    u.isSome = cond ∧ (∀ s, u = some s → StrWF s) ∧ r = printOptStr u ++ r' := by
  unfold readOptStrField at h
  cases cond with
  | true =>
    rw [ite_eq_left rfl] at h
    obtain ⟨⟨s, r2⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hu, hr⟩ := h2
    subst hu
    subst hr
    obtain ⟨hs, hbs⟩ := readStr_inv r s r2 h1
    exact ⟨rfl, fun s' hs' => by simp only [Option.some.injEq] at hs'; subst hs'; exact hs, hbs⟩
  | false =>
    rw [ite_eq_right (by decide)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hu, hr⟩ := h
    subst hu
    subst hr
    exact ⟨rfl, fun s hs => (by cases hs), rfl⟩

/-- What an optional binary field step accepts. -/
theorem readOptBinField_inv (cond : Bool) (r : List UInt8) (u : Option (List UInt8))
    (r' : List UInt8) (h : readOptBinField cond r = some (u, r')) :
    u.isSome = cond ∧ (∀ d, u = some d → BinWF d) ∧ r = printOptBin u ++ r' := by
  unfold readOptBinField at h
  cases cond with
  | true =>
    rw [ite_eq_left rfl] at h
    obtain ⟨⟨d, r2⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨hu, hr⟩ := h2
    subst hu
    subst hr
    obtain ⟨hd, hbs⟩ := readBin_inv r d r2 h1
    exact ⟨rfl, fun d' hd' => by simp only [Option.some.injEq] at hd'; subst hd'; exact hd, hbs⟩
  | false =>
    rw [ite_eq_right (by decide)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hu, hr⟩ := h
    subst hu
    subst hr
    exact ⟨rfl, fun d hd => (by cases hd), rfl⟩

/-- What the CONNECT body reader accepts is the printed body of a
    well formed CONNECT. -/
theorem readConnectBody_inv (seg : List UInt8) (c : Connect)
    (h : readConnectBody seg = some c) : ConnectWF c ∧ seg = printConnectBody c := by
  unfold readConnectBody at h
  obtain ⟨⟨proto, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases hp : proto = ['M', 'Q', 'T', 'T']
  rotate_left
  · rw [ite_eq_right hp] at h; cases h
  rw [ite_eq_left hp] at h
  obtain ⟨⟨level, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases hl : level = 5
  rotate_left
  · rw [ite_eq_right hl] at h; cases h
  rw [ite_eq_left hl] at h
  obtain ⟨⟨flags, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases hf0 : flags % 2 = 0
  rotate_left
  · rw [ite_eq_right hf0] at h; cases h
  rw [ite_eq_left hf0] at h
  by_cases hq3 : (flags / 8) % 4 ≠ 3
  rotate_left
  · rw [ite_eq_right hq3] at h; cases h
  rw [ite_eq_left hq3] at h
  by_cases hwb : (flagBit flags 2 || decide ((flags / 8) % 8 = 0)) = true
  rotate_left
  · rw [ite_eq_right hwb] at h; cases h
  rw [ite_eq_left hwb] at h
  obtain ⟨⟨ka, r4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨props, r5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨cid, r6⟩, h6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨will, r7⟩, h7, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨username, r8⟩, h8, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨password, r9⟩, h9, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases he : r9.isEmpty = true
  rotate_left
  · rw [ite_eq_right he] at h; cases h
  rw [ite_eq_left he] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨_, hb1⟩ := readStr_inv seg proto r1 h1
  obtain ⟨_, hb2⟩ := readByte_inv r1 level r2 h2
  obtain ⟨hfl, hb3⟩ := readByte_inv r2 flags r3 h3
  obtain ⟨hka, hb4⟩ := readNat_inv 2 r3 ka r4 h4
  obtain ⟨hps, hb5⟩ := readProps_inv .connect r4 props r5 h5
  obtain ⟨hcid, hb6⟩ := readStr_inv r5 cid r6 h6
  obtain ⟨hws, hb7, hwf⟩ := readWillPart_inv flags r6 will r7 h7
  obtain ⟨hus, huwf, hb8⟩ := readOptStrField_inv _ r7 username r8 h8
  obtain ⟨hpw, hpwf, hb9⟩ := readOptBinField_inv _ r8 password r9 h9
  have hr9 : r9 = [] := List.isEmpty_iff.mp he
  have hflags : connectFlags
      ⟨flagBit flags 1, ka, props, cid, will, username, password⟩ = flags := by
    refine flags_eq flags _ hfl hf0 hus hpw rfl hws
      (fun w hw => ⟨(hwf w hw).1, (hwf w hw).2.1⟩) ?_
    intro hn
    have hn' : will = none := hn
    have h2f : flagBit flags 2 = false := by
      rw [← hws, hn']; rfl
    rw [h2f] at hwb
    simpa using hwb
  refine ⟨⟨by simpa using hka, hps, hcid, ?_, huwf, hpwf⟩, ?_⟩
  · intro w hw
    obtain ⟨hq, _, hwp, hwt, hwpay⟩ := hwf w hw
    exact ⟨by rw [hq]; omega, hwp, hwt, hwpay⟩
  · subst hr9
    subst hb9
    subst hb8
    subst hb7
    subst hb6
    subst hb5
    subst hb4
    subst hb3
    subst hb2
    subst hb1
    subst hp
    subst hl
    show _ = printStr ['M', 'Q', 'T', 'T'] ++ ([5, (connectFlags
      ⟨flagBit flags 1, ka, props, cid, will, username, password⟩).toUInt8]
      ++ (writeBE 2 ka ++ (printProps props ++ (printStr cid ++ (printWillPart will
      ++ (printOptStr username ++ printOptBin password))))))
    rw [hflags]
    simp only [List.cons_append, List.nil_append, List.append_nil]
    rfl


/-- What the packet identifier step accepts: nothing at QoS 0, a
    printed nonzero identifier at QoS 1 and 2. -/
theorem readPacketId_inv (flags : Nat) (r1 : List UInt8) (pid : Option Nat)
    (r2 : List UInt8) (h : readPacketId flags r1 = some (pid, r2)) :
    r1 = printIdOpt pid ++ r2
      ∧ ((flags / 2) % 4 = 0 → pid = none)
      ∧ ((flags / 2) % 4 ≠ 0 → ∃ id, pid = some id ∧ 1 ≤ id ∧ id < 65536) := by
  unfold readPacketId at h
  by_cases hq : (flags / 2) % 4 = 0
  · rw [ite_eq_left hq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact ⟨rfl, fun _ => rfl, fun hn => absurd hq hn⟩
  · rw [ite_eq_right hq] at h
    obtain ⟨⟨id, r⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    by_cases hid : id ≠ 0
    · rw [ite_eq_left hid] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h2, h3⟩ := h
      subst h2
      subst h3
      obtain ⟨hlt, hbs⟩ := readNat_inv 2 r1 id r h1
      exact ⟨hbs, fun hz => absurd hz hq,
        fun _ => ⟨id, rfl, by omega, by simpa using hlt⟩⟩
    · rw [ite_eq_right hid] at h
      cases h

/-- What the PUBLISH body reader accepts, under flags the
    dispatcher lets through, is the printed body of a well formed
    PUBLISH whose header is the flags' header byte. -/
theorem readPublishBody_inv (flags : Nat) (seg : List UInt8) (p : Publish)
    (hf : flags < 16) (hq3 : ¬ (flags / 2) % 4 = 3)
    (hdup : ¬ ((flags / 2) % 4 = 0 ∧ flagBit flags 3 = true))
    (h : readPublishBody flags seg = some p) :
    PublishWF p ∧ seg = printPublishBody p ∧ publishHeader p = 48 + flags := by
  unfold readPublishBody at h
  obtain ⟨⟨topic, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨topic', h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨pid, r2⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨props, payload⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases hc : (topic'.isEmpty && !hasTopicAlias props) = true
  · rw [ite_eq_left hc] at h
    cases h
  rw [ite_eq_right hc] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hstr, hb1⟩ := readStr_inv seg topic r1 h1
  obtain ⟨ht, hp, hh⟩ := checkNoWildcards_inv h2
  subst ht
  obtain ⟨hb2, hq0, hqn⟩ := readPacketId_inv flags r1 pid r2 h3
  obtain ⟨hps, hb3⟩ := readProps_inv .publish r2 props payload h4
  refine ⟨⟨by dsimp only; omega, ⟨hstr, hp, hh, ?_⟩, ?_, ?_, hps, ?_⟩, ?_, ?_⟩
  · intro hnil
    subst hnil
    cases ha : hasTopicAlias props
    · rw [ha] at hc; exact absurd rfl hc
    · rfl
  · intro id hid
    dsimp only at hid ⊢
    by_cases hz : (flags / 2) % 4 = 0
    · rw [hq0 hz] at hid; cases hid
    · obtain ⟨id', hid', h1', h2'⟩ := hqn hz
      rw [hid'] at hid
      simp only [Option.some.injEq] at hid
      subst hid
      exact ⟨h1', h2', by omega⟩
  · intro hn
    dsimp only at hn ⊢
    by_cases hz : (flags / 2) % 4 = 0
    · exact hz
    · obtain ⟨id', hid', _, _⟩ := hqn hz
      rw [hid'] at hn; cases hn
  · intro hz
    dsimp only at hz ⊢
    cases hb : flagBit flags 3
    · rfl
    · exact absurd ⟨hz, hb⟩ hdup
  · rw [hb1, hb2, hb3]
    rfl
  · unfold publishHeader
    dsimp only
    rw [if_bit flags 3 8, if_bit flags 0 1]
    simp only [Nat.reducePow]
    omega

/-- What the SUBSCRIBE body reader accepts is the printed body of
    a well formed SUBSCRIBE. -/
theorem readSubscribeBody_inv (seg : List UInt8) (p : Packet)
    (h : readSubscribeBody seg = some p) :
    (∃ id ps fs, p = .subscribe id ps fs) ∧ PacketFieldsWF p ∧ seg = bodyOf p := by
  rw [readSubscribeBody_step] at h
  obtain ⟨⟨id, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases hid : id ≠ 0
  · rw [ite_eq_left hid] at h
    obtain ⟨⟨props, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨fs, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    by_cases hc : (r3.isEmpty && !fs.isEmpty) = true
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hlt, hb1⟩ := readNat_inv 2 seg id r1 h1
      obtain ⟨hps, hb2⟩ := readProps_inv .subscribe r1 props r2 h2
      obtain ⟨hr3, hfs, hb3⟩ := readFiltersGo_inv _ r2 fs r3 h3
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      refine ⟨⟨id, props, fs, rfl⟩, ⟨by omega, by simpa using hlt, hps, ?_, hfs⟩, ?_⟩
      · intro hn
        rw [hn] at hc
        exact absurd hc.2 (by decide)
      · rw [hb1, hb2, hb3]
        rfl
    · rw [ite_eq_right hc] at h
      cases h
  · rw [ite_eq_right hid] at h
    cases h

/-- Reason codes read as numbers, written back, are the bytes. -/
theorem map_toNat_toUInt8 (bs : List UInt8) :
    (bs.map UInt8.toNat).map Nat.toUInt8 = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons]
    rw [byte_eq_toUInt8]
    exact congrArg _ ih

/-- What the SUBACK body reader accepts is the printed body of a
    well formed SUBACK. -/
theorem readSubackBody_inv (seg : List UInt8) (p : Packet)
    (h : readSubackBody seg = some p) :
    (∃ id ps rs, p = .suback id ps rs) ∧ PacketFieldsWF p ∧ seg = bodyOf p := by
  rw [readSubackBody_step] at h
  obtain ⟨⟨id, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  by_cases hid : id ≠ 0
  · rw [ite_eq_left hid] at h
    obtain ⟨⟨props, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    by_cases hc : (!r2.isEmpty) = true
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hlt, hb1⟩ := readNat_inv 2 seg id r1 h1
      obtain ⟨hps, hb2⟩ := readProps_inv .suback r1 props r2 h2
      refine ⟨⟨id, props, _, rfl⟩, ⟨by omega, by simpa using hlt, hps, ?_, ?_⟩, ?_⟩
      · intro hn
        cases r2 with
        | nil => exact absurd hc (by decide)
        | cons a t => cases hn
      · intro r hr
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hr
        rw [← hb]
        exact UInt8.toNat_lt b
      · rw [hb1, hb2]
        show _ = writeBE 2 id ++ (printProps props ++ (r2.map UInt8.toNat).map Nat.toUInt8)
        rw [map_toNat_toUInt8]
    · rw [ite_eq_right hc] at h
      cases h
  · rw [ite_eq_right hid] at h
    cases h

/-- What the DISCONNECT body reader accepts is the printed body of
    a well formed DISCONNECT, in the form it came. -/
theorem readDisconnectBody_inv (seg : List UInt8) (p : Packet)
    (h : readDisconnectBody seg = some p) :
    (∃ x, p = .disconnect x) ∧ PacketFieldsWF p ∧ seg = bodyOf p := by
  cases seg with
  | nil =>
    simp only [readDisconnectBody, Option.some.injEq] at h
    subst h
    exact ⟨⟨_, rfl⟩, trivial, rfl⟩
  | cons rc r1 =>
    unfold readDisconnectBody at h
    dsimp only at h
    by_cases he : r1.isEmpty = true
    · rw [ite_eq_left he] at h
      simp only [Option.some.injEq] at h
      subst h
      have : r1 = [] := List.isEmpty_iff.mp he
      subst this
      refine ⟨⟨_, rfl⟩, UInt8.toNat_lt rc, ?_⟩
      show _ = [rc.toNat.toUInt8]
      rw [byte_eq_toUInt8]
    · rw [ite_eq_right he] at h
      obtain ⟨⟨props, r2⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
      simp only at h
      by_cases he2 : r2.isEmpty = true
      · rw [ite_eq_left he2] at h
        cases h
        have : r2 = [] := List.isEmpty_iff.mp he2
        subst this
        obtain ⟨hps, hb⟩ := readProps_inv .disconnect r1 props [] h1
        refine ⟨⟨_, rfl⟩, ⟨UInt8.toNat_lt rc, hps⟩, ?_⟩
        show _ = [rc.toNat.toUInt8] ++ printProps props
        rw [byte_eq_toUInt8, hb, List.append_nil]
        rfl
      · rw [ite_eq_right he2] at h
        cases h


/-- A header byte equal in value to a number is that number's
    byte. -/
theorem byte_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.toNat_inj.mp h

/-- What the body dispatcher accepts, under a header byte, is the
    printed body of a well formed packet whose header is that
    byte. -/
theorem parseBody_inv (b : UInt8) (seg : List UInt8) (p : Packet)
    (h : parseBody (b.toNat / 16) (b.toNat % 16) seg = some p) :
    PacketFieldsWF p ∧ seg = bodyOf p ∧ headerOf p = b := by
  have hb := UInt8.toNat_lt b
  have hf : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize htyp : b.toNat / 16 = typ at h
  generalize hfl : b.toNat % 16 = flags at h hf
  have hbv : b.toNat = 16 * typ + flags := by omega
  unfold parseBody at h
  split at h
  · by_cases h0 : flags = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨c, h1, h2⟩ := Option.map_eq_some_iff.mp h
      subst h2
      obtain ⟨hwf, hseg⟩ := readConnectBody_inv seg c h1
      exact ⟨hwf, hseg, byte_eq_of_toNat (by rw [hbv, h0]; rfl)⟩
    · rw [ite_eq_right h0] at h
      cases h
  · by_cases hq3 : (flags / 2) % 4 = 3
    · rw [ite_eq_left hq3] at h
      cases h
    rw [ite_eq_right hq3] at h
    by_cases hd : (flags / 2) % 4 = 0 ∧ flagBit flags 3 = true
    · rw [ite_eq_left hd] at h
      cases h
    rw [ite_eq_right hd] at h
    obtain ⟨q, h1, h2⟩ := Option.map_eq_some_iff.mp h
    subst h2
    obtain ⟨hwf, hseg, hhead⟩ := readPublishBody_inv flags seg q hf hq3 hd h1
    refine ⟨hwf, hseg, byte_eq_of_toNat ?_⟩
    show (publishHeader q).toUInt8.toNat = b.toNat
    rw [hhead, toNat_toUInt8 (by omega)]
    omega
  · by_cases h2 : flags = 2
    · rw [ite_eq_left h2] at h
      obtain ⟨⟨id, ps, fs, hp⟩, hwf, hseg⟩ := readSubscribeBody_inv seg p h
      subst hp
      exact ⟨hwf, hseg, byte_eq_of_toNat (by rw [hbv, h2]; rfl)⟩
    · rw [ite_eq_right h2] at h
      cases h
  · by_cases h0 : flags = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨⟨id, ps, rs, hp⟩, hwf, hseg⟩ := readSubackBody_inv seg p h
      subst hp
      exact ⟨hwf, hseg, byte_eq_of_toNat (by rw [hbv, h0]; rfl)⟩
    · rw [ite_eq_right h0] at h
      cases h
  · by_cases hc : (decide (flags = 0) && seg.isEmpty) = true
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨h0, he⟩ := hc
      exact ⟨trivial, List.isEmpty_iff.mp he, byte_eq_of_toNat (by rw [hbv, h0]; rfl)⟩
    · rw [ite_eq_right hc] at h
      cases h
  · by_cases hc : (decide (flags = 0) && seg.isEmpty) = true
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨h0, he⟩ := hc
      exact ⟨trivial, List.isEmpty_iff.mp he, byte_eq_of_toNat (by rw [hbv, h0]; rfl)⟩
    · rw [ite_eq_right hc] at h
      cases h
  · by_cases h0 : flags = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨⟨x, hp⟩, hwf, hseg⟩ := readDisconnectBody_inv seg p h
      subst hp
      exact ⟨hwf, hseg, byte_eq_of_toNat (by rw [hbv, h0]; rfl)⟩
    · rw [ite_eq_right h0] at h
      cases h
  · cases h

/-- What the stream reader accepts is the printed form of a well
    formed packet, followed by the bytes it returns. -/
theorem parsePacket_inv (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) : PacketWF p ∧ bs = print p ++ r := by
  cases bs with
  | nil => exact absurd h (by simp [parsePacket])
  | cons b r0 =>
    cases hd : decVBI r0 with
    | none =>
      have : parsePacket (b :: r0) = none := by
        show (decVBI r0).bind _ = none
        rw [hd]; rfl
      rw [this] at h
      exact absurd h (by simp)
    | some lr =>
      obtain ⟨len, r1⟩ := lr
      obtain ⟨hlen, hr0⟩ := decVBI_canonical r0 len r1 hd
      cases hb : readBytes len r1 with
      | none =>
        have : parsePacket (b :: r0) = none := by
          show (decVBI r0).bind _ = none
          rw [hd]
          show (readBytes len r1).bind _ = none
          rw [hb]; rfl
        rw [this] at h
        exact absurd h (by simp)
      | some sr =>
        obtain ⟨seg, r2⟩ := sr
        obtain ⟨hsl, hr1⟩ := readBytes_inv len r1 seg r2 hb
        have e : parsePacket (b :: r0)
            = (parseBody (b.toNat / 16) (b.toNat % 16) seg).bind
                (fun q => some (q, r2)) := by
          show (decVBI r0).bind _ = _
          rw [hd]
          show (readBytes len r1).bind _ = _
          rw [hb]
          rfl
        rw [e] at h
        cases hp : parseBody (b.toNat / 16) (b.toNat % 16) seg with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some q =>
          rw [hp] at h
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hq, hr⟩ := h
          subst hq
          subst hr
          obtain ⟨hwf, hseg, hhead⟩ := parseBody_inv b seg q hp
          refine ⟨⟨hwf, by rw [← hseg, hsl]; exact hlen⟩, ?_⟩
          rw [hr0, hr1, ← hsl, hseg, ← hhead]
          show _ = (headerOf q :: (printVBI (bodyOf q).length ++ bodyOf q)) ++ r2
          simp only [List.cons_append, List.append_assoc]

/-- What the whole input reader accepts is exactly the printed
    form of a well formed packet. -/
theorem parse_inv (bs : List UInt8) (p : Packet) (h : parse bs = some p) :
    PacketWF p ∧ print p = bs := by
  unfold parse at h
  cases hp : parsePacket bs with
  | none => rw [hp] at h; cases h
  | some pr =>
    obtain ⟨q, r⟩ := pr
    rw [hp] at h
    cases r with
    | nil =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hwf, hbs⟩ := parsePacket_inv bs q [] hp
      exact ⟨hwf, by rw [hbs, List.append_nil]⟩
    | cons x xs => cases h

end Mqtt.Proofs
