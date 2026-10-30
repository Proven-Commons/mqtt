/-
  The round trip proofs for the MQTT packet codec: reading what
  the printer wrote gives the packet back.

  The main claim is `Mqtt.Proofs.parse_print`: for a well
  formed packet `p`, `parse (print p) = some p`. It is built
  from one lemma per field reader, each in the shape "reading
  the printed field, with any bytes after it left in place,
  gives the field and leaves the bytes after it". Property
  blocks and filter lists read to the end of their bytes, so
  their lemmas are stated on the printed bytes exactly.
-/

import Mqtt
import Mqtt.Proofs.Utf8

namespace Mqtt.Proofs

open Mqtt

/-- A number below 256 written as a byte reads back as itself. -/
theorem toNat_toUInt8 {k : Nat} (h : k < 256) : k.toUInt8.toNat = k :=
  Mqtt.Utf8.Proofs.toNat_toUInt8 h

/-! ## The byte readers on writings -/

/-- A big endian writing reads back: at every width, the number
    written is the number read, and the bytes after the writing
    are left alone. -/
theorem readNat_writeBE : ∀ (k n : Nat) (rest : List UInt8),
    n < 256 ^ k → readNat k (writeBE k n ++ rest) = some (n, rest) := by
  intro k
  induction k with
  | zero =>
    intro n rest hn
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    rw [hn0]
    rfl
  | succ k ih =>
    intro n rest hn
    have hP : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have hlt : n / 256 ^ k < 256 := by
      rw [Nat.pow_succ] at hn
      exact Nat.div_lt_of_lt_mul hn
    have hd : ((n / 256 ^ k) % 256).toUInt8.toNat = n / 256 ^ k := by
      have h1 : ((n / 256 ^ k) % 256).toUInt8.toNat = (n / 256 ^ k) % 256 :=
        UInt8.toNat_ofNat_of_lt (Nat.mod_lt _ (by decide : 0 < 256))
      rw [h1, Nat.mod_eq_of_lt hlt]
    rw [writeBE_succ, List.cons_append, readNat_succ_cons,
      ih (n % 256 ^ k) rest (Nat.mod_lt _ hP), hd]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    · trivial

/-- A byte run reads back whole: taking the front of a list that
    starts with the run gives the run, and leaves the rest. -/
theorem readBytes_append : ∀ (n : Nat) (bs rest : List UInt8),
    bs.length = n → readBytes n (bs ++ rest) = some (bs, rest) := by
  intro n bs rest h
  unfold readBytes
  rw [ite_eq_left (by simp [List.length_append, h] : (bs ++ rest).length ≥ n),
    ← h, List.take_left, List.drop_left]

/-! ## The variable byte integer -/

/-- A variable byte integer writing is never empty. -/
theorem printVBI_pos : ∀ (n : Nat), 0 < (printVBI n).length := by
  intro n
  rw [printVBI_def]
  by_cases h : n < 128
  · rw [ite_eq_left h]; simp
  · rw [ite_eq_right h]; simp

/-- Reading a printed variable byte integer, with the counting
    form of the reader: with at most `k + 1` bytes to spend and
    a value that fits in `k + 1` groups, the reader returns the
    value and leaves the bytes after the writing. Induction on
    `k`: a value below 128 is one byte, and a larger value is
    its low group, marked as continued, in front of the writing
    of the rest of the value, which is not 0. -/
theorem decVBIGo_printVBI : ∀ (k : Nat) (n : Nat) (rest : List UInt8),
    n < 128 ^ (k + 1) →
    decVBIGo (k + 1) (printVBI n ++ rest) = some (n, rest) := by
  intro k
  induction k with
  | zero =>
    intro n rest hn
    rw [Nat.pow_one] at hn
    rw [printVBI_def, ite_eq_left hn]
    show decVBIGo 1 (n.toUInt8 :: rest) = some (n, rest)
    rw [decVBIGo, toNat_toUInt8 (by omega : n < 256), ite_eq_left hn]
  | succ k ih =>
    intro n rest hn
    by_cases h1 : n < 128
    · rw [printVBI_def, ite_eq_left h1]
      show decVBIGo (k + 2) (n.toUInt8 :: rest) = some (n, rest)
      rw [decVBIGo, toNat_toUInt8 (by omega : n < 256), ite_eq_left h1]
    · rw [printVBI_def, ite_eq_right h1]
      show decVBIGo (k + 2) ((128 + n % 128).toUInt8 :: (printVBI (n / 128) ++ rest))
        = some (n, rest)
      have hdiv : n / 128 < 128 ^ (k + 1) := by
        rw [Nat.pow_succ] at hn
        omega
      rw [decVBIGo, toNat_toUInt8 (by omega : 128 + n % 128 < 256),
        ite_eq_right (by omega : ¬ (128 + n % 128 < 128)), ih (n / 128) rest hdiv]
      simp only []
      rw [ite_eq_right (by omega : ¬ (n / 128 = 0))]
      have key : 128 + n % 128 - 128 + 128 * (n / 128) = n := by omega
      rw [key]

/-- Reading a printed variable byte integer gives the number
    back: any number below 2^28, the most four bytes carry. -/
theorem decVBI_printVBI (n : Nat) (rest : List UInt8) (hn : n < 268435456) :
    decVBI (printVBI n ++ rest) = some (n, rest) :=
  decVBIGo_printVBI 3 n rest (by
    have e : (128 : Nat) ^ (3 + 1) = 268435456 := by decide
    rw [e]; exact hn)

/-- A byte read as a number and written back is the same
    byte. -/
theorem byte_eq_toUInt8 (b : UInt8) : b.toNat.toUInt8 = b := UInt8.ofNat_toNat

/-- What the counting reader accepts is a printed writing: with
    `k` bytes to spend, an accepted value fits in `k` groups,
    and the bytes it read are exactly the printer's writing of
    that value, with the returned bytes after them. Induction
    on `k`: one byte below 128 is the writing of its value; a
    continuation byte in front of the writing of a nonzero rest
    is the writing of the whole value. -/
theorem decVBIGo_canonical : ∀ (k : Nat) (bs : List UInt8) (n : Nat) (r : List UInt8),
    decVBIGo k bs = some (n, r) → n < 128 ^ k ∧ bs = printVBI n ++ r := by
  intro k
  induction k with
  | zero =>
    intro bs n r h
    rw [decVBIGo] at h
    exact absurd h (by simp)
  | succ k ih =>
    intro bs n r h
    cases bs with
    | nil =>
      rw [decVBIGo] at h
      exact absurd h (by simp)
    | cons b bs =>
      have hb256 : b.toNat < 256 := UInt8.toNat_lt b
      have hpow : 1 ≤ 128 ^ k := Nat.pow_pos (by decide)
      rw [decVBIGo] at h
      by_cases hb : b.toNat < 128
      · rw [ite_eq_left hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hn, hr⟩ := h
        subst hn
        subst hr
        refine ⟨?_, ?_⟩
        · rw [Nat.pow_succ]; omega
        · rw [printVBI_def, ite_eq_left hb, byte_eq_toUInt8]
          rfl
      · rw [ite_eq_right hb] at h
        cases hk : decVBIGo k bs with
        | none =>
          rw [hk] at h
          exact absurd h (by simp)
        | some vr =>
          obtain ⟨v, r'⟩ := vr
          rw [hk] at h
          simp only [] at h
          by_cases hv : v = 0
          · rw [ite_eq_left hv] at h
            exact absurd h (by simp)
          · rw [ite_eq_right hv] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hn, hr⟩ := h
            subst hn
            subst hr
            obtain ⟨hvb, hbs⟩ := ih bs v r' hk
            refine ⟨?_, ?_⟩
            · rw [Nat.pow_succ]
              have : 128 * v ≤ 128 * (128 ^ k - 1) := Nat.mul_le_mul_left _ (by omega)
              have e2 : 128 * (128 ^ k - 1) = 128 ^ k * 128 - 128 := by
                rw [Nat.mul_sub, Nat.mul_comm]
              omega
            · rw [hbs, printVBI_def (b.toNat - 128 + 128 * v),
                ite_eq_right (by omega : ¬ (b.toNat - 128 + 128 * v < 128))]
              have e1 : (b.toNat - 128 + 128 * v) % 128 = b.toNat - 128 := by omega
              have e2 : (b.toNat - 128 + 128 * v) / 128 = v := by omega
              rw [e1, e2, show 128 + (b.toNat - 128) = b.toNat by omega, byte_eq_toUInt8]
              rfl

/-- What the variable byte integer reader accepts is the
    printer's writing of the value it returns, the shortest
    one, with the returned bytes after it; and the value is
    below 2^28. So no longer writing of a value is accepted. -/
theorem decVBI_canonical (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) : n < 268435456 ∧ bs = printVBI n ++ r := by
  have e : (128 : Nat) ^ 4 = 268435456 := by decide
  rw [← e]
  exact decVBIGo_canonical 4 bs n r h

/-- The four byte cap: a variable byte integer whose first four
    bytes all carry a continuation mark is refused, whatever
    follows. The value would need a fifth byte, and the
    standard allows four (section 1.5.5). A reader with a
    higher cap, or none, fails this statement on
    `[128, 128, 128, 128, 1]`. -/
theorem decVBI_four_byte_cap (b0 b1 b2 b3 : UInt8) (rest : List UInt8)
    (h0 : 128 ≤ b0.toNat) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat)
    (h3 : 128 ≤ b3.toNat) :
    decVBI (b0 :: b1 :: b2 :: b3 :: rest) = none := by
  unfold decVBI
  rw [decVBIGo, ite_eq_right (by omega), decVBIGo, ite_eq_right (by omega),
    decVBIGo, ite_eq_right (by omega), decVBIGo, ite_eq_right (by omega), decVBIGo]

/-- The four byte cap on the remaining length: a packet whose
    remaining length has a continuation mark on each of its
    first four bytes is refused, by the stream reader and by
    the whole input reader, whatever the header byte and
    whatever follows. -/
theorem parsePacket_four_byte_cap (h b0 b1 b2 b3 : UInt8) (rest : List UInt8)
    (h0 : 128 ≤ b0.toNat) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat)
    (h3 : 128 ≤ b3.toNat) :
    parsePacket (h :: b0 :: b1 :: b2 :: b3 :: rest) = none
      ∧ parse (h :: b0 :: b1 :: b2 :: b3 :: rest) = none := by
  have e : parsePacket (h :: b0 :: b1 :: b2 :: b3 :: rest) = none := by
    show (decVBI (b0 :: b1 :: b2 :: b3 :: rest)).bind _ = none
    rw [decVBI_four_byte_cap b0 b1 b2 b3 rest h0 h1 h2 h3]
    rfl
  refine ⟨e, ?_⟩
  unfold parse
  rw [e]

/-- What the byte cut takes is exactly `n` bytes from the front,
    and the returned bytes are the ones after them. -/
theorem readBytes_inv (n : Nat) (bs seg r : List UInt8)
    (h : readBytes n bs = some (seg, r)) : seg.length = n ∧ bs = seg ++ r := by
  unfold readBytes at h
  by_cases hl : bs.length ≥ n
  · rw [ite_eq_left hl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    refine ⟨?_, (List.take_append_drop n bs).symm⟩
    rw [List.length_take]
    omega
  · rw [ite_eq_right hl] at h
    exact absurd h (by simp)

/-- The frame of an accepted packet: every packet the stream
    reader takes is a header byte, the shortest writing of the
    body's length, and that many body bytes, all standing in
    the input; the bytes it returns are exactly the ones after
    them. So the reader never takes a byte the input does not
    hold, and refuses a remaining length written in more bytes
    than it needs. -/
theorem parsePacket_frame (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) :
    ∃ (b : UInt8) (body : List UInt8), body.length < 268435456
      ∧ bs = b :: (printVBI body.length ++ body) ++ r := by
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
        have hr : r2 = r := by
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
            exact h.2
        subst hr
        refine ⟨b, seg, by omega, ?_⟩
        rw [hr0, hr1, hsl]
        simp

/-! ## Step lemmas

  The readers written with `do` notation are unfolded one step
  at a time through these equations, each proved by `rfl`, so
  the proofs below can rewrite one field at a time. -/

/-- One step of the string reader, stated for rewriting. -/
theorem readStr_step (bs : List UInt8) :
    readStr bs = (readNat 2 bs).bind fun (len, r1) =>
      (readBytes len r1).bind fun (chunk, r2) =>
      ((Utf8.decode chunk).bind checkChars).bind fun s => some (s, r2) := rfl

/-- One step of the binary reader, stated for rewriting. -/
theorem readBin_step (bs : List UInt8) :
    readBin bs = (readNat 2 bs).bind fun (len, r1) => readBytes len r1 := rfl

/-- One step of the string pair value reader, stated for
    rewriting. -/
theorem readPropVal_pair_step (bs : List UInt8) :
    readPropVal .utf8Pair bs = (readStr bs).bind fun (k, r1) =>
      (readStr r1).bind fun (v, r2) => some (.utf8Pair k v, r2) := rfl

/-- One step of the property reader, stated for rewriting. -/
theorem readEntry_step (s : PropSet) (seen : List Nat) (bs : List UInt8) :
    readEntry s seen bs = (decVBI bs).bind fun (id, r1) =>
      if (allowedOf s).contains id && (repeatableIn s id || !seen.contains id) then
        match propTypeOf id with
        | none => none
        | some t => (readPropVal t r1).bind fun (v, r2) =>
          if propValOK id v then some (⟨id, v⟩, r2) else none
      else none := rfl

/-- One step of the property block reader, stated for
    rewriting. -/
theorem readProps_step (s : PropSet) (bs : List UInt8) :
    readProps s bs = (decVBI bs).bind fun (len, r1) =>
      (readBytes len r1).bind fun (seg, r2) =>
      (readEntries s seg).bind fun ps => some (ps, r2) := rfl

/-! ## Strings and binary data -/

/-- The null character check passes on a well formed string. -/
theorem hasNul_false {s : List Char} (h : '\u0000' ∉ s) : hasNul s = false := by
  simp only [hasNul, List.any_eq_false]
  intro c hc hcc
  have hceq : c = '\u0000' := of_decide_eq_true hcc
  subst hceq
  exact h hc

/-- The character check passes on a well formed string. -/
theorem checkChars_of_wf {s : List Char} (h : StrWF s) : checkChars s = some s := by
  simp [checkChars, hasNul_false h.1]

/-- A printed string field reads back: the string, with the
    bytes after the field left in place. -/
theorem readStr_printStr (s : List Char) (rest : List UInt8) (h : StrWF s) :
    readStr (printStr s ++ rest) = some (s, rest) := by
  have hlen : (Utf8.encode s).length < 256 ^ 2 := by
    have h2 := h.2
    have e : (256 : Nat) ^ 2 = 65536 := by decide
    rw [e]
    omega
  rw [readStr_step, printStr, List.append_assoc, readNat_writeBE 2 _ _ hlen]
  simp only [Option.bind_some]
  rw [readBytes_append _ _ _ rfl]
  simp only [Option.bind_some]
  rw [Mqtt.Utf8.Proofs.decode_encode]
  simp only [Option.bind_some]
  rw [checkChars_of_wf h]
  simp only [Option.bind_some]

/-- A printed binary field reads back: the bytes, with the
    bytes after the field left in place. -/
theorem readBin_printBin (bs : List UInt8) (rest : List UInt8) (h : BinWF bs) :
    readBin (printBin bs ++ rest) = some (bs, rest) := by
  have hlen : bs.length < 256 ^ 2 := by
    have h2 : bs.length ≤ 65535 := h
    have e : (256 : Nat) ^ 2 = 65536 := by decide
    rw [e]
    omega
  rw [readBin_step, printBin, List.append_assoc, readNat_writeBE 2 _ _ hlen]
  simp only [Option.bind_some]
  rw [readBytes_append _ _ _ rfl]

/-! ## Properties -/

/-- An identifier with a table entry is below 2^28. -/
theorem propTypeOf_id_lt {id : Nat} {t : PropType}
    (h : propTypeOf id = some t) : id < 268435456 := by
  unfold propTypeOf at h
  split at h <;> simp_all <;> omega

/-- A printed property value reads back, at the type the table
    gives it. -/
theorem readPropVal_printPropVal (v : PropVal) (rest : List UInt8) (h : ValWF v) :
    readPropVal (valType v) (printPropVal v ++ rest) = some (v, rest) := by
  cases v with
  | byte n =>
    have hn : n < 256 := h
    simp only [valType, printPropVal, readPropVal]
    rw [List.cons_append, List.nil_append, readNat_succ_cons,
      show readNat 0 rest = some (0, rest) from rfl, Option.map_some,
      Option.map_some, toNat_toUInt8 hn]
    simp
  | twoByte n =>
    simp only [valType, printPropVal, readPropVal]
    rw [readNat_writeBE 2 n rest (by
      have e : (256 : Nat) ^ 2 = 65536 := by decide
      rw [e]; exact h)]
    rfl
  | fourByte n =>
    simp only [valType, printPropVal, readPropVal]
    rw [readNat_writeBE 4 n rest (by
      have e : (256 : Nat) ^ 4 = 4294967296 := by decide
      rw [e]; exact h)]
    rfl
  | varByte n =>
    simp only [valType, printPropVal, readPropVal]
    rw [decVBI_printVBI n rest h]
    rfl
  | utf8 s =>
    simp only [valType, printPropVal, readPropVal]
    rw [readStr_printStr s rest h]
    rfl
  | utf8Pair k v =>
    obtain ⟨hk, hv⟩ := h
    show readPropVal .utf8Pair ((printStr k ++ printStr v) ++ rest)
        = some (.utf8Pair k v, rest)
    rw [readPropVal_pair_step, List.append_assoc, readStr_printStr k _ hk]
    simp only [Option.bind_some]
    rw [readStr_printStr v rest hv]
    simp only [Option.bind_some]
  | binary bs =>
    simp only [valType, printPropVal, readPropVal]
    rw [readBin_printBin bs rest h]
    rfl

/-- A printed property reads back, when the property stands in
    the block it is read for: its identifier is allowed there,
    its value matches the table's type, the value is well
    formed, and the block's repeat rule is respected. -/
theorem readEntry_printProperty (s : PropSet) (seen : List Nat) (p : Property)
    (rest : List UInt8)
    (hid : p.id ∈ allowedOf s) (hty : propTypeOf p.id = some (valType p.val))
    (hval : ValWF p.val) (hok : propValOK p.id p.val = true)
    (hrep : repeatableIn s p.id = true ∨ p.id ∉ seen) :
    readEntry s seen (printProperty p ++ rest) = some (p, rest) := by
  have hc : (allowedOf s).contains p.id = true := List.contains_iff_mem.mpr hid
  have hr : (repeatableIn s p.id || !seen.contains p.id) = true := by
    cases hrep with
    | inl h => rw [h]; rfl
    | inr h =>
      have h2 : seen.contains p.id = false := by
        cases hseen : seen.contains p.id with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.mp hseen) h
      rw [h2]
      cases repeatableIn s p.id <;> rfl
  rw [readEntry_step, printProperty, List.append_assoc,
    decVBI_printVBI p.id _ (propTypeOf_id_lt hty)]
  simp only [Option.bind_some]
  rw [ite_eq_left (by rw [hc, hr]; rfl), hty]
  simp only []
  rw [readPropVal_printPropVal p.val rest hval]
  simp only [Option.bind_some]
  rw [ite_eq_left hok]

/-- A printed property list reads back whole, when the list is
    well formed for its block: the reader spends one fuel per
    property and each property takes at least a byte, so the
    list's own length is fuel enough. -/
theorem readEntriesGo_printPropsList : ∀ (fuel : Nat) (s : PropSet)
    (seen : List Nat) (ps : List Property),
    ps.length ≤ fuel → PropsWF s seen ps →
    readEntriesGo fuel s seen (printPropsList ps) = some (ps, []) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s seen ps hlen _
    have hps : ps = [] := by
      cases ps with
      | nil => rfl
      | cons p ps' => simp at hlen
    rw [hps]
    rfl
  | succ fuel ih =>
    intro s seen ps hlen hwf
    cases ps with
    | nil => rfl
    | cons p ps' =>
      have hne : ¬ (printProperty p ++ printPropsList ps').isEmpty := by
        have h1 : 0 < (printVBI p.id).length := printVBI_pos p.id
        intro hcon
        rw [List.isEmpty_iff] at hcon
        have h3 : printProperty p = [] := (List.append_eq_nil_iff.mp hcon).1
        rw [printProperty] at h3
        have h4 : printVBI p.id = [] := (List.append_eq_nil_iff.mp h3).1
        rw [h4] at h1
        exact absurd h1 (by decide)
      obtain ⟨hid, hty, hval, hok, hrep, htail⟩ := hwf
      rw [List.length_cons] at hlen
      show readEntriesGo (fuel + 1) s seen (printPropsList (p :: ps')) = _
      rw [printPropsList, readEntriesGo, ite_eq_right hne,
        readEntry_printProperty s seen p (printPropsList ps') hid hty hval hok hrep]
      simp only []
      rw [ih s (p.id :: seen) ps' (by omega) htail]

/-- A property list is never longer than its printing: each
    property takes at least the byte of its identifier. -/
theorem propsList_length_le (ps : List Property) :
    ps.length ≤ (printPropsList ps).length := by
  induction ps with
  | nil => simp [printPropsList]
  | cons p ps' ih =>
    have h1 : 0 < (printVBI p.id).length := printVBI_pos p.id
    simp only [printPropsList, printProperty, List.length_cons,
      List.length_append]
    omega

/-- A whole printed property block's insides read back. -/
theorem readEntries_printPropsList (s : PropSet) (ps : List Property)
    (h : PropsWF s [] ps) (hauth : authOK ps = true) :
    readEntries s (printPropsList ps) = some ps := by
  unfold readEntries
  rw [readEntriesGo_printPropsList (printPropsList ps).length s [] ps
    (propsList_length_le ps) h]
  simp only []
  rw [ite_eq_left hauth]

/-- A printed property block reads back: the properties, with
    the bytes after the block left in place. -/
theorem readProps_printProps (s : PropSet) (ps : List Property)
    (rest : List UInt8) (h : PropsBlockWF s ps) :
    readProps s (printProps ps ++ rest) = some (ps, rest) := by
  obtain ⟨hwf, hlen, hauth⟩ := h
  rw [readProps_step, printProps, List.append_assoc, decVBI_printVBI _ _ hlen]
  simp only [Option.bind_some]
  rw [readBytes_append _ _ _ rfl]
  simp only [Option.bind_some]
  rw [readEntries_printPropsList s ps hwf hauth]
  simp only [Option.bind_some]

/-! ## Topic names and flag bits -/

/-- An `any` test for one character fails when the character
    does not stand in the text. -/
theorem any_eq_false_of_not_mem {s : List Char} {c : Char} (h : c ∉ s) :
    s.any (fun x => decide (x = c)) = false := by
  simp only [List.any_eq_false]
  intro x hx hxc
  have hxcq : x = c := of_decide_eq_true hxc
  subst hxcq
  exact h hx

/-- The topic name check passes on a well formed topic name. -/
theorem checkTopic_of_wf {s : List Char} (h : TopicWF s) : checkTopic s = some s := by
  obtain ⟨hstr, hne, hp, hh⟩ := h
  have e1 : s.isEmpty = false := by
    cases s with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have e2 : s.any (fun c => decide (c = '+')) = false :=
    any_eq_false_of_not_mem hp
  have e3 : s.any (fun c => decide (c = '#')) = false :=
    any_eq_false_of_not_mem hh
  unfold checkTopic
  rw [e1, e2, e3]
  exact ite_eq_right (by decide)

/-- The wildcard check passes on a PUBLISH topic name fit to
    print. -/
theorem checkNoWildcards_of_wf {s : List Char} (hp : '+' ∉ s) (hh : '#' ∉ s) :
    checkNoWildcards s = some s := by
  unfold checkNoWildcards
  rw [any_eq_false_of_not_mem hp, any_eq_false_of_not_mem hh]
  exact ite_eq_right (by decide)

/-- The empty topic check passes on a PUBLISH topic name fit to
    print: an empty topic comes with a Topic Alias. -/
theorem pubTopic_alias_ok {s : List Char} {props : List Property}
    (h : s = [] → hasTopicAlias props = true) :
    ¬ ((s.isEmpty && !hasTopicAlias props) = true) := by
  cases s with
  | nil => rw [h rfl]; decide
  | cons c t => simp

/-- An `if` on a boolean, in the flags builders' shape, is the
    bit as a number times the place value. -/
theorem if_bool_mul (b : Bool) (x : Nat) :
    (if b then x else 0) = (if b then 1 else 0) * x := by
  cases b <;> simp

/-- The bits of a number built as `q + a * 4 + b * 8 + rh * 16`,
    with `a` and `b` bits and `q` and `rh` at most 2: the fields
    an options byte carries. Pure arithmetic. -/
theorem optsByte_fields (q rh a b : Nat) (hq : q ≤ 2) (hr : rh ≤ 2)
    (ha : a ≤ 1) (hb : b ≤ 1) :
    readOptsByte (q + a * 4 + b * 8 + rh * 16) = some ⟨q, a = 1, b = 1, rh⟩ := by
  unfold readOptsByte
  rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
  simp only [Option.some.injEq, SubOpts.mk.injEq]
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [show (q + a * 4 + b * 8 + rh * 16) / 4 % 2 = a by omega]
  · rw [show (q + a * 4 + b * 8 + rh * 16) / 8 % 2 = b by omega]

/-- A printed options byte reads back as the options. -/
theorem readOptsByte_printOptsByte (o : SubOpts) (h : OptsWF o) :
    readOptsByte (printOptsByte o).toNat = some o := by
  obtain ⟨q, nl, rap, rh⟩ := o
  have hq : q ≤ 2 := h.1
  have hr : rh ≤ 2 := h.2
  have ha : (if nl then (1 : Nat) else 0) ≤ 1 := by cases nl <;> decide
  have hb : (if rap then (1 : Nat) else 0) ≤ 1 := by cases rap <;> decide
  have hbound : q + (if nl then 1 else 0) * 4 + (if rap then 1 else 0) * 8
      + rh * 16 < 256 := by omega
  have hsum : (printOptsByte ⟨q, nl, rap, rh⟩).toNat
      = q + (if nl then 1 else 0) * 4 + (if rap then 1 else 0) * 8 + rh * 16 := by
    show ((q + (if nl then 4 else 0) + (if rap then 8 else 0) + rh * 16).toUInt8).toNat = _
    rw [if_bool_mul nl 4, if_bool_mul rap 8, toNat_toUInt8 hbound]
  rw [hsum, optsByte_fields q rh _ _ hq hr ha hb]
  cases nl <;> cases rap <;> rfl

/-! ## SUBSCRIBE filters -/

/-- A printed filter list is at least as long as the list: each
    filter takes at least the byte of its options. -/
theorem printFilters_length_ge : ∀ (fs : List (List Char × SubOpts)),
    fs.length ≤ (printFilters fs).length := by
  intro fs
  induction fs with
  | nil => simp [printFilters]
  | cons f fs' ih =>
    have h1 : 0 < (printFilter f).length := by
      simp only [printFilter, List.length_append, List.length_cons,
        List.length_nil]
      omega
    simp only [printFilters, List.length_cons, List.length_append]
    omega

/-- A printed filter list reads back whole, when its members
    are well formed: the reader spends one fuel per filter and
    each filter takes at least a byte, so the list's own length
    is fuel enough. -/
theorem readFiltersGo_printFilters : ∀ (fuel : Nat)
    (fs : List (List Char × SubOpts)),
    fs.length ≤ fuel → FiltersWF fs →
    readFiltersGo fuel (printFilters fs) = some (fs, []) := by
  intro fuel
  induction fuel with
  | zero =>
    intro fs hlen _
    have hfs : fs = [] := by
      cases fs with
      | nil => rfl
      | cons f fs' => simp at hlen
    rw [hfs]
    rfl
  | succ fuel ih =>
    intro fs hlen hwf
    cases fs with
    | nil => rfl
    | cons fr fs' =>
      obtain ⟨f, o⟩ := fr
      obtain ⟨hf, ho, hok, htail⟩ := hwf
      have hne : ¬ (printFilter (f, o) ++ printFilters fs').isEmpty := by
        have h1 : 0 < (printFilter (f, o)).length := by
          simp only [printFilter, List.length_append, List.length_cons,
            List.length_nil]
          omega
        intro hcon
        rw [List.isEmpty_iff] at hcon
        have h3 : printFilter (f, o) = [] := (List.append_eq_nil_iff.mp hcon).1
        rw [h3] at h1
        exact absurd h1 (by decide)
      rw [List.length_cons] at hlen
      show readFiltersGo (fuel + 1) (printFilters ((f, o) :: fs')) = _
      rw [printFilters, readFiltersGo, ite_eq_right hne, printFilter,
        List.append_assoc, readStr_printStr f _ hf]
      rw [List.cons_append, List.nil_append]
      simp only []
      rw [readOptsByte_printOptsByte o ho]
      simp only []
      rw [ite_eq_left hok, ih fs' (by omega) htail]

/-! ## Packet bodies -/

/-- One step of the single byte reader, stated for rewriting. -/
theorem readByte_cons (b : UInt8) (bs : List UInt8) :
    readByte (b :: bs) = some (b.toNat, bs) := rfl

/-- The bits of a PUBLISH flags nibble built from a packet's
    fields: the QoS sits at bits 2 and 1, DUP at bit 3, RETAIN
    at bit 0. -/
theorem publish_bits (dup retain : Bool) (qos : Nat) (hq : qos ≤ 2) :
    ((if dup then 8 else 0) + qos * 2 + (if retain then 1 else 0)) / 2 % 4 = qos
      ∧ flagBit ((if dup then 8 else 0) + qos * 2 + (if retain then 1 else 0)) 3 = dup
      ∧ flagBit ((if dup then 8 else 0) + qos * 2 + (if retain then 1 else 0)) 0
        = retain := by
  have e1 : (if dup then (8 : Nat) else 0) = (if dup then 1 else 0) * 8 :=
    if_bool_mul dup 8
  have e2 : (if retain then (1 : Nat) else 0) = (if retain then 1 else 0) * 1 :=
    if_bool_mul retain 1
  have ha : (if dup then (1 : Nat) else 0) ≤ 1 := by cases dup <;> decide
  have hb : (if retain then (1 : Nat) else 0) ≤ 1 := by cases retain <;> decide
  rw [e1, e2]
  refine ⟨by omega, ?_, ?_⟩
  · unfold flagBit
    rw [show (2 : Nat) ^ 3 = 8 by decide,
      show ((if dup then 1 else 0) * 8 + qos * 2 + (if retain then 1 else 0) * 1)
          / 8 % 2 = (if dup then 1 else 0) by omega]
    cases dup <;> rfl
  · unfold flagBit
    rw [show (2 : Nat) ^ 0 = 1 by decide,
      show ((if dup then 1 else 0) * 8 + qos * 2 + (if retain then 1 else 0) * 1)
          / 1 % 2 = (if retain then 1 else 0) by omega]
    cases retain <;> rfl

/-- The properties reader on exactly the printed bytes. -/
theorem readProps_printProps_exact (s : PropSet) (ps : List Property)
    (h : PropsBlockWF s ps) : readProps s (printProps ps) = some (ps, []) := by
  have h2 := readProps_printProps s ps [] h
  rwa [List.append_nil] at h2

/-- The SUBSCRIBE body reader as one bind chain; the form the
    round trip proof rewrites through. -/
theorem readSubscribeBody_step (seg : List UInt8) :
    readSubscribeBody seg =
    (readNat 2 seg).bind fun (id, r1) =>
      if id ≠ 0 then
        (readProps .subscribe r1).bind fun (props, r2) =>
        (readFiltersGo r2.length r2).bind fun (fs, r3) =>
          if r3.isEmpty && !fs.isEmpty then some (.subscribe id props fs)
          else none
      else none := rfl

/-- A printed SUBSCRIBE body reads back as the packet. -/
theorem readSubscribeBody_printSubscribeBody (id : Nat) (ps : List Property)
    (fs : List (List Char × SubOpts)) (hid : 1 ≤ id ∧ id < 65536)
    (hps : PropsBlockWF .subscribe ps) (hfs : fs ≠ [] ∧ FiltersWF fs) :
    readSubscribeBody (printSubscribeBody id ps fs) = some (.subscribe id ps fs) := by
  rw [readSubscribeBody_step,
    show printSubscribeBody id ps fs
      = writeBE 2 id ++ (printProps ps ++ printFilters fs) from rfl,
    readNat_writeBE 2 id _ (by omega)]
  simp only [Option.bind_some]
  rw [ite_eq_left (by omega : id ≠ 0), readProps_printProps .subscribe ps _ hps]
  simp only [Option.bind_some]
  rw [readFiltersGo_printFilters (printFilters fs).length fs
    (printFilters_length_ge fs) hfs.2]
  simp only [Option.bind_some]
  have h2 : fs.isEmpty = false := by
    cases fs with
    | nil => exact absurd rfl hfs.1
    | cons a t => rfl
  rw [ite_eq_left (by rw [h2]; rfl : ([].isEmpty && !fs.isEmpty) = true)]

/-- Reason codes written as bytes read back as themselves. -/
theorem map_toUInt8_toNat (rs : List Nat) (h : ∀ r ∈ rs, r < 256) :
    (rs.map Nat.toUInt8).map UInt8.toNat = rs := by
  induction rs with
  | nil => rfl
  | cons r rs' ih =>
    simp only [List.map_cons]
    rw [toNat_toUInt8 (h r (by simp)), ih (fun x hx => h x (by simp [hx]))]

/-- The SUBACK body reader as one bind chain. -/
theorem readSubackBody_step (seg : List UInt8) :
    readSubackBody seg =
    (readNat 2 seg).bind fun (id, r1) =>
      if id ≠ 0 then
        (readProps .suback r1).bind fun (props, r2) =>
          if !r2.isEmpty then some (.suback id props (r2.map UInt8.toNat))
          else none
      else none := rfl

/-- A printed SUBACK body reads back as the packet. -/
theorem readSubackBody_printSubackBody (id : Nat) (ps : List Property)
    (rs : List Nat) (hid : 1 ≤ id ∧ id < 65536)
    (hps : PropsBlockWF .suback ps) (hrs : rs ≠ [] ∧ ∀ r ∈ rs, r < 256) :
    readSubackBody (printSubackBody id ps rs) = some (.suback id ps rs) := by
  rw [readSubackBody_step,
    show printSubackBody id ps rs
      = writeBE 2 id ++ (printProps ps ++ rs.map Nat.toUInt8) from rfl,
    readNat_writeBE 2 id _ (by omega)]
  simp only [Option.bind_some]
  rw [ite_eq_left (by omega : id ≠ 0), readProps_printProps .suback ps _ hps]
  simp only [Option.bind_some]
  have h2 : (rs.map Nat.toUInt8).isEmpty = false := by
    cases rs with
    | nil => exact absurd rfl hrs.1
    | cons a t => rfl
  rw [ite_eq_left (by rw [h2]; rfl : (!(rs.map Nat.toUInt8).isEmpty) = true),
    map_toUInt8_toNat rs hrs.2]

/-- A printed DISCONNECT body reads back as the packet, in each
    of its three forms. -/
theorem readDisconnectBody_print (x : Option (Nat × Option (List Property)))
    (h : match x with
      | none => True
      | some (rc, none) => rc < 256
      | some (rc, some ps) => rc < 256 ∧ PropsBlockWF PropSet.disconnect ps) :
    readDisconnectBody (bodyOf (Packet.disconnect x))
      = some (Packet.disconnect x) := by
  cases x with
  | none => rfl
  | some rp =>
    obtain ⟨rc, ops⟩ := rp
    cases ops with
    | none =>
      have hrc : rc < 256 := h
      show readDisconnectBody [rc.toUInt8]
          = some (Packet.disconnect (some (rc, none)))
      show (if ([] : List UInt8).isEmpty
          then some (Packet.disconnect (some ((rc.toUInt8).toNat, none)))
          else (readProps PropSet.disconnect []).bind
            fun (props, r2) =>
            if r2.isEmpty
              then some (Packet.disconnect (some ((rc.toUInt8).toNat, some props)))
              else none) = some (Packet.disconnect (some (rc, none)))
      rw [ite_eq_left (by decide : List.isEmpty ([] : List UInt8) = true),
        toNat_toUInt8 hrc]
    | some ps =>
      obtain ⟨hrc, hps⟩ := h
      show readDisconnectBody ([rc.toUInt8] ++ printProps ps)
          = some (Packet.disconnect (some (rc, some ps)))
      rw [show [rc.toUInt8] ++ printProps ps = rc.toUInt8 :: printProps ps from rfl]
      have hpos : 0 < (printProps ps).length := by
        show 0 < (printVBI (printPropsList ps).length
          ++ printPropsList ps).length
        rw [List.length_append]
        have h1 := printVBI_pos (printPropsList ps).length
        omega
      have hne : ¬ ((printProps ps).isEmpty = true) := by
        intro hcon
        rw [List.isEmpty_iff] at hcon
        have hz : (printProps ps).length = 0 := congrArg List.length hcon
        omega
      show (if (printProps ps).isEmpty
          then some (Packet.disconnect (some ((rc.toUInt8).toNat, none)))
          else (readProps PropSet.disconnect (printProps ps)).bind
            fun (props, r2) =>
            if r2.isEmpty
              then some (Packet.disconnect (some ((rc.toUInt8).toNat, some props)))
              else none) = some (Packet.disconnect (some (rc, some ps)))
      rw [ite_eq_right hne]
      simp only [readProps_printProps_exact PropSet.disconnect ps hps,
        Option.bind_some]
      rw [ite_eq_left (by decide : List.isEmpty ([] : List UInt8) = true),
        toNat_toUInt8 hrc]

/-- The facts about a well formed connect flags byte: it
    fits in a byte, the reserved bit is clear, and every field
    the reader recovers from the byte (the will QoS, the will
    retain, the will flag, the username and password flags,
    the clean start) is the field that was written. -/
theorem connectFlags_facts (c : Connect) (h : ConnectWF c) :
    (connectFlags c).toUInt8.toNat = connectFlags c
    ∧ connectFlags c % 2 = 0
    ∧ (connectFlags c / 8) % 4
        = (match c.will with | some w => w.qos | none => 0)
    ∧ flagBit (connectFlags c) 7 = c.username.isSome
    ∧ flagBit (connectFlags c) 6 = c.password.isSome
    ∧ flagBit (connectFlags c) 5
        = (match c.will with | some w => w.retain | none => false)
    ∧ flagBit (connectFlags c) 2 = c.will.isSome
    ∧ flagBit (connectFlags c) 1 = c.cleanStart
    ∧ (c.will = none → (connectFlags c / 8) % 8 = 0) := by
  have e1 : (if c.username.isSome then (128 : Nat) else 0)
      = (if c.username.isSome then 1 else 0) * 128 := if_bool_mul _ _
  have e2 : (if c.password.isSome then (64 : Nat) else 0)
      = (if c.password.isSome then 1 else 0) * 64 := if_bool_mul _ _
  have e3 : (if c.cleanStart then (2 : Nat) else 0)
      = (if c.cleanStart then 1 else 0) * 2 := if_bool_mul _ _
  have hub : (if c.username.isSome then (1 : Nat) else 0) ≤ 1 := by
    cases h : c.username.isSome <;> decide
  have hpb : (if c.password.isSome then (1 : Nat) else 0) ≤ 1 := by
    cases h : c.password.isSome <;> decide
  have hcs : (if c.cleanStart then (1 : Nat) else 0) ≤ 1 := by
    cases h : c.cleanStart <;> decide
  cases hw : c.will with
  | none =>
    have hf : connectFlags c
        = (if c.username.isSome then 1 else 0) * 128
          + (if c.password.isSome then 1 else 0) * 64
          + (if c.cleanStart then 1 else 0) * 2 := by
      unfold connectFlags
      rw [e1, e2, e3, hw]
      dsimp only
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf]
      exact toNat_toUInt8 (by omega)
    · rw [hf]; omega
    · show (connectFlags c / 8) % 4 = 0
      rw [hf]; omega
    · rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 7 = 128 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + (if c.cleanStart then 1 else 0) * 2) / 128 % 2
          = (if c.username.isSome then 1 else 0) by omega]
      cases h : c.username.isSome <;> rfl
    · rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 6 = 64 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + (if c.cleanStart then 1 else 0) * 2) / 64 % 2
          = (if c.password.isSome then 1 else 0) by omega]
      cases h : c.password.isSome <;> rfl
    · show flagBit (connectFlags c) 5 = false
      rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 5 = 32 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + (if c.cleanStart then 1 else 0) * 2) / 32 % 2 = 0 by omega]
      rfl
    · show flagBit (connectFlags c) 2 = false
      rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 2 = 4 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + (if c.cleanStart then 1 else 0) * 2) / 4 % 2 = 0 by omega]
      rfl
    · rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 1 = 2 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + (if c.cleanStart then 1 else 0) * 2) / 2 % 2
          = (if c.cleanStart then 1 else 0) by omega]
      cases h : c.cleanStart <;> rfl
    · intro _
      rw [hf]; omega
  | some w =>
    have hwf : WillWF w := h.2.2.2.1 w hw
    have hwq : w.qos ≤ 2 := hwf.1
    have hrb : (if w.retain then (1 : Nat) else 0) ≤ 1 := by
      cases w.retain <;> decide
    have e4 : (if w.retain then (32 : Nat) else 0)
        = (if w.retain then 1 else 0) * 32 := if_bool_mul _ _
    have hf : connectFlags c
        = (if c.username.isSome then 1 else 0) * 128
          + (if c.password.isSome then 1 else 0) * 64
          + ((if w.retain then 1 else 0) * 32 + w.qos * 8 + 4)
          + (if c.cleanStart then 1 else 0) * 2 := by
      unfold connectFlags
      rw [e1, e2, e3, hw]
      dsimp only
      rw [e4]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf]
      exact toNat_toUInt8 (by omega)
    · rw [hf]; omega
    · show (connectFlags c / 8) % 4 = w.qos
      rw [hf]; omega
    · rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 7 = 128 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + ((if w.retain then 1 else 0) * 32 + w.qos * 8 + 4)
            + (if c.cleanStart then 1 else 0) * 2) / 128 % 2
          = (if c.username.isSome then 1 else 0) by omega]
      cases h : c.username.isSome <;> rfl
    · rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 6 = 64 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + ((if w.retain then 1 else 0) * 32 + w.qos * 8 + 4)
            + (if c.cleanStart then 1 else 0) * 2) / 64 % 2
          = (if c.password.isSome then 1 else 0) by omega]
      cases h : c.password.isSome <;> rfl
    · show flagBit (connectFlags c) 5 = w.retain
      rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 5 = 32 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + ((if w.retain then 1 else 0) * 32 + w.qos * 8 + 4)
            + (if c.cleanStart then 1 else 0) * 2) / 32 % 2
          = (if w.retain then 1 else 0) by omega]
      cases w.retain <;> rfl
    · show flagBit (connectFlags c) 2 = true
      rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 2 = 4 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + ((if w.retain then 1 else 0) * 32 + w.qos * 8 + 4)
            + (if c.cleanStart then 1 else 0) * 2) / 4 % 2 = 1 by omega]
      rfl
    · rw [hf]
      unfold flagBit
      rw [show (2 : Nat) ^ 1 = 2 by decide,
        show ((if c.username.isSome then 1 else 0) * 128
            + (if c.password.isSome then 1 else 0) * 64
            + ((if w.retain then 1 else 0) * 32 + w.qos * 8 + 4)
            + (if c.cleanStart then 1 else 0) * 2) / 2 % 2
          = (if c.cleanStart then 1 else 0) by omega]
      cases h : c.cleanStart <;> rfl
    · intro hn
      cases hn

/-- The CONNECT tail: the optional username and password
    fields read back as themselves, and nothing is left
    over, so the assembled packet is the one that was
    printed. The three flag values are the reader's own
    recoveries from the flags byte; the hypotheses tie them
    to the fields. -/
theorem readOptFields (u : Option (List Char)) (p : Option (List UInt8))
    (hu : ∀ s, u = some s → StrWF s) (hp : ∀ b, p = some b → BinWF b)
    (cs : Bool) (ka : Nat) (props : List Property) (cid : List Char)
    (will : Option Will) (f7 f6 f1 : Bool)
    (h7 : f7 = u.isSome) (h6 : f6 = p.isSome) (h1 : f1 = cs) :
    ((readOptStrField f7 (printOptStr u ++ printOptBin p)).bind
        fun (u', r8) =>
      (readOptBinField f6 r8).bind fun (p', r9) =>
      (if r9.isEmpty
        then some (⟨f1, ka, props, cid, will, u', p'⟩ : Connect) else none)
      : Option Connect)
    = some (⟨cs, ka, props, cid, will, u, p⟩ : Connect) := by
  subst h7
  subst h6
  subst h1
  cases u with
  | none =>
    rw [show printOptStr none = [] from rfl, List.nil_append]
    unfold readOptStrField
    rw [ite_eq_right (by decide : ¬ (Option.isSome none = true))]
    simp only [Option.bind_some]
    cases p with
    | none =>
      rw [show printOptBin none = [] from rfl]
      unfold readOptBinField
      rw [ite_eq_right (by decide : ¬ (Option.isSome none = true))]
      simp only [Option.bind_some]
      rw [ite_eq_left (by decide : List.isEmpty [] = true)]
    | some b =>
      rw [show printOptBin (some b) = printBin b from rfl]
      unfold readOptBinField
      rw [ite_eq_left (by rfl : Option.isSome (some b) = true),
        ← List.append_nil (printBin b), readBin_printBin b [] (hp b rfl)]
      simp only [Option.map_some, Option.bind_some]
      rw [ite_eq_left (by decide : List.isEmpty [] = true)]
  | some s =>
    rw [show printOptStr (some s) = printStr s from rfl]
    unfold readOptStrField
    rw [ite_eq_left (by rfl : Option.isSome (some s) = true),
      readStr_printStr s _ (hu s rfl)]
    simp only [Option.map_some, Option.bind_some]
    cases p with
    | none =>
      rw [show printOptBin none = [] from rfl]
      unfold readOptBinField
      rw [ite_eq_right (by decide : ¬ (Option.isSome none = true))]
      simp only [Option.bind_some]
      rw [ite_eq_left (by decide : List.isEmpty [] = true)]
    | some b =>
      rw [show printOptBin (some b) = printBin b from rfl]
      unfold readOptBinField
      rw [ite_eq_left (by rfl : Option.isSome (some b) = true),
        ← List.append_nil (printBin b), readBin_printBin b [] (hp b rfl)]
      simp only [Option.map_some, Option.bind_some]
      rw [ite_eq_left (by decide : List.isEmpty [] = true)]

/-- A printed CONNECT body reads back as the packet. -/
theorem readConnectBody_printConnectBody (c : Connect) (h : ConnectWF c) :
    readConnectBody (printConnectBody c) = some c := by
  obtain ⟨hka, hprops, hcid, hwill, huser, hpass⟩ := h
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9⟩ := connectFlags_facts c
    ⟨hka, hprops, hcid, hwill, huser, hpass⟩
  have hfin : ∀ (w : Option Will), w = c.will →
      (⟨c.cleanStart, c.keepAlive, c.props, c.clientId, w, c.username,
        c.password⟩ : Connect) = c := by
    intro w hw
    subst hw
    rfl
  have hproto : StrWF ['M', 'Q', 'T', 'T'] := by
    constructor
    · decide
    · decide
  unfold readConnectBody
  rw [show printConnectBody c
      = printStr ['M', 'Q', 'T', 'T'] ++ ([5, (connectFlags c).toUInt8]
        ++ (writeBE 2 c.keepAlive ++ (printProps c.props
        ++ (printStr c.clientId ++ (printWillPart c.will
        ++ (printOptStr c.username ++ printOptBin c.password))))))
      from rfl,
    readStr_printStr _ _ hproto]
  simp only [Option.bind_some]
  rw [ite_eq_left trivial]
  simp only [List.cons_append, List.nil_append]
  rw [readByte_cons]
  simp only [Option.bind_some]
  rw [ite_eq_left (by decide : (5 : UInt8).toNat = 5), readByte_cons]
  simp only [Option.bind_some]
  rw [hf1, ite_eq_left hf2]
  by_cases hwn : c.will = none
  · have hf3' : (connectFlags c / 8) % 4 = 0 := by rw [hf3, hwn]
    have hf7' : flagBit (connectFlags c) 2 = false := by simp [hf7, hwn]
    rw [ite_eq_left (by rw [hf3']; omega : (connectFlags c / 8) % 4 ≠ 3),
      ite_eq_left (by rw [hf9 hwn]; simp :
        (flagBit (connectFlags c) 2 || decide ((connectFlags c / 8) % 8 = 0)) = true),
      readNat_writeBE 2 c.keepAlive _ (by omega)]
    simp only [Option.bind_some]
    rw [readProps_printProps .connect c.props _ hprops]
    simp only [Option.bind_some]
    rw [readStr_printStr c.clientId _ hcid]
    simp only [Option.bind_some]
    rw [hwn, show printWillPart none = [] from rfl, List.nil_append]
    unfold readWillPart
    rw [ite_eq_right (by rw [hf7']; decide : ¬ (flagBit (connectFlags c) 2 = true))]
    simp only [Option.bind_some]
    rw [readOptFields c.username c.password huser hpass c.cleanStart
      c.keepAlive c.props c.clientId none (flagBit (connectFlags c) 7)
      (flagBit (connectFlags c) 6) (flagBit (connectFlags c) 1) hf4 hf5 hf8]
    exact congrArg Option.some (hfin none hwn.symm)
  · obtain ⟨w, hw⟩ : ∃ w, c.will = some w := by
      cases hw2 : c.will with
      | none => exact absurd hw2 hwn
      | some w => exact ⟨w, rfl⟩
    obtain ⟨wq, wr, wps, wt, wpay⟩ := w
    have hwf : WillWF ⟨wq, wr, wps, wt, wpay⟩ := hwill _ hw
    have hwq : wq ≤ 2 := hwf.1
    have hwprops : PropsBlockWF .will wps := hwf.2.1
    have hwtopic : TopicWF wt := hwf.2.2.1
    have hwpay : BinWF wpay := hwf.2.2.2
    have hf3' : (connectFlags c / 8) % 4 = wq := by rw [hf3, hw]
    have hf6' : flagBit (connectFlags c) 5 = wr := by rw [hf6, hw]
    have hf7' : flagBit (connectFlags c) 2 = true := by simp [hf7, hw]
    rw [ite_eq_left (by rw [hf3']; omega : (connectFlags c / 8) % 4 ≠ 3),
      ite_eq_left (by rw [hf7']; rfl :
        (flagBit (connectFlags c) 2 || decide ((connectFlags c / 8) % 8 = 0)) = true),
      readNat_writeBE 2 c.keepAlive _ (by omega)]
    simp only [Option.bind_some]
    rw [readProps_printProps .connect c.props _ hprops]
    simp only [Option.bind_some]
    rw [readStr_printStr c.clientId _ hcid]
    simp only [Option.bind_some]
    rw [hw, show printWillPart (some ⟨wq, wr, wps, wt, wpay⟩)
        = printProps wps ++ (printStr wt ++ printBin wpay) from rfl]
    unfold readWillPart
    rw [ite_eq_left hf7', List.append_assoc, readProps_printProps .will wps _ hwprops]
    simp only [Option.bind_some]
    rw [List.append_assoc, readStr_printStr wt _ hwtopic.1]
    simp only [Option.bind_some]
    rw [checkTopic_of_wf hwtopic]
    simp only [Option.bind_some]
    rw [readBin_printBin wpay _ hwpay]
    simp only [Option.bind_some]
    rw [readOptFields c.username c.password huser hpass c.cleanStart
      c.keepAlive c.props c.clientId
      (some ⟨(connectFlags c / 8) % 4, flagBit (connectFlags c) 5, wps, wt,
        wpay⟩)
      (flagBit (connectFlags c) 7) (flagBit (connectFlags c) 6)
      (flagBit (connectFlags c) 1) hf4 hf5 hf8]
    rw [hf3', hf6']
    exact congrArg Option.some (hfin _ hw.symm)

/-- The packet identifier step at QoS 0 reads nothing. -/
theorem readPacketId_qos0 (flags : Nat) (r : List UInt8)
    (h : (flags / 2) % 4 = 0) :
    readPacketId flags r = some (none, r) := by
  unfold readPacketId
  rw [ite_eq_left h]

/-- The packet identifier step at QoS 1 and 2 reads a printed
    nonzero identifier. -/
theorem readPacketId_print (flags : Nat) (i : Nat) (rest : List UInt8)
    (h : (flags / 2) % 4 ≠ 0) (hi : 1 ≤ i ∧ i < 65536) :
    readPacketId flags (printIdOpt (some i) ++ rest) = some (some i, rest) := by
  unfold readPacketId
  rw [ite_eq_right h, show printIdOpt (some i) = writeBE 2 i from rfl,
    readNat_writeBE 2 i _ (by omega)]
  simp only [Option.bind_some]
  rw [ite_eq_left (by omega : i ≠ 0)]

/-- A printed PUBLISH body reads back as the packet, when the
    flags word carries the packet's own QoS, DUP and RETAIN. -/
theorem readPublishBody_printPublishBody (flags : Nat) (pub : Publish)
    (hq : (flags / 2) % 4 = pub.qos) (h3 : flagBit flags 3 = pub.dup)
    (h0 : flagBit flags 0 = pub.retain) (h : PublishWF pub) :
    readPublishBody flags (printPublishBody pub) = some pub := by
  obtain ⟨dup, qos, retain, topic, pid, props, payload⟩ := pub
  obtain ⟨hqos, htopic, hidf, hnone, hprops, _⟩ := h
  have htopic' : PubTopicWF topic props := htopic
  have hcond := pubTopic_alias_ok htopic'.2.2.2
  have hidf' : ∀ id, pid = some id →
      1 ≤ id ∧ id < 65536 ∧ (qos = 1 ∨ qos = 2) := hidf
  have hnone' : pid = none → qos = 0 := hnone
  have hprops' : PropsBlockWF .publish props := hprops
  have hq' : (flags / 2) % 4 = qos := hq
  have h3' : flagBit flags 3 = dup := h3
  have h0' : flagBit flags 0 = retain := h0
  unfold readPublishBody
  rw [show printPublishBody ⟨dup, qos, retain, topic, pid, props, payload⟩
      = printStr topic ++ (printIdOpt pid ++ (printProps props ++ payload))
      from rfl,
    readStr_printStr topic _ htopic'.1]
  simp only [Option.bind_some]
  rw [checkNoWildcards_of_wf htopic'.2.1 htopic'.2.2.1]
  simp only [Option.bind_some]
  by_cases hq0 : qos = 0
  · have hpid : pid = none := by
      cases hp : pid with
      | none => rfl
      | some i =>
        have h2 := hidf' i hp
        omega
    rw [hpid, show printIdOpt none = [] from rfl, List.nil_append,
      readPacketId_qos0 flags _ (by omega)]
    simp only [Option.bind_some]
    rw [readProps_printProps .publish props payload hprops']
    simp only [Option.bind_some]
    rw [ite_eq_right hcond, h3', h0', hq']
  · have hpid : ∃ i, pid = some i ∧ 1 ≤ i ∧ i < 65536 := by
      cases hp : pid with
      | none => exact absurd (hnone' hp) hq0
      | some i =>
        have h2 := hidf' i hp
        exact ⟨i, rfl, h2.1, h2.2.1⟩
    obtain ⟨i, hi, hi1, hi2⟩ := hpid
    rw [hi, readPacketId_print flags i _ (by omega) ⟨hi1, hi2⟩]
    simp only [Option.bind_some]
    rw [readProps_printProps .publish props payload hprops']
    simp only [Option.bind_some]
    rw [ite_eq_right hcond, h3', h0', hq']

/-! ## Whole packets -/

/-- A well formed PUBLISH header byte value fits in a
    byte: the fixed part is 0x30 and the flags part is at
    most 8 + 4 + 1. -/
theorem publishHeader_bound (pub : Publish) (h : PublishWF pub) :
    publishHeader pub < 256 := by
  have hA : (if pub.dup then (8 : Nat) else 0) ≤ 8 := by
    cases pub.dup <;> decide
  have hB : (if pub.retain then (1 : Nat) else 0) ≤ 1 := by
    cases pub.retain <;> decide
  have hqos : pub.qos ≤ 2 := h.1
  unfold publishHeader
  omega

/-- The body dispatcher on a printed CONNECT body. -/
theorem parseBody_connect (c : Connect) (h : ConnectWF c) :
    parseBody 1 0 (printConnectBody c) = some (.connect c) := by
  show (readConnectBody (printConnectBody c)).map Packet.connect
    = some (.connect c)
  rw [readConnectBody_printConnectBody c h]
  simp only [Option.map_some]

/-- The body dispatcher on a printed PUBLISH body. -/
theorem parseBody_publish (pub : Publish) (h : PublishWF pub) :
    parseBody 3 (publishHeader pub % 16) (printPublishBody pub)
      = some (.publish pub) := by
  have hqos : pub.qos ≤ 2 := h.1
  have hA : (if pub.dup then (8 : Nat) else 0) ≤ 8 := by
    cases pub.dup <;> decide
  have hB : (if pub.retain then (1 : Nat) else 0) ≤ 1 := by
    cases pub.retain <;> decide
  have hE : (if pub.dup then 8 else 0) + pub.qos * 2
      + (if pub.retain then 1 else 0) ≤ 15 := by omega
  have hphv : publishHeader pub
      = 48 + ((if pub.dup then 8 else 0) + pub.qos * 2
        + (if pub.retain then 1 else 0)) := by
    unfold publishHeader
    omega
  have hmod : publishHeader pub % 16
      = (if pub.dup then 8 else 0) + pub.qos * 2
        + (if pub.retain then 1 else 0) := by omega
  have hb := publish_bits pub.dup pub.retain pub.qos hqos
  have hdupwf : pub.qos = 0 → pub.dup = false := h.2.2.2.2.2
  have hdup : ¬ (((if pub.dup then 8 else 0) + pub.qos * 2
      + (if pub.retain then 1 else 0)) / 2 % 4 = 0
      ∧ flagBit ((if pub.dup then 8 else 0) + pub.qos * 2
        + (if pub.retain then 1 else 0)) 3 = true) := by
    rw [hb.1, hb.2.1]
    intro hc
    rw [hdupwf hc.1] at hc
    cases hc.2
  show (if (publishHeader pub % 16 / 2) % 4 = 3 then none
    else if (publishHeader pub % 16 / 2) % 4 = 0
        ∧ flagBit (publishHeader pub % 16) 3 = true then none
    else (readPublishBody (publishHeader pub % 16) (printPublishBody pub)).map
      Packet.publish) = some (.publish pub)
  rw [hmod, ite_eq_right (by rw [hb.1]; omega :
      ¬ ((if pub.dup then 8 else 0) + pub.qos * 2
        + (if pub.retain then 1 else 0)) / 2 % 4 = 3),
    ite_eq_right hdup,
    readPublishBody_printPublishBody _ pub hb.1 hb.2.1 hb.2.2 h]
  simp only [Option.map_some]

/-- The body dispatcher on a printed SUBSCRIBE body. -/
theorem parseBody_subscribe (id : Nat) (ps : List Property)
    (fs : List (List Char × SubOpts)) (hid : 1 ≤ id ∧ id < 65536)
    (hps : PropsBlockWF .subscribe ps) (hfs : fs ≠ [] ∧ FiltersWF fs) :
    parseBody 8 2 (printSubscribeBody id ps fs)
      = some (.subscribe id ps fs) := by
  show (if (2 : Nat) = 2 then readSubscribeBody (printSubscribeBody id ps fs)
    else none) = some (.subscribe id ps fs)
  rw [ite_eq_left rfl, readSubscribeBody_printSubscribeBody id ps fs hid hps hfs]

/-- The body dispatcher on a printed SUBACK body. -/
theorem parseBody_suback (id : Nat) (ps : List Property) (rs : List Nat)
    (hid : 1 ≤ id ∧ id < 65536) (hps : PropsBlockWF .suback ps)
    (hrs : rs ≠ [] ∧ ∀ r ∈ rs, r < 256) :
    parseBody 9 0 (printSubackBody id ps rs) = some (.suback id ps rs) := by
  show (if (0 : Nat) = 0 then readSubackBody (printSubackBody id ps rs)
    else none) = some (.suback id ps rs)
  rw [ite_eq_left rfl, readSubackBody_printSubackBody id ps rs hid hps hrs]

/-- The body dispatcher on an empty PINGREQ body: a closed
    computation. -/
theorem parseBody_pingreq : parseBody 12 0 [] = some .pingreq := by decide

/-- The body dispatcher on an empty PINGRESP body. -/
theorem parseBody_pingresp : parseBody 13 0 [] = some .pingresp := by decide

/-- The body dispatcher on an empty DISCONNECT body. -/
theorem parseBody_disconnect_none :
    parseBody 14 0 (bodyOf (.disconnect none)) = some (.disconnect none) := by
  show (if (0 : Nat) = 0 then readDisconnectBody (bodyOf (.disconnect none))
    else none) = some (.disconnect none)
  rw [ite_eq_left rfl, readDisconnectBody_print none trivial]

/-- The body dispatcher on a printed DISCONNECT body with a
    reason code alone. -/
theorem parseBody_disconnect_short (rc : Nat) (h : rc < 256) :
    parseBody 14 0 (bodyOf (.disconnect (some (rc, none))))
      = some (.disconnect (some (rc, none))) := by
  show (if (0 : Nat) = 0
      then readDisconnectBody (bodyOf (.disconnect (some (rc, none))))
      else none) = some (.disconnect (some (rc, none)))
  rw [ite_eq_left rfl, readDisconnectBody_print (some (rc, none)) h]

/-- The body dispatcher on a printed DISCONNECT body with a
    reason code and properties. -/
theorem parseBody_disconnect_some (rc : Nat) (ps : List Property)
    (h : rc < 256 ∧ PropsBlockWF PropSet.disconnect ps) :
    parseBody 14 0 (bodyOf (.disconnect (some (rc, some ps))))
      = some (.disconnect (some (rc, some ps))) := by
  show (if (0 : Nat) = 0
      then readDisconnectBody (bodyOf (.disconnect (some (rc, some ps))))
      else none) = some (.disconnect (some (rc, some ps)))
  rw [ite_eq_left rfl, readDisconnectBody_print (some (rc, some ps)) h]

/-- One packet at the head of a stream: a printed packet
    followed by any bytes parses to the packet and leaves
    the rest of the stream untouched. -/
theorem parsePacket_print (p : Packet) (rest : List UInt8) (h : PacketWF p) :
    parsePacket (print p ++ rest) = some (p, rest) := by
  obtain ⟨hfields, hlen⟩ := h
  have hnorm : print p ++ rest
      = headerOf p :: (printVBI (bodyOf p).length ++ (bodyOf p ++ rest)) := by
    show (headerOf p :: (printVBI (bodyOf p).length ++ bodyOf p)) ++ rest
      = headerOf p :: (printVBI (bodyOf p).length ++ (bodyOf p ++ rest))
    rw [List.cons_append, List.append_assoc]
  rw [hnorm]
  show ((decVBI (printVBI (bodyOf p).length ++ (bodyOf p ++ rest))).bind
      fun (len, r1) =>
    (readBytes len r1).bind fun (seg, r2) =>
    (parseBody ((headerOf p).toNat / 16) ((headerOf p).toNat % 16) seg).bind
      fun q => some (q, r2)) = some (p, rest)
  rw [decVBI_printVBI _ _ hlen]
  simp only [Option.bind_some]
  rw [readBytes_append _ _ _ rfl]
  simp only [Option.bind_some]
  cases p with
  | connect c =>
    have hfc : ConnectWF c := hfields
    have e1 : (headerOf (.connect c)).toNat / 16 = 1 := by
      rw [show headerOf (.connect c) = (0x10 : UInt8) from rfl]; decide
    have e2 : (headerOf (.connect c)).toNat % 16 = 0 := by
      rw [show headerOf (.connect c) = (0x10 : UInt8) from rfl]; decide
    have e3 : bodyOf (.connect c) = printConnectBody c := rfl
    rw [e1, e2, e3]
    simp only [parseBody_connect c hfc, Option.bind_some]
  | publish pub =>
    have hfp : PublishWF pub := hfields
    have hph : (publishHeader pub).toUInt8.toNat = publishHeader pub :=
      toNat_toUInt8 (publishHeader_bound pub hfp)
    have hqos : pub.qos ≤ 2 := hfp.1
    have hA : (if pub.dup then (8 : Nat) else 0) ≤ 8 := by
      cases pub.dup <;> decide
    have hB : (if pub.retain then (1 : Nat) else 0) ≤ 1 := by
      cases pub.retain <;> decide
    have hphv : publishHeader pub
        = 48 + ((if pub.dup then 8 else 0) + pub.qos * 2
          + (if pub.retain then 1 else 0)) := by
      unfold publishHeader
      omega
    have hE : (if pub.dup then 8 else 0) + pub.qos * 2
        + (if pub.retain then 1 else 0) ≤ 15 := by omega
    have hdiv : publishHeader pub / 16 = 3 := by omega
    have e3 : bodyOf (.publish pub) = printPublishBody pub := rfl
    have e0 : headerOf (.publish pub) = (publishHeader pub).toUInt8 := rfl
    rw [e3, e0, hph, hdiv]
    simp only [parseBody_publish pub hfp, Option.bind_some]
  | subscribe id ps fs =>
    have hid : 1 ≤ id ∧ id < 65536 := ⟨hfields.1, hfields.2.1⟩
    have hps : PropsBlockWF .subscribe ps := hfields.2.2.1
    have hfs : fs ≠ [] ∧ FiltersWF fs := ⟨hfields.2.2.2.1, hfields.2.2.2.2⟩
    have e1 : (headerOf (.subscribe id ps fs)).toNat / 16 = 8 := by
      rw [show headerOf (.subscribe id ps fs) = (0x82 : UInt8) from rfl]; decide
    have e2 : (headerOf (.subscribe id ps fs)).toNat % 16 = 2 := by
      rw [show headerOf (.subscribe id ps fs) = (0x82 : UInt8) from rfl]; decide
    have e3 : bodyOf (.subscribe id ps fs) = printSubscribeBody id ps fs := rfl
    rw [e1, e2, e3]
    simp only [parseBody_subscribe id ps fs hid hps hfs, Option.bind_some]
  | suback id ps rs =>
    have hid : 1 ≤ id ∧ id < 65536 := ⟨hfields.1, hfields.2.1⟩
    have hps : PropsBlockWF .suback ps := hfields.2.2.1
    have hrs : rs ≠ [] ∧ ∀ r ∈ rs, r < 256 :=
      ⟨hfields.2.2.2.1, hfields.2.2.2.2⟩
    have e1 : (headerOf (.suback id ps rs)).toNat / 16 = 9 := by
      rw [show headerOf (.suback id ps rs) = (0x90 : UInt8) from rfl]; decide
    have e2 : (headerOf (.suback id ps rs)).toNat % 16 = 0 := by
      rw [show headerOf (.suback id ps rs) = (0x90 : UInt8) from rfl]; decide
    have e3 : bodyOf (.suback id ps rs) = printSubackBody id ps rs := rfl
    rw [e1, e2, e3]
    simp only [parseBody_suback id ps rs hid hps hrs, Option.bind_some]
  | pingreq =>
    have e1 : (headerOf .pingreq).toNat / 16 = 12 := by decide
    have e2 : (headerOf .pingreq).toNat % 16 = 0 := by decide
    have e3 : bodyOf .pingreq = [] := rfl
    rw [e1, e2, e3]
    simp only [parseBody_pingreq, Option.bind_some]
  | pingresp =>
    have e1 : (headerOf .pingresp).toNat / 16 = 13 := by decide
    have e2 : (headerOf .pingresp).toNat % 16 = 0 := by decide
    have e3 : bodyOf .pingresp = [] := rfl
    rw [e1, e2, e3]
    simp only [parseBody_pingresp, Option.bind_some]
  | disconnect x =>
    have e1 : (headerOf (.disconnect x)).toNat / 16 = 14 := by
      rw [show headerOf (.disconnect x) = (0xE0 : UInt8) from rfl]; decide
    have e2 : (headerOf (.disconnect x)).toNat % 16 = 0 := by
      rw [show headerOf (.disconnect x) = (0xE0 : UInt8) from rfl]; decide
    rw [e1, e2]
    cases x with
    | none =>
      simp only [parseBody_disconnect_none, Option.bind_some]
    | some rp =>
      obtain ⟨rc, ops⟩ := rp
      cases ops with
      | none =>
        have h2 : rc < 256 := hfields
        simp only [parseBody_disconnect_short rc h2, Option.bind_some]
      | some ps =>
        have h2 : rc < 256 ∧ PropsBlockWF PropSet.disconnect ps := hfields
        simp only [parseBody_disconnect_some rc ps h2, Option.bind_some]

/-- The main round trip claim: a well formed packet,
    printed and parsed back on its own, is the same
    packet. -/
theorem parse_print (p : Packet) (h : PacketWF p) : parse (print p) = some p := by
  unfold parse
  have h2 := parsePacket_print p [] h
  rw [List.append_nil] at h2
  simp only [h2]

end Mqtt.Proofs
