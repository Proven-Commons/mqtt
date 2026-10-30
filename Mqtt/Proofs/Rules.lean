/-
  Proofs of the statements in `Mqtt/Spec.lean` whose rule text stands
  in `Mqtt/Spec/Defs.lean`, part of the specification.

  Each proof starts from what the reader is already proved to
  accept (`parsePacket_inv` in `Mqtt/Proofs/Sound.lean`, and
  `decVBI_canonical` in `Mqtt/Proofs/RoundTrip.lean`) and shows that the
  rule written in the specification holds for it.
-/

import Mqtt
import Mqtt.Spec.Defs
import Mqtt.Proofs.Sound

namespace Mqtt.Proofs

open Mqtt

/-! ## The byte count of a variable byte integer -/

/-- The printer writes a value below 2^28 in `Mqtt.Spec.vbiSize`
    bytes. -/
theorem printVBI_length (n : Nat) (hn : n < 268435456) :
    (printVBI n).length = Mqtt.Spec.vbiSize n := by
  unfold Mqtt.Spec.vbiSize
  rw [printVBI_def]
  by_cases h1 : n < 128
  · simp [h1]
  rw [ite_eq_right h1, ite_eq_right h1, List.length_cons, printVBI_def]
  by_cases h2 : n < 16384
  · rw [ite_eq_left (by omega : n / 128 < 128), ite_eq_left h2]; rfl
  rw [ite_eq_right (by omega : ¬ n / 128 < 128), ite_eq_right h2, List.length_cons,
    printVBI_def]
  by_cases h3 : n < 2097152
  · rw [ite_eq_left (by omega : n / 128 / 128 < 128), ite_eq_left h3]; rfl
  rw [ite_eq_right (by omega : ¬ n / 128 / 128 < 128), ite_eq_right h3,
    List.length_cons, printVBI_def, ite_eq_left (by omega : n / 128 / 128 / 128 < 128)]
  rfl

/-- What the variable byte integer reader accepts takes exactly
    `Mqtt.Spec.vbiSize` bytes of its value: it is the printer's
    writing (`decVBI_canonical`), whose length is that count. -/
theorem decVBI_length (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) : bs.length = r.length + Mqtt.Spec.vbiSize n := by
  obtain ⟨hn, he⟩ := decVBI_canonical bs n r h
  rw [he, List.length_append, printVBI_length n hn, Nat.add_comm]

/-! ## parse and parsePacket -/

/-- `parse` accepts exactly what `parsePacket` takes whole. -/
theorem parse_iff (bs : List UInt8) (p : Packet) :
    parse bs = some p ↔ parsePacket bs = some (p, []) := by
  unfold parse
  constructor
  · intro h
    split at h
    · rename_i q heq
      cases h; exact heq
    · cases h
  · intro h
    rw [h]

/-! ## Header bytes -/

/-- A PUBLISH header byte with QoS at most 2 and DUP clear at
    QoS 0 is on the list. -/
theorem pubHeader_mem (dup retain : Bool) (qos : Nat) (hq : qos ≤ 2)
    (hd : qos = 0 → dup = false) :
    (0x30 + (if dup then 8 else 0) + qos * 2 + (if retain then 1 else 0)).toUInt8
      ∈ Mqtt.Spec.headerBytes := by
  have : qos = 0 ∨ qos = 1 ∨ qos = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [hd rfl]; cases retain <;> decide
  · cases dup <;> cases retain <;> decide
  · cases dup <;> cases retain <;> decide

/-- The printer's header byte of a well formed packet is on the
    list `Mqtt.Spec.headerBytes`. -/
theorem header_mem (p : Packet) (h : PacketWF p) : headerOf p ∈ Mqtt.Spec.headerBytes := by
  cases p with
  | publish m =>
    obtain ⟨hq, -, -, -, -, hd⟩ := (h.1 : PublishWF m)
    exact pubHeader_mem m.dup m.retain m.qos hq hd
  | connect c => show (0x10 : UInt8) ∈ Mqtt.Spec.headerBytes; decide
  | subscribe => show (0x82 : UInt8) ∈ Mqtt.Spec.headerBytes; decide
  | suback => show (0x90 : UInt8) ∈ Mqtt.Spec.headerBytes; decide
  | pingreq => decide
  | pingresp => decide
  | disconnect => show (0xE0 : UInt8) ∈ Mqtt.Spec.headerBytes; decide

/-- What the stream reader takes starts with a header byte on
    the list: it is a printing (`parsePacket_inv`). -/
theorem header_rule (bs : List UInt8) (p : Packet) (r : List UInt8)
    (h : parsePacket bs = some (p, r)) :
    ∃ b tl, bs = b :: tl ∧ b ∈ Mqtt.Spec.headerBytes := by
  obtain ⟨hwf, he⟩ := parsePacket_inv bs p r h
  refine ⟨headerOf p, (printVBI (bodyOf p).length ++ bodyOf p) ++ r, ?_, header_mem p hwf⟩
  rw [he]; rfl

/-! ## Empty bodies -/

/-- A PINGREQ or PINGRESP the stream reader takes is its
    two byte printing. -/
theorem empty_body_rule (bs r : List UInt8) :
    (parsePacket bs = some (.pingreq, r) → bs = [192, 0] ++ r)
    ∧ (parsePacket bs = some (.pingresp, r) → bs = [208, 0] ++ r) := by
  constructor
  · intro h
    rw [(parsePacket_inv bs _ r h).2, (by decide +kernel : print .pingreq = [192, 0])]
  · intro h
    rw [(parsePacket_inv bs _ r h).2, (by decide +kernel : print .pingresp = [208, 0])]

/-! ## CONNECT -/

/-- A CONNECT the stream reader takes is its printing, whose
    body starts with the protocol name, the level and the flags
    byte `connectFlags_facts` describes. -/
theorem connect_rule (bs r : List UInt8) (c : Connect)
    (h : parsePacket bs = some (.connect c, r)) :
    (∃ (f : UInt8) (tail : List UInt8),
      bs = 16 :: (printVBI (8 + tail.length) ++ ([0, 4, 77, 81, 84, 84, 5, f] ++ tail)) ++ r
      ∧ Mqtt.Spec.ConnectFlagsRule f.toNat)
    ∧ ∀ w, c.will = some w → w.topic ≠ [] ∧ Mqtt.Spec.TopicNameRule w.topic := by
  obtain ⟨hwf, he⟩ := parsePacket_inv bs _ r h
  have hc : ConnectWF c := hwf.1
  obtain ⟨f1, f2, f3, -, -, -, f7, -, f9⟩ := connectFlags_facts c hc
  refine ⟨⟨(connectFlags c).toUInt8, writeBE 2 c.keepAlive ++ (printProps c.props
    ++ (printStr c.clientId ++ (printWillPart c.will ++ (printOptStr c.username
    ++ printOptBin c.password)))), ?_, ?_⟩, ?_⟩
  · rw [he]
    show (16 : UInt8) :: (printVBI (printConnectBody c).length ++ printConnectBody c) ++ r = _
    have hb : printConnectBody c = [0, 4, 77, 81, 84, 84, 5, (connectFlags c).toUInt8]
        ++ (writeBE 2 c.keepAlive ++ (printProps c.props
        ++ (printStr c.clientId ++ (printWillPart c.will ++ (printOptStr c.username
        ++ printOptBin c.password))))) := by
      unfold printConnectBody
      rfl
    rw [hb]
    simp only [List.length_append, List.length_cons, List.length_nil]
  · rw [f1]
    refine ⟨f2, ?_, ?_⟩
    · rw [f3]
      cases hw : c.will with
      | none => simp
      | some w =>
        have := (hc.2.2.2.1 w hw).1
        simp only []
        omega
    · intro hb
      apply f9
      have : flagBit (connectFlags c) 2 = false := by
        unfold flagBit; simp; omega
      rw [f7] at this
      cases hw : c.will with
      | none => rfl
      | some w => rw [hw] at this; cases this
  · intro w hw
    have := (hc.2.2.2.1 w hw).2.2.1
    exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩

/-! ## PUBLISH -/

/-- `hasTopicAlias` finds a property with identifier 0x23. -/
theorem hasTopicAlias_true {ps : List Property} (h : hasTopicAlias ps = true) :
    ∃ q ∈ ps, q.id = 0x23 := by
  unfold hasTopicAlias at h
  obtain ⟨q, hq, he⟩ := List.any_eq_true.mp h
  exact ⟨q, hq, by simpa using he⟩

/-- A PUBLISH the stream reader takes is well formed, and
    `PublishWF` gives the topic and identifier rules. -/
theorem publish_rule (bs r : List UInt8) (m : Publish)
    (h : parsePacket bs = some (.publish m, r)) :
    Mqtt.Spec.TopicNameRule m.topic ∧ (m.topic = [] → ∃ q ∈ m.props, q.id = 0x23)
    ∧ (m.packetId = none ↔ m.qos = 0) ∧ (∀ i, m.packetId = some i → i ≠ 0) := by
  obtain ⟨hwf, -⟩ := parsePacket_inv bs _ r h
  obtain ⟨hq, ht, hid, hnone, -, -⟩ := (hwf.1 : PublishWF m)
  obtain ⟨-, hp, hh, ha⟩ := ht
  refine ⟨⟨hp, hh⟩, fun e => hasTopicAlias_true (ha e), ⟨hnone, ?_⟩, ?_⟩
  · intro h0
    cases hpid : m.packetId with
    | none => rfl
    | some i =>
      have := (hid i hpid).2.2
      omega
  · intro i hi
    have := (hid i hi).1
    omega

/-! ## Property blocks -/

/-- Every property of a well formed list is allowed on its block,
    has its table type, and keeps `propValOK`. -/
theorem propsWF_mem : ∀ (s : PropSet) (seen : List Nat) (ps : List Property),
    PropsWF s seen ps → ∀ q ∈ ps, q.id ∈ allowedOf s
      ∧ propTypeOf q.id = some (valType q.val) ∧ propValOK q.id q.val = true
  | _, _, [], _, q, hq => by cases hq
  | s, seen, p :: ps, h, q, hq => by
    rw [PropsWF] at h
    obtain ⟨h1, h2, -, h4, -, h6⟩ := h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨h1, h2, h4⟩
    · exact propsWF_mem s _ ps h6 q hq

/-- In a well formed list, a single use identifier already seen
    does not stand again, and stands at most once. -/
theorem propsWF_count : ∀ (s : PropSet) (seen : List Nat) (ps : List Property),
    PropsWF s seen ps → ∀ i, repeatableIn s i = false →
      (i ∈ seen → i ∉ ps.map Property.id) ∧ (ps.map Property.id).count i ≤ 1
  | _, _, [], _, i, _ => by simp
  | s, seen, p :: ps, h, i, hi => by
    rw [PropsWF] at h
    obtain ⟨-, -, -, -, h5, h6⟩ := h
    obtain ⟨ih1, ih2⟩ := propsWF_count s (p.id :: seen) ps h6 i hi
    by_cases he : p.id = i
    · subst he
      have hns : p.id ∉ seen := by
        rcases h5 with h5 | h5
        · rw [hi] at h5; cases h5
        · exact h5
      refine ⟨fun hm => absurd hm hns, ?_⟩
      have h0 : (ps.map Property.id).count p.id = 0 :=
        List.count_eq_zero.mpr (ih1 (List.mem_cons_self ..))
      simp [h0]
    · refine ⟨fun hm => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨fun e => he e.symm, ih1 (List.mem_cons_of_mem _ hm)⟩
      · simp only [List.map_cons, List.count_cons]
        have : (p.id == i) = false := by simpa using he
        simp [this, ih2]

/-- The table type and `propValOK` of an allowed identifier give
    `Mqtt.Spec.ValueRule`, by cases on the identifier. -/
theorem valueRule_of (s : PropSet) (q : Property) (h1 : q.id ∈ allowedOf s)
    (h2 : propTypeOf q.id = some (valType q.val)) (h3 : propValOK q.id q.val = true) :
    Mqtt.Spec.ValueRule q.id q.val := by
  obtain ⟨i, v⟩ := q
  dsimp only at h1 h2 h3 ⊢
  have hi : i = 0x01 ∨ i = 0x02 ∨ i = 0x03 ∨ i = 0x08 ∨ i = 0x09 ∨ i = 0x0B ∨ i = 0x11
      ∨ i = 0x15 ∨ i = 0x16 ∨ i = 0x17 ∨ i = 0x18 ∨ i = 0x19 ∨ i = 0x1C ∨ i = 0x1F
      ∨ i = 0x21 ∨ i = 0x22 ∨ i = 0x23 ∨ i = 0x26 ∨ i = 0x27 := by
    cases s <;> simp [allowedOf] at h1 <;> omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases v <;> simp_all [propTypeOf, valType, propValOK, Mqtt.Spec.ValueRule, Mqtt.Spec.TopicNameRule]

/-- A well formed property block keeps `Mqtt.Spec.BlockRule`. -/
theorem blockRule_of_wf (s : PropSet) (ps : List Property) (h : PropsBlockWF s ps) :
    Mqtt.Spec.BlockRule s ps := by
  obtain ⟨hw, -, ha⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := propsWF_mem s [] ps hw q hq
    refine ⟨?_, valueRule_of s q h1 h2 h3⟩
    cases s <;> exact h1
  · intro i hi
    have : repeatableIn s i = false := by
      unfold Mqtt.Spec.MayRepeat at hi
      unfold repeatableIn
      cases s <;> simp_all
    exact (propsWF_count s [] ps hw i this).2
  · rintro ⟨q, hq, he⟩
    unfold authOK at ha
    have h16 : ps.any (fun p => p.id == 0x16) = true :=
      List.any_eq_true.mpr ⟨q, hq, by simp [he]⟩
    rw [h16] at ha
    simp only [Bool.not_true, Bool.false_or] at ha
    obtain ⟨q', hq', he'⟩ := List.any_eq_true.mp ha
    exact ⟨q', hq', by simpa using he'⟩

/-- Every block of a packet the stream reader takes is well
    formed, so it keeps `Mqtt.Spec.BlockRule`. -/
theorem property_rule (bs r : List UInt8) (p : Packet)
    (h : parsePacket bs = some (p, r)) :
    ∀ b ∈ Mqtt.Spec.blocks p, Mqtt.Spec.BlockRule b.1 b.2 := by
  obtain ⟨hwf, -⟩ := parsePacket_inv bs p r h
  intro b hb
  cases p with
  | connect c =>
    have hc : ConnectWF c := hwf.1
    simp only [Mqtt.Spec.blocks] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact blockRule_of_wf _ _ hc.2.1
    · cases hw : c.will with
      | none => rw [hw] at hb; cases hb
      | some w =>
        rw [hw] at hb
        rcases List.mem_singleton.mp hb with rfl
        exact blockRule_of_wf _ _ (hc.2.2.2.1 w hw).2.1
  | publish m =>
    rcases List.mem_singleton.mp hb with rfl
    exact blockRule_of_wf _ _ (hwf.1 : PublishWF m).2.2.2.2.1
  | subscribe id ps fs =>
    rcases List.mem_singleton.mp hb with rfl
    exact blockRule_of_wf _ _ hwf.1.2.2.1
  | suback id ps rs =>
    rcases List.mem_singleton.mp hb with rfl
    exact blockRule_of_wf _ _ hwf.1.2.2.1
  | pingreq => cases hb
  | pingresp => cases hb
  | disconnect x =>
    rcases x with _ | ⟨rc, _ | ps⟩
    · cases hb
    · cases hb
    · rcases List.mem_singleton.mp hb with rfl
      exact blockRule_of_wf _ _ hwf.1.2

/-! ## Topic filters -/

/-- The code's level splitter is the standard library's
    `List.splitOn '/'`. -/
theorem splitLevels_eq : ∀ f : List Char, splitLevels f = f.splitOn '/'
  | [] => by simp [splitLevels]
  | c :: cs => by
    rw [List.splitOn_cons_eq_ite_modifyHead, splitLevels, ← splitLevels_eq cs]
    by_cases h : c = '/'
    · simp [h]
    · have hne : splitLevels cs ≠ [] := by
        rw [splitLevels_eq cs]; exact List.splitOn_ne_nil _ _
      rw [ite_eq_right h]
      have hb : (c == '/') = false := by simpa using h
      rw [hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hs : splitLevels cs with
      | nil => exact absurd hs hne
      | cons l ls => rfl

/-- A level other than the last that passes `levelOK` is `+`
    alone or holds no wildcard. -/
theorem levelOK_facts {l : List Char} (h : levelOK l = true) :
    ('+' ∈ l → l = ['+']) ∧ '#' ∉ l := by
  unfold levelOK at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at h
  rcases h with rfl | ⟨h1, h2⟩
  · exact ⟨fun _ => rfl, by simp⟩
  · exact ⟨fun hm => absurd hm h2, h1⟩

/-- Levels that pass `levelsOK` keep `Mqtt.Spec.WildcardRule`. -/
theorem wildcardRule_of : ∀ ls : List (List Char), levelsOK ls = true → Mqtt.Spec.WildcardRule ls
  | [], _ => fun i hi => absurd hi (by simp)
  | [l], h => by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simp only [List.getElem_cons_zero, List.length_cons, List.length_nil]
    simp only [levelsOK, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨fun hm => by simp at hm, fun _ => by simp⟩
    · obtain ⟨h1, h2⟩ := levelOK_facts h
      exact ⟨h1, fun hm => absurd hm h2⟩
  | l :: l2 :: ls, h => by
    simp only [levelsOK, Bool.and_eq_true] at h
    obtain ⟨hl, hrest⟩ := h
    have ih := wildcardRule_of (l2 :: ls) hrest
    intro i hi
    cases i with
    | zero =>
      obtain ⟨h1, h2⟩ := levelOK_facts hl
      exact ⟨h1, fun hm => absurd hm h2⟩
    | succ i =>
      have hi' : i < (l2 :: ls).length := by simp at hi ⊢; omega
      obtain ⟨h1, h2⟩ := ih i hi'
      simp only [List.getElem_cons_succ, List.length_cons] at h1 h2 ⊢
      exact ⟨h1, fun hm => ⟨(h2 hm).1, by have := (h2 hm).2; omega⟩⟩

/-- A filter that passes `plainFilterOK` keeps
    `Mqtt.Spec.PlainFilterRule`. -/
theorem plainRule_of (f : List Char) (h : plainFilterOK f = true) : Mqtt.Spec.PlainFilterRule f := by
  unfold plainFilterOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  exact ⟨h.1, by rw [← splitLevels_eq]; exact wildcardRule_of _ h.2⟩

/-- When `shareSplit` finds a `/`, the text is the ShareName, the
    `/` and the rest, and the ShareName holds no `/`. -/
theorem shareSplit_some : ∀ (r name flt : List Char),
    shareSplit r = (name, some flt) → r = name ++ '/' :: flt ∧ '/' ∉ name
  | [], name, flt, h => by simp [shareSplit] at h
  | c :: cs, name, flt, h => by
    unfold shareSplit at h
    by_cases hc : c = '/'
    · rw [ite_eq_left hc] at h
      cases h
      subst hc
      exact ⟨rfl, by simp⟩
    · rw [ite_eq_right hc] at h
      cases hs : shareSplit cs with
      | mk n r =>
        rw [hs] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := shareSplit_some cs n flt hs
        refine ⟨by rw [h1]; rfl, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hc e.symm, h2⟩

/-- A filter that passes `filterOK` keeps `Mqtt.Spec.FilterRule`. -/
theorem filterRule_of (f : List Char) (o : SubOpts) (h : filterOK f o = true) :
    Mqtt.Spec.FilterRule f o := by
  by_cases hp : Mqtt.Spec.sharePrefix <+: f
  · obtain ⟨r, rfl⟩ := hp
    refine ⟨fun _ => ?_, fun hn => absurd (List.prefix_append _ _) hn⟩
    have h' : (match shareSplit r with
        | (name, some flt) =>
          !name.isEmpty && !name.contains '+' && !name.contains '#'
            && plainFilterOK flt && !o.noLocal
        | (_, none) => false) = true := h
    cases hs : shareSplit r with
    | mk name rest =>
      cases rest with
      | none => rw [hs] at h'; cases h'
      | some flt =>
        rw [hs] at h'
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.contains_eq_mem, decide_eq_false_iff_not] at h'
        obtain ⟨⟨⟨⟨hn, hplus⟩, hhash⟩, hplain⟩, hnl⟩ := h'
        obtain ⟨hr, hslash⟩ := shareSplit_some r name flt hs
        exact ⟨name, flt, by rw [hr, List.append_assoc], hn, hslash, hplus, hhash,
          plainRule_of flt hplain, hnl⟩
  · refine ⟨fun hp' => absurd hp' hp, fun _ => ?_⟩
    unfold filterOK at h
    split at h
    · exact absurd ⟨_, rfl⟩ hp
    · exact plainRule_of f h

/-- Every filter of a well formed filter list keeps
    `Mqtt.Spec.FilterRule`. -/
theorem filtersWF_rule : ∀ (fs : List (List Char × SubOpts)), FiltersWF fs →
    ∀ fo ∈ fs, Mqtt.Spec.FilterRule fo.1 fo.2
  | [], _, fo, hfo => by cases hfo
  | (f, o) :: gs, h, fo, hfo => by
    obtain ⟨-, -, hok, hrest⟩ := h
    rcases List.mem_cons.mp hfo with rfl | hfo
    · exact filterRule_of f o hok
    · exact filtersWF_rule gs hrest fo hfo

/-- A SUBSCRIBE the stream reader takes is well formed, so its
    identifier, filter list and filters keep the rules. -/
theorem subscribe_rule (bs r : List UInt8) (i : Nat) (ps : List Property)
    (fs : List (List Char × SubOpts)) (h : parsePacket bs = some (.subscribe i ps fs, r)) :
    i ≠ 0 ∧ fs ≠ [] ∧ ∀ fo ∈ fs, Mqtt.Spec.FilterRule fo.1 fo.2 := by
  obtain ⟨hwf, -⟩ := parsePacket_inv bs _ r h
  obtain ⟨h1, -, -, h4, h5⟩ := hwf.1
  exact ⟨by omega, h4, filtersWF_rule fs h5⟩

end Mqtt.Proofs
