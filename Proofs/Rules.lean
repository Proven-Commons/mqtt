/-
  Proofs of the statements in `Spec.lean` whose rule text stands
  in `Spec/Defs.lean`, part of the specification.

  Each proof starts from what the reader is already proved to
  accept (`parsePacket_inv` in `Proofs/Sound.lean`, and
  `decVBI_canonical` in `Proofs/RoundTrip.lean`) and shows that the
  rule written in the specification holds for it.
-/

import Mqtt
import Spec.Defs
import Proofs.Sound

namespace Mqtt.Proofs

open Mqtt

/-! ## The byte count of a variable byte integer -/

/-- The printer writes a value below 2^28 in `Spec.vbiSize`
    bytes. -/
theorem printVBI_length (n : Nat) (hn : n < 268435456) :
    (printVBI n).length = Spec.vbiSize n := by
  unfold Spec.vbiSize
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
    `Spec.vbiSize` bytes of its value: it is the printer's
    writing (`decVBI_canonical`), whose length is that count. -/
theorem decVBI_length (bs : List UInt8) (n : Nat) (r : List UInt8)
    (h : decVBI bs = some (n, r)) : bs.length = r.length + Spec.vbiSize n := by
  obtain ⟨hn, he⟩ := decVBI_canonical bs n r h
  rw [he, List.length_append, printVBI_length n hn, Nat.add_comm]

end Mqtt.Proofs
