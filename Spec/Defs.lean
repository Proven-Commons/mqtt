/-
  Definitions the statements in `Spec.lean` use besides the code
  under proof.

  This file is part of the specification, with `Spec.lean` and
  `SPEC.md`: `bar.toml` lists it among the spec files, so an
  approval covers its text. Each definition here is written from
  the MQTT 5.0 standard (OASIS Standard, 7 March 2019; section
  numbers below are that standard's), not from the reader in
  `Mqtt/Parse.lean` or the well formedness rules in
  `Mqtt/Value.lean`. The proofs show that what the reader accepts
  keeps these definitions.
-/

import Mqtt

namespace Spec

open Mqtt

/-! ## Variable byte integers -/

/-- The number of bytes in the shortest variable byte integer
    writing of `n` (sections 1.5.5 and 2.1.4). Each byte carries
    seven bits of the value, so one byte carries values below
    2^7 = 128, two bytes below 2^14 = 16384, three bytes below
    2^21 = 2097152, and four bytes below 2^28, the largest value
    the format allows. -/
def vbiSize (n : Nat) : Nat :=
  if n < 128 then 1 else if n < 16384 then 2 else if n < 2097152 then 3 else 4

end Spec
