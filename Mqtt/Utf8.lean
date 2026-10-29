/-
  UTF-8, by hand: MQTT strings travel on the wire as bytes, and
  the string fields in this slice are held as lists of
  characters, so the packet code needs both directions between
  characters and bytes.

  The encoder writes the standard one to four bytes per
  character. The decoder is strict. It turns away stray
  continuation bytes, overlong forms (a character written with
  more bytes than it needs, including any lead byte below C2),
  lead bytes above F4, encodings of the surrogate values D800 to
  DFFF, values above 10FFFF, and truncated sequences.

  This file is copied from Jws/Utf8.lean in Proven-Commons/jws#2,
  a draft pull request that is not merged (jws main has no such
  file), with the namespace renamed. The repos in this programme
  do not share a library, so the code travels. Its proof is
  included here, in Proofs/Utf8.lean.
-/

namespace Mqtt.Utf8

/-- The bytes of one character. -/
def encodeChar (c : Char) : List UInt8 :=
  let n := c.toNat
  if n < 0x80 then [n.toUInt8]
  else if n < 0x800 then
    [(0xC0 + n / 64).toUInt8, (0x80 + n % 64).toUInt8]
  else if n < 0x10000 then
    [(0xE0 + n / 4096).toUInt8, (0x80 + (n / 64) % 64).toUInt8, (0x80 + n % 64).toUInt8]
  else
    [(0xF0 + n / 262144).toUInt8, (0x80 + (n / 4096) % 64).toUInt8,
     (0x80 + (n / 64) % 64).toUInt8, (0x80 + n % 64).toUInt8]

/-- The bytes of a text. -/
def encode (cs : List Char) : List UInt8 :=
  cs.flatMap encodeChar

/-- The payload bits of a continuation byte (80 to BF). -/
def contVal (b : UInt8) : Option Nat :=
  if 0x80 ≤ b.toNat ∧ b.toNat < 0xC0 then some (b.toNat - 0x80) else none

/-- Strict decoding. The side conditions on the three and four
    byte forms are the overlong, surrogate, and range rules:
    after E0 the first continuation value is at least 32, after
    ED it is below 32, after F0 it is at least 16, after F4 it
    is below 16. -/
def decode : List UInt8 → Option (List Char)
  | [] => some []
  | b :: rest =>
    if b.toNat < 0x80 then
      (decode rest).map fun cs => Char.ofNat b.toNat :: cs
    else if b.toNat < 0xC2 then none
    else if b.toNat < 0xE0 then
      match rest with
      | b1 :: rest1 =>
        match contVal b1 with
        | some v1 => (decode rest1).map fun cs =>
            Char.ofNat ((b.toNat - 0xC0) * 64 + v1) :: cs
        | none => none
      | [] => none
    else if b.toNat < 0xF0 then
      match rest with
      | b1 :: b2 :: rest1 =>
        match contVal b1, contVal b2 with
        | some v1, some v2 =>
          if (b.toNat = 0xE0 → 0x20 ≤ v1) ∧ (b.toNat = 0xED → v1 < 0x20) then
            (decode rest1).map fun cs =>
              Char.ofNat ((b.toNat - 0xE0) * 4096 + v1 * 64 + v2) :: cs
          else none
        | _, _ => none
      | _ => none
    else if b.toNat < 0xF5 then
      match rest with
      | b1 :: b2 :: b3 :: rest1 =>
        match contVal b1, contVal b2, contVal b3 with
        | some v1, some v2, some v3 =>
          if (b.toNat = 0xF0 → 0x10 ≤ v1) ∧ (b.toNat = 0xF4 → v1 < 0x10) then
            (decode rest1).map fun cs =>
              Char.ofNat ((b.toNat - 0xF0) * 262144 + v1 * 4096 + v2 * 64 + v3) :: cs
          else none
        | _, _, _ => none
      | _ => none
    else none

end Mqtt.Utf8
