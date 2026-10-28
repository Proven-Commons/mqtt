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

/-! ## The fixed header byte -/

/-- The fixed header bytes a packet of this slice may start with
    (sections 2.1.2 and 2.1.3, Tables 2-1 and 2-2, and section
    3.3.1): CONNECT 0x10, SUBSCRIBE 0x82 (flags 0010), SUBACK
    0x90, PINGREQ 0xC0, PINGRESP 0xD0 and DISCONNECT 0xE0, whose
    flags are fixed [MQTT-2.1.3-1]; and the PUBLISH bytes 0x30 to 0x3D whose QoS
    bits (2 and 1) are not the reserved value 3 [MQTT-3.3.1-4]
    and whose DUP bit (3) is clear at QoS 0 [MQTT-3.3.1-2]. Any
    other first byte, including every packet type outside the
    seven of this slice, is not on the list. -/
def headerBytes : List UInt8 :=
  [0x10,
   0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x3A, 0x3B, 0x3C, 0x3D,
   0x82, 0x90, 0xC0, 0xD0, 0xE0]

/-! ## CONNECT -/

/-- The rules on the CONNECT flags byte `f` (section 3.1.2.3):
    the reserved bit 0 is clear [MQTT-3.1.2-3]; the will QoS
    field, bits 4 and 3, is not 3 [MQTT-3.1.2-12]; and when the
    will flag, bit 2, is clear, the will QoS and will retain
    bits, 3 to 5, are all clear [MQTT-3.1.2-11] [MQTT-3.1.2-13]. -/
def ConnectFlagsRule (f : Nat) : Prop :=
  f % 2 = 0 ∧ f / 8 % 4 ≠ 3 ∧ (f / 4 % 2 = 0 → f / 8 % 8 = 0)

/-! ## Topic names -/

/-- A Topic Name holds neither wildcard character, `+` or `#`
    (section 4.7.1, [MQTT-3.3.2-2]). Whether it may be empty
    depends on where it stands, so that is said beside each use. -/
def TopicNameRule (s : List Char) : Prop :=
  '+' ∉ s ∧ '#' ∉ s

/-! ## Properties -/

/-- The property identifiers each property block of this slice
    may carry, from the packet column of the standard's property
    table (section 2.2.2, Table 2-4). The will block is the
    will properties inside a CONNECT payload (section 3.1.3.2). -/
def allowedIds : PropSet → List Nat
  | .connect => [0x11, 0x15, 0x16, 0x17, 0x19, 0x21, 0x22, 0x26, 0x27]
  | .will => [0x01, 0x02, 0x03, 0x08, 0x09, 0x18, 0x26]
  | .publish => [0x01, 0x02, 0x03, 0x08, 0x09, 0x0B, 0x23, 0x26]
  | .subscribe => [0x0B, 0x26]
  | .suback => [0x1F, 0x26]
  | .disconnect => [0x11, 0x1C, 0x1F, 0x26]

/-- A property value keeps the standard's rules for its
    identifier: it has the value type of the identifier's row in
    Table 2-4, and the value is not one the standard calls a
    Protocol Error. Only the identifiers some block of this slice
    allows are listed; any other identifier fails.

    - Response Topic (0x08) is used as a Topic Name, so it is not
      empty and holds no wildcard (sections 3.3.2.3.5
      [MQTT-3.3.2-14] and 4.7).
    - Subscription Identifier (0x0B) is not 0 (sections 3.3.2.3.8
      and 3.8.2.1.2).
    - Request Problem Information (0x17) and Request Response
      Information (0x19) are 0 or 1 (sections 3.1.2.11.7 and
      3.1.2.11.6).
    - Receive Maximum (0x21) is not 0 (section 3.1.2.11.3).
    - Topic Alias (0x23) is not 0 (section 3.3.2.3.4,
      [MQTT-3.3.2-8]).
    - Maximum Packet Size (0x27) is not 0 (section 3.1.2.11.4). -/
def ValueRule : Nat → PropVal → Prop
  | 0x01, .byte _ => True                         -- Payload Format Indicator
  | 0x02, .fourByte _ => True                     -- Message Expiry Interval
  | 0x03, .utf8 _ => True                         -- Content Type
  | 0x08, .utf8 s => s ≠ [] ∧ TopicNameRule s     -- Response Topic
  | 0x09, .binary _ => True                       -- Correlation Data
  | 0x0B, .varByte n => n ≠ 0                     -- Subscription Identifier
  | 0x11, .fourByte _ => True                     -- Session Expiry Interval
  | 0x15, .utf8 _ => True                         -- Authentication Method
  | 0x16, .binary _ => True                       -- Authentication Data
  | 0x17, .byte n => n ≤ 1                        -- Request Problem Information
  | 0x18, .fourByte _ => True                     -- Will Delay Interval
  | 0x19, .byte n => n ≤ 1                        -- Request Response Information
  | 0x1C, .utf8 _ => True                         -- Server Reference
  | 0x1F, .utf8 _ => True                         -- Reason String
  | 0x21, .twoByte n => n ≠ 0                     -- Receive Maximum
  | 0x22, .twoByte _ => True                      -- Topic Alias Maximum
  | 0x23, .twoByte n => n ≠ 0                     -- Topic Alias
  | 0x26, .utf8Pair _ _ => True                   -- User Property
  | 0x27, .fourByte n => n ≠ 0                    -- Maximum Packet Size
  | _, _ => False

/-- The properties that may stand more than once in one block:
    the User Property (0x26) anywhere it is allowed (section
    3.1.2.11.8 and the like), and the Subscription Identifier
    (0x0B) on PUBLISH, which carries one per matching
    subscription (section 3.3.2.3.8). Every other property is
    single use: "It is a Protocol Error to include" it "more than
    once". -/
def MayRepeat (s : PropSet) (i : Nat) : Prop :=
  i = 0x26 ∨ (i = 0x0B ∧ s = .publish)

/-- The rules on one property block of kind `s`: every property
    is allowed on the block and keeps `ValueRule`; no single use
    identifier stands more than once; and Authentication Data
    (0x16) stands only with an Authentication Method (0x15)
    (section 3.1.2.11.10). -/
def BlockRule (s : PropSet) (ps : List Property) : Prop :=
  (∀ q ∈ ps, q.id ∈ allowedIds s ∧ ValueRule q.id q.val)
  ∧ (∀ i, ¬ MayRepeat s i → (ps.map Property.id).count i ≤ 1)
  ∧ ((∃ q ∈ ps, q.id = 0x16) → ∃ q ∈ ps, q.id = 0x15)

/-- Every property block a packet carries, with its kind: the
    CONNECT block and, when a will stands, the will block; the
    PUBLISH, SUBSCRIBE and SUBACK blocks; and the DISCONNECT
    block when the body carries one. -/
def blocks : Packet → List (PropSet × List Property)
  | .connect c =>
    (.connect, c.props) :: (match c.will with
      | some w => [(.will, w.props)]
      | none => [])
  | .publish p => [(.publish, p.props)]
  | .subscribe _ ps _ => [(.subscribe, ps)]
  | .suback _ ps _ => [(.suback, ps)]
  | .disconnect (some (_, some ps)) => [(.disconnect, ps)]
  | _ => []

/-! ## Topic filters -/

/-- The wildcard rules over the levels of a topic filter, the
    filter split at each `/` (section 4.7.1.1): a level that
    holds `+` is `+` alone [MQTT-4.7.1-2], and a level that holds
    `#` is `#` alone and is the last level [MQTT-4.7.1-1]. -/
def WildcardRule (ls : List (List Char)) : Prop :=
  ∀ (i : Nat) (h : i < ls.length),
    ('+' ∈ ls[i] → ls[i] = ['+']) ∧ ('#' ∈ ls[i] → ls[i] = ['#'] ∧ i + 1 = ls.length)

/-- A topic filter outside a shared subscription: at least one
    character long [MQTT-4.7.3-1], and its levels, split at each
    `/` by the standard library's `List.splitOn`, keep the
    wildcard rules. -/
def PlainFilterRule (f : List Char) : Prop :=
  f ≠ [] ∧ WildcardRule (f.splitOn '/')

/-- The text that starts a shared subscription's filter. -/
def sharePrefix : List Char := ['$', 's', 'h', 'a', 'r', 'e', '/']

/-- The rules on a SUBSCRIBE topic filter `f` with options `o`.
    A filter that starts with `$share/` is a shared subscription
    (section 4.8.2): after `$share/` comes a ShareName at least
    one character long that holds no `/`, `+` or `#`
    [MQTT-4.8.2-1] [MQTT-4.8.2-2], then a `/` and a filter that
    keeps the plain rules; and its No Local option is clear
    [MQTT-3.8.3-4]. Any other filter keeps the plain rules. -/
def FilterRule (f : List Char) (o : SubOpts) : Prop :=
  (sharePrefix <+: f → ∃ name flt, f = sharePrefix ++ name ++ '/' :: flt
      ∧ name ≠ [] ∧ '/' ∉ name ∧ '+' ∉ name ∧ '#' ∉ name
      ∧ PlainFilterRule flt ∧ o.noLocal = false)
  ∧ (¬ sharePrefix <+: f → PlainFilterRule f)

end Spec
