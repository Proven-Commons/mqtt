/-
  MQTT 5.0 packet values and the printer.

  A packet is one of the seven control packet types this slice
  covers: CONNECT, PUBLISH, SUBSCRIBE, SUBACK, PINGREQ,
  PINGRESP, and DISCONNECT. The printer writes a packet as the
  fixed header byte, the remaining length as a variable byte
  integer, and the body: the variable header and payload for the
  packet's type.

  Properties are held as an identifier and a typed value. The
  value type of an identifier is fixed by the specification's
  property table (section 2.2.2, Table 2-4), which also says
  which packets a property may appear on. Will properties, the
  property block inside a CONNECT packet's will, count as their
  own packet kind for that table, as the specification's table
  lists them on their own line.

  Strings are held as lists of characters. What a string means
  as bytes is settled by the strict UTF-8 codec in Mqtt/Utf8.
-/

import Mqtt.Utf8

namespace Mqtt

/-! ## Big endian byte strings -/

/-- Write a number in exactly `k` bytes, most significant byte
    first. Bytes past the number's own width are zero, and a
    number too wide for `k` bytes loses its top bytes: the
    printer only calls this with a width the number fits. -/
def writeBE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => ((n / 256 ^ k) % 256).toUInt8 :: writeBE k (n % 256 ^ k)

/-- The unfolding rule for `writeBE` at a successor width. -/
theorem writeBE_succ (k n : Nat) :
    writeBE (k + 1) n = ((n / 256 ^ k) % 256).toUInt8 :: writeBE k (n % 256 ^ k) := by
  rw [writeBE]

/-- A big endian writing is exactly as long as its width. -/
theorem writeBE_length : ∀ (k n : Nat), (writeBE k n).length = k
  | 0, _ => rfl
  | k + 1, n => by rw [writeBE_succ]; simp [writeBE_length k]

/-! ## The variable byte integer -/

/-- Write a number as a variable byte integer (section 2.1.4):
    seven bits per byte, low groups first, the top bit of each
    byte but the last set as a continuation mark. The format
    carries at most four bytes, so numbers below 2^28 are the
    ones it can carry. This function has no cap: a number of
    2^28 or more gets a writing of five or more bytes, which
    the reader refuses. The well formedness rules below keep
    every written number under the bound. -/
def printVBI (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else (128 + n % 128).toUInt8 :: printVBI (n / 128)
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

/-- The unfolding rule for `printVBI`. -/
theorem printVBI_def (n : Nat) :
    printVBI n = if n < 128 then [n.toUInt8]
      else (128 + n % 128).toUInt8 :: printVBI (n / 128) := by
  rw [printVBI]

/-! ## Properties: the table -/

/-- The value type of a property, as the specification's
    property table gives it. -/
inductive PropType where
  | byte : PropType
  | twoByte : PropType
  | fourByte : PropType
  | varByte : PropType
  | utf8 : PropType
  | utf8Pair : PropType
  | binary : PropType
  deriving DecidableEq, Repr

/-- A property value, in the shape of its type. Strings are
    lists of characters; binary data is a list of bytes. -/
inductive PropVal where
  | byte (n : Nat) : PropVal
  | twoByte (n : Nat) : PropVal
  | fourByte (n : Nat) : PropVal
  | varByte (n : Nat) : PropVal
  | utf8 (s : List Char) : PropVal
  | utf8Pair (k v : List Char) : PropVal
  | binary (bs : List UInt8) : PropVal
  deriving DecidableEq, Repr

/-- The type of a property value. -/
def valType : PropVal → PropType
  | .byte _ => .byte
  | .twoByte _ => .twoByte
  | .fourByte _ => .fourByte
  | .varByte _ => .varByte
  | .utf8 _ => .utf8
  | .utf8Pair _ _ => .utf8Pair
  | .binary _ => .binary

/-- One property: an identifier and a value. -/
structure Property where
  id : Nat
  val : PropVal
  deriving DecidableEq, Repr

/-- The specification's property table (section 2.2.2,
    Table 2-4): the value type of each identifier the
    specification defines. An identifier the table does not
    list has no type here, and the reader rejects it. -/
def propTypeOf : Nat → Option PropType
  | 0x01 => some .byte
  | 0x02 => some .fourByte
  | 0x03 => some .utf8
  | 0x08 => some .utf8
  | 0x09 => some .binary
  | 0x0B => some .varByte
  | 0x11 => some .fourByte
  | 0x12 => some .utf8
  | 0x13 => some .twoByte
  | 0x15 => some .utf8
  | 0x16 => some .binary
  | 0x17 => some .byte
  | 0x18 => some .fourByte
  | 0x19 => some .byte
  | 0x1A => some .utf8
  | 0x1C => some .utf8
  | 0x1F => some .utf8
  | 0x21 => some .twoByte
  | 0x22 => some .twoByte
  | 0x23 => some .twoByte
  | 0x24 => some .byte
  | 0x25 => some .byte
  | 0x26 => some .utf8Pair
  | 0x27 => some .fourByte
  | 0x28 => some .byte
  | 0x29 => some .byte
  | 0x2A => some .byte
  | _ => none

/-- The places a property block can stand, for the table's
    packet column: the CONNECT packet's own block, the will
    block inside CONNECT, and one block each for PUBLISH,
    SUBSCRIBE, SUBACK, and DISCONNECT. -/
inductive PropSet where
  | connect : PropSet
  | will : PropSet
  | publish : PropSet
  | subscribe : PropSet
  | suback : PropSet
  | disconnect : PropSet
  deriving DecidableEq, Repr

/-- The identifiers the specification's table allows on each
    property block, by the table's packet column. -/
def allowedOf : PropSet → List Nat
  | .connect => [0x11, 0x15, 0x16, 0x17, 0x19, 0x21, 0x22, 0x26, 0x27]
  | .will => [0x01, 0x02, 0x03, 0x08, 0x09, 0x18, 0x26]
  | .publish => [0x01, 0x02, 0x03, 0x08, 0x09, 0x0B, 0x23, 0x26]
  | .subscribe => [0x0B, 0x26]
  | .suback => [0x1F, 0x26]
  | .disconnect => [0x11, 0x1C, 0x1F, 0x26]

/-- May this property appear more than once in one block? The
    user property (0x26) may, wherever it is allowed. The
    subscription identifier (0x0B) may repeat on PUBLISH: a
    server sending one message for several matching
    subscriptions carries one identifier per subscription, and
    the identifiers may be equal (section 3.3.4). Every other
    property is single use: a second copy in one block is
    rejected. -/
def repeatableIn (s : PropSet) (id : Nat) : Bool :=
  id = 0x26 || (id = 0x0B && s = .publish)

/-- The value rules the standard sets on single property
    values, beyond their type. A value that breaks one is a
    Protocol Error:

    - Response Topic (0x08) is used as a Topic Name, so it is
      not empty and holds neither wildcard character (sections
      3.3.2.3.5 [MQTT-3.3.2-14], 4.7.0 [MQTT-4.7.0-1] and
      4.7.3 [MQTT-4.7.3-1]).
    - Subscription Identifier (0x0B) is not 0 (sections
      3.3.2.3.8 and 3.8.2.1.2).
    - Request Problem Information (0x17) and Request Response
      Information (0x19) are 0 or 1 (sections 3.1.2.11.7 and
      3.1.2.11.6).
    - Receive Maximum (0x21) is not 0 (section 3.1.2.11.3).
    - Topic Alias (0x23) is not 0 (section 3.3.2.3.4,
      [MQTT-3.3.2-8]).
    - Maximum Packet Size (0x27) is not 0 (section
      3.1.2.11.4).

    Every other value of the right type passes. -/
def propValOK : Nat → PropVal → Bool
  | 0x08, .utf8 s => !s.isEmpty && !s.contains '+' && !s.contains '#'
  | 0x0B, .varByte n => n != 0
  | 0x17, .byte n => n ≤ 1
  | 0x19, .byte n => n ≤ 1
  | 0x21, .twoByte n => n != 0
  | 0x23, .twoByte n => n != 0
  | 0x27, .fourByte n => n != 0
  | _, _ => true

/-- The one rule the standard sets across a property block:
    Authentication Data (0x16) may stand only together with an
    Authentication Method (0x15) (section 3.1.2.11.10). -/
def authOK (ps : List Property) : Bool :=
  !(ps.any fun p => p.id == 0x16) || ps.any fun p => p.id == 0x15

/-! ## String checks

  The specification's string rules (section 1.5.4): a string is
  well formed UTF-8 and must not contain the null character
  U+0000. The byte length of a string field must also fit the
  two byte length prefix. -/

/-- Does this text contain the null character? -/
def hasNul (s : List Char) : Bool :=
  s.any fun c => decide (c = '\u0000')

/-- A string fit to print: no null character, and its UTF-8
    byte length fits the two byte length prefix. -/
def StrWF (s : List Char) : Prop :=
  '\u0000' ∉ s ∧ (Utf8.encode s).length ≤ 65535

/-- Binary data fit to print: its length fits the two byte
    length prefix. -/
def BinWF (bs : List UInt8) : Prop :=
  bs.length ≤ 65535

/-- A topic name fit to print (section 4.7.1): a string, not
    empty, holding neither wildcard character. -/
def TopicWF (s : List Char) : Prop :=
  StrWF s ∧ s ≠ [] ∧ '+' ∉ s ∧ '#' ∉ s

/-- Does a property list carry a Topic Alias (0x23)? -/
def hasTopicAlias (ps : List Property) : Bool :=
  ps.any fun p => p.id == 0x23

/-- A PUBLISH topic name fit to print, beside the packet's
    properties: a string holding neither wildcard character,
    which may be empty only when the properties carry a Topic
    Alias that stands for the topic (sections 3.3.2.1 and
    3.3.2.3.4). -/
def PubTopicWF (s : List Char) (props : List Property) : Prop :=
  StrWF s ∧ '+' ∉ s ∧ '#' ∉ s ∧ (s = [] → hasTopicAlias props = true)

/-! ## Field printers -/

/-- Print a string field: the two byte length of its UTF-8
    bytes, then the bytes (section 1.5.4). -/
def printStr (s : List Char) : List UInt8 :=
  writeBE 2 (Utf8.encode s).length ++ Utf8.encode s

/-- Print a binary data field: the two byte length, then the
    bytes (section 1.5.3). -/
def printBin (bs : List UInt8) : List UInt8 :=
  writeBE 2 bs.length ++ bs

/-- Print a property value, in the shape of its type. -/
def printPropVal : PropVal → List UInt8
  | .byte n => [n.toUInt8]
  | .twoByte n => writeBE 2 n
  | .fourByte n => writeBE 4 n
  | .varByte n => printVBI n
  | .utf8 s => printStr s
  | .utf8Pair k v => printStr k ++ printStr v
  | .binary bs => printBin bs

/-- Print one property: the identifier as a variable byte
    integer, then the value. -/
def printProperty (p : Property) : List UInt8 :=
  printVBI p.id ++ printPropVal p.val

/-- Print a list of properties, one after the other. -/
def printPropsList : List Property → List UInt8
  | [] => []
  | p :: ps => printProperty p ++ printPropsList ps

/-- Print a property block: the property length as a variable
    byte integer, then the properties themselves (section
    2.2.2). -/
def printProps (ps : List Property) : List UInt8 :=
  printVBI (printPropsList ps).length ++ printPropsList ps

/-! ## The packet values -/

/-- The subscription options of one topic filter in a SUBSCRIBE
    packet (section 3.8.3): a maximum QoS, the no local and
    retain as published flags, and a retain handling choice. -/
structure SubOpts where
  qos : Nat
  noLocal : Bool
  retainAsPublished : Bool
  retainHandling : Nat
  deriving DecidableEq, Repr

/-- The options byte of a filter: QoS in bits 0 and 1, no local
    at bit 2, retain as published at bit 3, retain handling in
    bits 4 and 5, and the reserved bits 6 and 7 clear. -/
def printOptsByte (o : SubOpts) : UInt8 :=
  (o.qos + (if o.noLocal then 4 else 0) + (if o.retainAsPublished then 8 else 0)
    + o.retainHandling * 16).toUInt8

/-- A will, the part of a CONNECT packet that stands when its
    will flag is set (section 3.1.3): will properties, a will
    topic, and a will payload, with the QoS and retain flag the
    connect flags byte carries. -/
structure Will where
  qos : Nat
  retain : Bool
  props : List Property
  topic : List Char
  payload : List UInt8
  deriving DecidableEq, Repr

/-- A CONNECT packet's fields (section 3.1). The protocol name
    and level are not fields: this slice reads and writes MQTT
    5.0 only, so they are fixed at "MQTT" and 5. The connect
    flags byte is computed from the fields that drive it: the
    username and password options, the will option with its QoS
    and retain flag, and the clean start flag. -/
structure Connect where
  cleanStart : Bool
  keepAlive : Nat
  props : List Property
  clientId : List Char
  will : Option Will
  username : Option (List Char)
  password : Option (List UInt8)
  deriving DecidableEq, Repr

/-- A PUBLISH packet's fields (section 3.3). The packet
    identifier stands exactly when the QoS is 1 or 2, so it is
    an option beside the QoS. -/
structure Publish where
  dup : Bool
  qos : Nat
  retain : Bool
  topic : List Char
  packetId : Option Nat
  props : List Property
  payload : List UInt8
  deriving DecidableEq, Repr

/-- A control packet of one of the seven types this slice
    covers. A DISCONNECT body is one of the three forms section
    3.14 allows: none at all (`none`), a reason code alone
    (`some (rc, none)`), or a reason code and a property block
    (`some (rc, some ps)`). -/
inductive Packet where
  | connect (c : Connect) : Packet
  | publish (p : Publish) : Packet
  | subscribe (packetId : Nat) (props : List Property)
      (filters : List (List Char × SubOpts)) : Packet
  | suback (packetId : Nat) (props : List Property)
      (reasons : List Nat) : Packet
  | pingreq : Packet
  | pingresp : Packet
  | disconnect (body : Option (Nat × Option (List Property))) : Packet
  deriving DecidableEq, Repr

/-! ## Body printers -/

/-- The connect flags byte (section 3.1.2): username flag at
    bit 7, password flag at bit 6, will retain at bit 5, will
    QoS at bits 4 and 3, will flag at bit 2, clean start at
    bit 1, and the reserved bit 0 clear. -/
def connectFlags (c : Connect) : Nat :=
  (if c.username.isSome then 128 else 0)
    + (if c.password.isSome then 64 else 0)
    + (match c.will with
       | some w => (if w.retain then 32 else 0) + w.qos * 8 + 4
       | none => 0)
    + (if c.cleanStart then 2 else 0)

/-- Print the will part of a CONNECT payload, or nothing when
    there is no will. -/
def printWillPart : Option Will → List UInt8
  | none => []
  | some w => printProps w.props ++ (printStr w.topic ++ printBin w.payload)

/-- Print an optional string field, or nothing. -/
def printOptStr : Option (List Char) → List UInt8
  | none => []
  | some s => printStr s

/-- Print an optional binary field, or nothing. -/
def printOptBin : Option (List UInt8) → List UInt8
  | none => []
  | some bs => printBin bs

/-- The body of a CONNECT packet: the protocol name, protocol
    level, connect flags, and keep alive, then the properties,
    then the payload: client identifier, the will fields when
    the will flag is set, the username when its flag is set,
    and the password when its flag is set. -/
def printConnectBody (c : Connect) : List UInt8 :=
  printStr ['M', 'Q', 'T', 'T'] ++ ([5, (connectFlags c).toUInt8]
    ++ (writeBE 2 c.keepAlive ++ (printProps c.props ++ (printStr c.clientId
    ++ (printWillPart c.will ++ (printOptStr c.username
    ++ printOptBin c.password))))))

/-- The fixed header byte of a PUBLISH packet: the type 3, the
    DUP flag at bit 3, the QoS at bits 2 and 1, and RETAIN at
    bit 0. -/
def publishHeader (p : Publish) : Nat :=
  0x30 + (if p.dup then 8 else 0) + p.qos * 2 + (if p.retain then 1 else 0)

/-- Print a packet identifier when one stands, or nothing. -/
def printIdOpt : Option Nat → List UInt8
  | none => []
  | some id => writeBE 2 id

/-- The body of a PUBLISH packet: topic name, the packet
    identifier when the QoS carries one, the properties, then
    the payload, which is all the bytes that remain. -/
def printPublishBody (p : Publish) : List UInt8 :=
  printStr p.topic ++ (printIdOpt p.packetId ++ (printProps p.props ++ p.payload))

/-- Print one topic filter of a SUBSCRIBE payload: the filter
    string, then its options byte. -/
def printFilter (f : List Char × SubOpts) : List UInt8 :=
  printStr f.1 ++ [printOptsByte f.2]

/-- Print a list of topic filters, one after the other. -/
def printFilters : List (List Char × SubOpts) → List UInt8
  | [] => []
  | f :: fs => printFilter f ++ printFilters fs

/-- The body of a SUBSCRIBE packet: packet identifier,
    properties, then the topic filters. -/
def printSubscribeBody (id : Nat) (ps : List Property)
    (fs : List (List Char × SubOpts)) : List UInt8 :=
  writeBE 2 id ++ (printProps ps ++ printFilters fs)

/-- The body of a SUBACK packet: packet identifier, properties,
    then one reason code byte per granted subscription. -/
def printSubackBody (id : Nat) (ps : List Property) (rs : List Nat) : List UInt8 :=
  writeBE 2 id ++ (printProps ps ++ rs.map Nat.toUInt8)

/-- The body of a packet: everything after the fixed header
    byte and the remaining length. -/
def bodyOf : Packet → List UInt8
  | .connect c => printConnectBody c
  | .publish p => printPublishBody p
  | .subscribe id ps fs => printSubscribeBody id ps fs
  | .suback id ps rs => printSubackBody id ps rs
  | .pingreq => []
  | .pingresp => []
  | .disconnect none => []
  | .disconnect (some (rc, none)) => [rc.toUInt8]
  | .disconnect (some (rc, some ps)) => [rc.toUInt8] ++ printProps ps

/-- The fixed header byte of a packet: the type in the high
    nibble, and the flags the specification fixes in the low
    nibble (section 2.1.2). SUBSCRIBE carries 0010; PUBLISH
    carries its own DUP, QoS, and RETAIN bits; the rest carry
    0000. -/
def headerOf : Packet → UInt8
  | .connect _ => 0x10
  | .publish p => (publishHeader p).toUInt8
  | .subscribe _ _ _ => 0x82
  | .suback _ _ _ => 0x90
  | .pingreq => 0xC0
  | .pingresp => 0xD0
  | .disconnect _ => 0xE0

/-- Print a packet: the fixed header byte, the remaining length
    as a variable byte integer, and the body. -/
def print (p : Packet) : List UInt8 :=
  headerOf p :: printVBI (bodyOf p).length ++ bodyOf p

/-! ## Well formed values

  The round trip claim in `Mqtt.Proofs` holds for well formed
  packets: the fields the printer can write exactly. Numbers
  fit the widths that carry them, strings obey the string
  rules, properties match the table in type and place and do
  not repeat a single use property, and the whole body fits
  the remaining length's four byte variable byte integer. -/

/-- A property value in the shape the printer writes exactly. -/
def ValWF : PropVal → Prop
  | .byte n => n < 256
  | .twoByte n => n < 65536
  | .fourByte n => n < 4294967296
  | .varByte n => n < 268435456
  | .utf8 s => StrWF s
  | .utf8Pair k v => StrWF k ∧ StrWF v
  | .binary bs => BinWF bs

/-- A property list in the shape of one block: every property
    is allowed on the block's packet kind, its value matches
    the table's type for its identifier, is itself well formed
    and keeps the value rules of `propValOK`, and no single use
    property repeats. The `seen` list carries the identifiers
    already standing in the block; calls start it empty. -/
def PropsWF (s : PropSet) : List Nat → List Property → Prop
  | _, [] => True
  | seen, p :: ps =>
    p.id ∈ allowedOf s ∧ propTypeOf p.id = some (valType p.val) ∧ ValWF p.val
      ∧ propValOK p.id p.val = true
      ∧ (repeatableIn s p.id = true ∨ p.id ∉ seen)
      ∧ PropsWF s (p.id :: seen) ps

/-- A property block fit to print: the list is well formed, its
    printed length fits a variable byte integer, and it keeps
    the block rule of `authOK`. -/
def PropsBlockWF (s : PropSet) (ps : List Property) : Prop :=
  PropsWF s [] ps ∧ (printPropsList ps).length < 268435456 ∧ authOK ps = true

/-- A will fit to print. -/
def WillWF (w : Will) : Prop :=
  w.qos ≤ 2 ∧ PropsBlockWF .will w.props ∧ TopicWF w.topic ∧ BinWF w.payload

/-- A CONNECT packet fit to print. -/
def ConnectWF (c : Connect) : Prop :=
  c.keepAlive < 65536 ∧ PropsBlockWF .connect c.props ∧ StrWF c.clientId
    ∧ (∀ w, c.will = some w → WillWF w)
    ∧ (∀ u, c.username = some u → StrWF u)
    ∧ (∀ p, c.password = some p → BinWF p)

/-- A PUBLISH packet fit to print. The packet identifier
    stands exactly when the QoS is 1 or 2, and is never 0. The
    DUP flag is clear at QoS 0 (section 3.3.1.1,
    [MQTT-3.3.1-2]). -/
def PublishWF (p : Publish) : Prop :=
  p.qos ≤ 2 ∧ PubTopicWF p.topic p.props
    ∧ (∀ id, p.packetId = some id → 1 ≤ id ∧ id < 65536 ∧ (p.qos = 1 ∨ p.qos = 2))
    ∧ (p.packetId = none → p.qos = 0)
    ∧ PropsBlockWF .publish p.props
    ∧ (p.qos = 0 → p.dup = false)

/-- Subscription options fit to print: the QoS and the retain
    handling choice are at most 2 (3 is reserved in both). -/
def OptsWF (o : SubOpts) : Prop :=
  o.qos ≤ 2 ∧ o.retainHandling ≤ 2

/-! ## Topic filters -/

/-- Split a text at each `/` into its topic levels (section
    4.7.1.1). A text with no `/` is one level, and the empty
    text is one empty level. -/
def splitLevels : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '/' then [] :: splitLevels cs
    else match splitLevels cs with
      | [] => [[c]]
      | l :: ls => (c :: l) :: ls

/-- A level of a topic filter other than the last: either `+`
    alone, which must occupy an entire level [MQTT-4.7.1-2], or
    a level holding neither wildcard character. -/
def levelOK (l : List Char) : Bool :=
  l == ['+'] || (!l.contains '#' && !l.contains '+')

/-- The wildcard rules over the levels of a topic filter
    (section 4.7.1): `+` stands alone in its level
    [MQTT-4.7.1-2], and `#` stands alone in the last level
    [MQTT-4.7.1-1]. -/
def levelsOK : List (List Char) → Bool
  | [] => true
  | [l] => l == ['#'] || levelOK l
  | l :: ls => levelOK l && levelsOK ls

/-- A topic filter that is not a shared subscription: at least
    one character long [MQTT-4.7.3-1], and its levels keep the
    wildcard rules. -/
def plainFilterOK (f : List Char) : Bool :=
  !f.isEmpty && levelsOK (splitLevels f)

/-- Split the text after `$share/` at its first `/`: the
    ShareName before it, and the filter after it when a `/`
    stands. -/
def shareSplit : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = '/' then ([], some cs)
    else match shareSplit cs with
      | (n, r) => (c :: n, r)

/-- A topic filter and its options, fit for a SUBSCRIBE. A filter
    that starts with `$share/` is a shared subscription (section
    4.8.2): a ShareName at least one character long holding no
    `+` or `#` [MQTT-4.8.2-1], then a `/` and a topic filter
    [MQTT-4.8.2-2], and the No Local option clear
    [MQTT-3.8.3-4]. Any other filter keeps the plain rules. -/
def filterOK (f : List Char) (o : SubOpts) : Bool :=
  match f with
  | '$' :: 's' :: 'h' :: 'a' :: 'r' :: 'e' :: '/' :: r =>
    match shareSplit r with
    | (name, some flt) =>
      !name.isEmpty && !name.contains '+' && !name.contains '#'
        && plainFilterOK flt && !o.noLocal
    | (_, none) => false
  | _ => plainFilterOK f

/-- A topic filter list fit to print, member by member: each
    filter is a string, its options are well formed, and the
    pair keeps the filter rules of `filterOK`. -/
def FiltersWF : List (List Char × SubOpts) → Prop
  | [] => True
  | (f, o) :: fs => StrWF f ∧ OptsWF o ∧ filterOK f o = true ∧ FiltersWF fs

/-- The per type half of well formedness for a packet. -/
def PacketFieldsWF : Packet → Prop
  | .connect c => ConnectWF c
  | .publish p => PublishWF p
  | .subscribe id ps fs =>
    1 ≤ id ∧ id < 65536 ∧ PropsBlockWF .subscribe ps ∧ fs ≠ [] ∧ FiltersWF fs
  | .suback id ps rs =>
    1 ≤ id ∧ id < 65536 ∧ PropsBlockWF .suback ps ∧ rs ≠ []
      ∧ (∀ r ∈ rs, r < 256)
  | .pingreq => True
  | .pingresp => True
  | .disconnect none => True
  | .disconnect (some (rc, none)) => rc < 256
  | .disconnect (some (rc, some ps)) => rc < 256 ∧ PropsBlockWF .disconnect ps

/-- A packet fit to print: its fields are well formed and its
    body fits the remaining length, a variable byte integer of
    at most four bytes. -/
def PacketWF (p : Packet) : Prop :=
  PacketFieldsWF p ∧ (bodyOf p).length < 268435456

end Mqtt
