/-
  The MQTT 5.0 packet reader.

  The reader works on a byte list and reads one packet from its
  front, returning the packet and the bytes after it, so a
  caller can walk a stream of packets arriving over TCP. It
  never reads past the end of its input: every length in the
  packet (the remaining length, a property length, a string or
  binary length) is checked against the bytes that actually
  remain before any of them are taken.

  Rules the reader follows, beyond the layout in SPEC.md:

  - A variable byte integer stops at four bytes: a continuation
    bit on the fourth byte is rejected, and a value cut off by
    the end of the input is rejected. An encoding that uses more
    bytes than the value needs is rejected too: its last byte
    is 0 after a continuation byte (section 1.5.5).
  - A packet type outside the seven this slice covers is
    rejected, and so is a fixed header flags nibble other than
    the one the specification fixes for the type; PUBLISH is
    the only type whose flags carry meaning, and its reserved
    QoS value 3 is rejected, as is the DUP flag at QoS 0
    (section 3.3.1.1, [MQTT-3.3.1-2]).
  - The body of a packet is cut out by its remaining length
    first, and the type's reader must consume the cut exactly:
    bytes left over inside the cut are rejected, and a field
    that runs past the cut is rejected.
  - Properties are checked against the specification's table:
    an identifier with no table entry, an identifier not
    allowed on the packet kind at hand, and a repeat of a single
    use property are all rejected. So is a value that breaks a
    value rule (`propValOK`), and Authentication Data without
    an Authentication Method (`authOK`).
-/

import Mqtt.Value

namespace Mqtt

/-! ## Byte readers -/

/-- Read a big endian number of exactly `k` bytes from the
    front of a byte list. Returns the number and the bytes
    after it, or `none` when fewer than `k` bytes stand there. -/
def readNat : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    (readNat k bs).map fun (u, r) => (b.toNat * 256 ^ k + u, r)

/-- The unfolding rule for `readNat` at a successor width on a
    list with a head byte. -/
theorem readNat_succ_cons (k : Nat) (b : UInt8) (bs : List UInt8) :
    readNat (k + 1) (b :: bs) =
      (readNat k bs).map fun (u, r) => (b.toNat * 256 ^ k + u, r) := by
  rw [readNat]

/-- Take `n` bytes off the front of a byte list, or `none` when
    fewer than `n` bytes stand there. Returns the bytes taken
    and the bytes after them. -/
def readBytes (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bs.length ≥ n then some (bs.take n, bs.drop n) else none

/-- Read one byte as a number. -/
def readByte : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs => some (b.toNat, bs)

/-! ## The variable byte integer reader -/

/-- Read a variable byte integer with at most `k` bytes left to
    spend. A byte below 128 ends the number. A byte of 128 or
    more carries the low seven bits of the value and a
    continuation mark: the bytes after it carry the rest of the
    value, which counts 128 times. That rest must not be 0: a
    writing whose last byte is 0 after a continuation byte uses
    more bytes than the value needs, which section 1.5.5
    forbids. A continuation byte with no byte left to spend is
    rejected, and so is the end of the input while a
    continuation bit stands. -/
def decVBIGo : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else match decVBIGo k bs with
      | none => none
      | some (v, r) => if v = 0 then none else some (b.toNat - 128 + 128 * v, r)

/-- Read a variable byte integer (sections 1.5.5 and 2.1.4): at
    most four bytes, in the fewest bytes the value needs.
    Returns the value and the bytes after it. -/
def decVBI (bs : List UInt8) : Option (Nat × List UInt8) :=
  decVBIGo 4 bs

/-! ## String and binary readers -/

/-- Check a decoded string field's characters: the strict
    decoder has already settled well formedness; the null
    character must also be absent (section 1.5.4). -/
def checkChars (s : List Char) : Option (List Char) :=
  if hasNul s then none else some s

/-- Read a string field: the two byte length, that many bytes,
    read as strict UTF-8 with no null character. -/
def readStr (bs : List UInt8) : Option (List Char × List UInt8) := do
  let (len, r1) ← readNat 2 bs
  let (chunk, r2) ← readBytes len r1
  let s ← (Utf8.decode chunk).bind checkChars
  pure (s, r2)

/-- Read a binary data field: the two byte length, then that
    many bytes. -/
def readBin (bs : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (len, r1) ← readNat 2 bs
  readBytes len r1

/-! ## Property readers -/

/-- Read a property value of the given type. -/
def readPropVal (t : PropType) : List UInt8 → Option (PropVal × List UInt8)
  | bs =>
    match t with
    | .byte => (readNat 1 bs).map fun (n, r) => (.byte n, r)
    | .twoByte => (readNat 2 bs).map fun (n, r) => (.twoByte n, r)
    | .fourByte => (readNat 4 bs).map fun (n, r) => (.fourByte n, r)
    | .varByte => (decVBI bs).map fun (n, r) => (.varByte n, r)
    | .utf8 => (readStr bs).map fun (s, r) => (.utf8 s, r)
    | .utf8Pair => do
      let (k, r1) ← readStr bs
      let (v, r2) ← readStr r1
      pure (.utf8Pair k v, r2)
    | .binary => (readBin bs).map fun (chunk, r) => (.binary chunk, r)

/-- Read one property: the identifier as a variable byte
    integer, checked against the table and the block's allowed
    list, then the value in the shape of the table's type for
    the identifier, which must keep the value rules of
    `propValOK`. A repeat of a single use property whose
    identifier already stands in `seen` is rejected. -/
def readEntry (s : PropSet) (seen : List Nat) (bs : List UInt8) :
    Option (Property × List UInt8) := do
  let (id, r1) ← decVBI bs
  if (allowedOf s).contains id && (repeatableIn s id || !seen.contains id) then
    match propTypeOf id with
    | none => none
    | some t => (readPropVal t r1).bind fun (v, r2) =>
      if propValOK id v then some (⟨id, v⟩, r2) else none
  else none

/-- Read properties until the input runs out, or `none` when
    one fails to read. The fuel is a bound on the number of
    properties: each property takes at least two bytes (an
    identifier and one value byte at the least), so the input
    length is always fuel enough. The `seen` list carries the
    identifiers already read in this block. -/
def readEntriesGo : Nat → PropSet → List Nat → List UInt8 →
    Option (List Property × List UInt8)
  | 0, _, _, bs => if bs.isEmpty then some ([], bs) else none
  | fuel + 1, s, seen, bs =>
    if bs.isEmpty then some ([], bs)
    else match readEntry s seen bs with
      | none => none
      | some (p, r1) =>
        match readEntriesGo fuel s (p.id :: seen) r1 with
        | none => none
        | some (ps, r2) => some (p :: ps, r2)

/-- Read a whole property block's insides: exactly the given
    bytes, all consumed, keeping the block rule of `authOK`. -/
def readEntries (s : PropSet) (seg : List UInt8) : Option (List Property) :=
  match readEntriesGo seg.length s [] seg with
  | some (ps, []) => if authOK ps then some ps else none
  | _ => none

/-- Read a property block: the property length as a variable
    byte integer, then exactly that many bytes of properties.
    Bytes left over inside the block, or a block that runs past
    the bytes at hand, are rejected. -/
def readProps (s : PropSet) (bs : List UInt8) :
    Option (List Property × List UInt8) := do
  let (len, r1) ← decVBI bs
  let (seg, r2) ← readBytes len r1
  let ps ← readEntries s seg
  pure (ps, r2)

/-! ## SUBSCRIBE filter readers -/

/-- Read a subscription options byte. The reserved bits 6 and
    7 must be clear, and neither the QoS field nor the retain
    handling field may hold the reserved value 3. -/
def readOptsByte (b : Nat) : Option SubOpts :=
  if b < 64 ∧ b % 4 ≠ 3 ∧ (b / 16) % 4 ≠ 3 then
    some ⟨b % 4, (b / 4) % 2 = 1, (b / 8) % 2 = 1, (b / 16) % 4⟩
  else none

/-- Read topic filters until the input runs out, or `none`
    when one fails to read. The fuel is a bound on the number
    of filters: each filter takes at least three bytes (a two
    byte length and an options byte), so the input length is
    always fuel enough. -/
def readFiltersGo : Nat → List UInt8 →
    Option (List (List Char × SubOpts) × List UInt8)
  | 0, bs => if bs.isEmpty then some ([], bs) else none
  | fuel + 1, bs =>
    if bs.isEmpty then some ([], bs)
    else match readStr bs with
      | none => none
      | some (f, ob :: r2) =>
        match readOptsByte ob.toNat with
        | none => none
        | some o =>
          match readFiltersGo fuel r2 with
          | none => none
          | some (fs, r3) => some ((f, o) :: fs, r3)
      | some (_, []) => none

/-! ## Body readers -/

/-- The `k`th bit of a number, as a boolean: bit 0 is the least
    significant. -/
def flagBit (n k : Nat) : Bool := (n / 2 ^ k) % 2 = 1

/-- A topic name check for a read string: not empty, and
    neither wildcard character stands in it. The will topic
    takes this check. -/
def checkTopic (s : List Char) : Option (List Char) :=
  if s.isEmpty || s.any (fun c => decide (c = '+')) || s.any (fun c => decide (c = '#')) then
    none
  else some s

/-- The wildcard half of the topic name check, for a PUBLISH
    topic name, which may be empty when a Topic Alias stands
    for it: neither wildcard character stands in the text
    (section 3.3.2.1, [MQTT-3.3.2-2]). -/
def checkNoWildcards (s : List Char) : Option (List Char) :=
  if s.any (fun c => decide (c = '+')) || s.any (fun c => decide (c = '#')) then
    none
  else some s

/-- Read the will step of a CONNECT body: the will
    properties, will topic and will payload when the will
    flag is set, nothing when it is clear. The will QoS and
    will retain come from the connect flags byte. -/
def readWillPart (flags : Nat) (r6 : List UInt8) :
    Option (Option Will × List UInt8) :=
  if flagBit flags 2 then
    (readProps .will r6).bind fun (wprops, s1) =>
    (readStr s1).bind fun (wtopic, s2) =>
    (checkTopic wtopic).bind fun wtopic =>
    (readBin s2).bind fun (wpay, s3) =>
    some (some ⟨(flags / 8) % 4, flagBit flags 5, wprops, wtopic, wpay⟩, s3)
  else some (none, r6)

/-- Read an optional string field of a CONNECT payload,
    present exactly when its connect flag bit is set. -/
def readOptStrField (cond : Bool) (r : List UInt8) :
    Option (Option (List Char) × List UInt8) :=
  if cond then (readStr r).map fun (u, r') => (some u, r')
  else some (none, r)

/-- Read an optional binary field of a CONNECT payload,
    present exactly when its connect flag bit is set. -/
def readOptBinField (cond : Bool) (r : List UInt8) :
    Option (Option (List UInt8) × List UInt8) :=
  if cond then (readBin r).map fun (p, r') => (some p, r')
  else some (none, r)

/-- Read a CONNECT body: the whole body cut, nothing left
    over. The protocol name must be "MQTT" and the level 5. The
    reserved connect flag bit must be clear and the will QoS
    must not be the reserved value 3. When the will flag is
    clear, the will QoS and will retain bits must be clear too
    (sections 3.1.2.6 [MQTT-3.1.2-11] and 3.1.2.7
    [MQTT-3.1.2-13]). The payload fields stand exactly when the
    connect flags say they stand. -/
def readConnectBody (seg : List UInt8) : Option Connect :=
  (readStr seg).bind fun (proto, r1) =>
  if proto = ['M', 'Q', 'T', 'T'] then
    (readByte r1).bind fun (level, r2) =>
    if level = 5 then
      (readByte r2).bind fun (flags, r3) =>
      if flags % 2 = 0 then
      if (flags / 8) % 4 ≠ 3 then
      if flagBit flags 2 || (flags / 8) % 8 = 0 then
        (readNat 2 r3).bind fun (ka, r4) =>
        (readProps .connect r4).bind fun (props, r5) =>
        (readStr r5).bind fun (cid, r6) =>
        (readWillPart flags r6).bind fun (will, r7) =>
        (readOptStrField (flagBit flags 7) r7).bind fun (username, r8) =>
        (readOptBinField (flagBit flags 6) r8).bind fun (password, r9) =>
        if r9.isEmpty then
          some ⟨flagBit flags 1, ka, props, cid, will, username, password⟩
        else none
      else none
      else none
      else none
    else none
  else none

/-- Read the packet identifier step of a PUBLISH body: no
    identifier at QoS 0, a two byte nonzero identifier at
    QoS 1 and 2. -/
def readPacketId (flags : Nat) (r1 : List UInt8) :
    Option (Option Nat × List UInt8) :=
  if (flags / 2) % 4 = 0 then some (none, r1)
  else (readNat 2 r1).bind fun (id, r) =>
    if id ≠ 0 then some (some id, r) else none

/-- Read a PUBLISH body: topic name, the packet identifier
    when the QoS is 1 or 2 (and never 0), the properties, and
    the payload, which is all the bytes that remain in the cut.
    The QoS comes from the fixed header flags; the reserved
    value 3 has already been turned away by the caller. The
    topic name holds no wildcard, and it may be empty only when
    the properties carry a Topic Alias (section 3.3.2.1: "It is
    a Protocol Error if the Topic Name is zero length and there
    is no Topic Alias"). -/
def readPublishBody (flags : Nat) (seg : List UInt8) : Option Publish :=
  (readStr seg).bind fun (topic, r1) =>
  (checkNoWildcards topic).bind fun topic =>
  (readPacketId flags r1).bind fun (pid, r2) =>
  (readProps .publish r2).bind fun (props, payload) =>
  if topic.isEmpty && !hasTopicAlias props then none
  else some ⟨flagBit flags 3, (flags / 2) % 4, flagBit flags 0, topic, pid,
    props, payload⟩

/-- Read a SUBSCRIBE body: a nonzero packet identifier, the
    properties, and a nonempty list of topic filters that
    fills the rest of the cut exactly. -/
def readSubscribeBody (seg : List UInt8) : Option Packet := do
  let (id, r1) ← readNat 2 seg
  if id ≠ 0 then pure () else none
  let (props, r2) ← readProps .subscribe r1
  let (fs, r3) ← readFiltersGo r2.length r2
  if r3.isEmpty && !fs.isEmpty then pure (.subscribe id props fs) else none

/-- Read a SUBACK body: a nonzero packet identifier, the
    properties, and a nonempty list of reason codes filling
    the rest of the cut. -/
def readSubackBody (seg : List UInt8) : Option Packet := do
  let (id, r1) ← readNat 2 seg
  if id ≠ 0 then pure () else none
  let (props, r2) ← readProps .suback r1
  if !r2.isEmpty then pure (.suback id props (r2.map UInt8.toNat)) else none

/-- Read a DISCONNECT body: an empty cut is a normal
    disconnection with no body. A cut of one byte is a reason
    code on its own: the specification omits the property
    length when the remaining length is 1 (section 3.14.2).
    A longer cut is a reason code and a property block that
    fills the rest of the cut. -/
def readDisconnectBody (seg : List UInt8) : Option Packet :=
  match seg with
  | [] => some (.disconnect none)
  | rc :: r1 =>
    if r1.isEmpty then some (.disconnect (some (rc.toNat, [])))
    else do
      let (props, r2) ← readProps .disconnect r1
      if r2.isEmpty then pure (.disconnect (some (rc.toNat, props))) else none

/-- Read a packet body of the given type, with the given fixed
    header flags, from a body cut out by the remaining length.
    The reader must consume the cut exactly. Packet types
    outside the seven this slice covers are rejected, and so
    is a flags nibble other than the one the specification
    fixes for the type, and a PUBLISH flags nibble with QoS 3,
    or with DUP set at QoS 0. -/
def parseBody (typ flags : Nat) (seg : List UInt8) : Option Packet :=
  match typ with
  | 1 => if flags = 0 then (readConnectBody seg).map Packet.connect else none
  | 3 =>
    if (flags / 2) % 4 = 3 then none
    else if (flags / 2) % 4 = 0 ∧ flagBit flags 3 = true then none
    else (readPublishBody flags seg).map Packet.publish
  | 8 => if flags = 2 then readSubscribeBody seg else none
  | 9 => if flags = 0 then readSubackBody seg else none
  | 12 => if flags = 0 && seg.isEmpty then some .pingreq else none
  | 13 => if flags = 0 && seg.isEmpty then some .pingresp else none
  | 14 => if flags = 0 then readDisconnectBody seg else none
  | _ => none

/-! ## The packet reader -/

/-- Read one packet from the front of a byte list: the fixed
    header byte, the remaining length, and exactly that many
    body bytes. Returns the packet and the bytes after it. -/
def parsePacket (bs : List UInt8) : Option (Packet × List UInt8) :=
  match bs with
  | [] => none
  | b :: r0 => do
    let (len, r1) ← decVBI r0
    let (seg, r2) ← readBytes len r1
    let p ← parseBody (b.toNat / 16) (b.toNat % 16) seg
    pure (p, r2)

/-- Read one whole packet: exactly one packet, with nothing
    after it. -/
def parse (bs : List UInt8) : Option Packet :=
  match parsePacket bs with
  | some (p, []) => some p
  | _ => none

end Mqtt
