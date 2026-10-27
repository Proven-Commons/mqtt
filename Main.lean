/-
  Command line front end for the MQTT packet codec.

  One request per line, in the shape `op numbers`, where the op
  and the numbers are parted by one space, and the numbers are
  decimal numbers parted by commas, with no spaces inside the
  number list. A line holds a number in plain decimal: no sign,
  no leading zeros (the number 0 itself is written `0`), and at
  most twenty digits. An empty line is passed over with no
  answer. A request that breaks the line shape prints `error`.

  The one operation:

  - `parse` takes comma parted byte numbers and prints `ok:` and
    the bytes of the packet printed back when the bytes are
    exactly one packet this slice reads, and `none` when they
    are not. The reprint is the packet read and written again,
    byte for byte when the packet arrived in its printed form.
    The full rules are in SPEC.md.
-/

import Mqtt

open Mqtt

/-- Read one number token: plain decimal digits, no sign, no
    leading zeros but for the number 0 itself, at most twenty
    digits. -/
def parseNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty ∨ 20 < cs.length then none
  else if 1 < cs.length ∧ cs.head! = '0' then none
  else if cs.all Char.isDigit then
    some (cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)
  else none

/-- Read the number list of a payload. The empty payload is the
    empty list. -/
def numsOf (payload : String) : Option (List Nat) :=
  if payload.isEmpty then some []
  else (payload.splitOn ",").mapM parseNat

/-- Read the byte list of a payload: every number at most 255. -/
def bytesOf (payload : String) : Option (List UInt8) :=
  (numsOf payload).bind fun ns =>
    if ns.all (· ≤ 255) then some (ns.map Nat.toUInt8) else none

/-- Print a number list as comma parted decimal numbers. -/
def joinNums (ns : List Nat) : String :=
  ns.foldl (fun acc n => if acc.isEmpty then toString n else acc ++ "," ++ toString n) ""

/-- Run one operation on one payload. The answer is `error` for a
    malformed request, and `none` for well formed bytes that this
    slice rejects. -/
def run (op payload : String) : String :=
  match op with
  | "parse" =>
    match bytesOf payload with
    | none => "error"
    | some bs =>
      match parse bs with
      | some v => "ok:" ++ joinNums ((print v).map UInt8.toNat)
      | none => "none"
  | _ => "error"

/-- Answer one request line. An empty line gets no answer. -/
def processLine (line : String) : Option String :=
  if line.isEmpty then none
  else
    match line.splitOn " " with
    | [op] => some (run op "")
    | [op, payload] => some (run op payload)
    | _ => some "error"

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match processLine (chomp line) with
    | some out => IO.println out
    | none => pure ()
