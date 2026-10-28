/-
  Worked examples, proved. The variable byte integer examples
  are the MQTT 5.0 specification's own table (section 2.1.4).
  The packet examples are hand built from the specification
  text, one for each packet type in this slice, plus the
  rejections this slice promises. The same packets run
  through the command line tool in the test harness, where
  they are checked byte by byte a second time.

  The examples are stated on the reading side. The printer's
  variable byte integer is defined by well founded recursion,
  which the kernel will not evaluate here; the round trip
  theorem covers the printer instead.
-/

import Mqtt

namespace Mqtt.Examples

open Mqtt

/-! ## The variable byte integer table (spec section 2.1.4) -/

theorem vbi_zero : decVBI [0] = some (0, []) := by decide

theorem vbi_127 : decVBI [127] = some (127, []) := by decide

theorem vbi_128 : decVBI [128, 1] = some (128, []) := by decide

theorem vbi_16383 : decVBI [255, 127] = some (16383, []) := by decide

theorem vbi_16384 : decVBI [128, 128, 1] = some (16384, []) := by decide

theorem vbi_2097151 : decVBI [255, 255, 127] = some (2097151, []) := by
  decide

theorem vbi_2097152 : decVBI [128, 128, 128, 1] = some (2097152, []) := by
  decide

theorem vbi_max : decVBI [255, 255, 255, 127] = some (268435455, []) := by
  decide

/-- A continuation bit on the fourth byte rejects: the value
    would need a fifth byte. -/
theorem vbi_five_bytes : decVBI [255, 255, 255, 255] = none := by decide

/-- A writing longer than the value needs rejects (section
    1.5.5): here 0 carried in two bytes, and 128 carried in
    three. -/
theorem vbi_non_minimal : decVBI [128, 0] = none := by decide

theorem vbi_non_minimal_three : decVBI [128, 129, 0] = none := by decide

/-- The decoder returns the rest of the stream untouched. -/
theorem vbi_rest : decVBI [128, 1, 99] = some (128, [99]) := by decide

/-! ## One packet of each type -/

theorem parse_pingreq : parse [192, 0] = some .pingreq := by decide

theorem parse_pingresp : parse [208, 0] = some .pingresp := by decide

/-- A DISCONNECT with no body is a normal disconnection. -/
theorem parse_disconnect_empty :
    parse [224, 0] = some (.disconnect none) := by decide

/-- A DISCONNECT body of one byte is a reason code with an
    empty property block. It is legal. -/
theorem parse_disconnect_reason :
    parse [224, 1, 0] = some (.disconnect (some (0, []))) := by decide

theorem parse_publish_qos0 :
    parse [48, 6, 0, 1, 97, 0, 1, 2]
      = some (.publish ⟨false, 0, false, ['a'], none, [], [1, 2]⟩) := by
  decide

theorem parse_publish_qos1 :
    parse [50, 6, 0, 1, 97, 0, 1, 0]
      = some (.publish ⟨false, 1, false, ['a'], some 1, [], []⟩) := by
  decide

theorem parse_subscribe :
    parse [130, 7, 0, 1, 0, 0, 1, 97, 0]
      = some (.subscribe 1 [] [(['a'], ⟨0, false, false, 0⟩)]) := by
  decide

theorem parse_suback :
    parse [144, 4, 0, 1, 0, 0] = some (.suback 1 [] [0]) := by decide

theorem parse_connect :
    parse [16, 14, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 0, 0, 1, 120]
      = some (.connect ⟨true, 0, [], ['x'], none, none, none⟩) := by
  decide

/-! ## Rejections -/

/-- A PINGREQ with a body rejects: its remaining length must
    be 0. -/
theorem parse_pingreq_body : parse [192, 1, 0] = none := by decide

/-- An empty PUBLISH topic rejects. -/
theorem parse_publish_empty_topic : parse [48, 2, 0, 0] = none := by
  decide

/-- A packet type outside this slice rejects, here type 2. -/
theorem parse_wrong_type : parse [32, 0] = none := by decide

end Mqtt.Examples
