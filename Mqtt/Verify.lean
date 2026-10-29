/-
  Axiom check for the claims this package makes. Run with:

    lake env lean Mqtt/Verify.lean

  Every claim should list only the standard axioms (propext,
  Classical.choice, Quot.sound). A line naming sorryAx would mean
  a proof rests on an admitted gap, and the claim is not proved.
-/

import Proofs
import Proofs.Examples

open Mqtt.Proofs Mqtt.Examples

#print axioms parse_print
#print axioms parsePacket_print
#print axioms decVBI_printVBI
#print axioms parse_inv
#print axioms parsePacket_inv
#print axioms decVBI_canonical
#print axioms parse_connect
#print axioms parse_publish_qos1
#print axioms vbi_max
#print axioms vbi_five_bytes
#print axioms printVBI_length
#print axioms decVBI_length
#print axioms parse_iff
#print axioms header_rule
#print axioms connect_rule
#print axioms publish_rule
#print axioms subscribe_rule
#print axioms property_rule
#print axioms empty_body_rule
