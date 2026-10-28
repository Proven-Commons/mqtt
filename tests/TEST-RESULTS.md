# Test results: mqtt

Seed: 20261026. Tool: the Lean command line program, one process per section, requests batched. The harness checks parsed structure through the re-encoding the tool prints, together with its own oracle.

Paho's Python library (`paho-mqtt`, version 2.1.0) was importable in the interpreter that ran this harness; the Paho cross-check ran. It covers variable byte integers and PUBLISH property blocks, the pieces the library exposes without a broker.

Mosquitto was NOT present on this machine (no `mosquitto` or `mosquitto_sub` binary), so no Mosquitto tests ran.

| Section | Inputs | Agreements |
| --- | --- | --- |
| Fixed cases (spec VBI table, one packet per type, richer hand built packets) | 37 | 37 |
| Oracle differential, random packets of all seven types (seed 20261026) | 3000 | 3000 |
| Paho 2.1.0 cross-check (variable byte integers as Subscription Identifiers, and PUBLISH property blocks) | 378 | 378 |
| Mutations and named rejections, settled by the oracle | 325 | 325 |
| Line protocol cases | 9 | 9 |

Named differences from the oracles:
- paho-mqtt's VariableByteIntegers.decode reads the longer writing 128, 0 as (0, 2) (value, bytes read); this reader refuses that writing, as MQTT-1.5.5-1 requires, so the run does not take Paho's answer there.

Failures: none.
