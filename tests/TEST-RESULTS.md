# Test results: mqtt

- Oracle: the strict reference decoder and encoder in tests/run_tests.py, written from the OASIS MQTT Version 5.0 standard (OASIS Standard, 7 March 2019) and SPEC.md, run on Python 3.13.17; with a cross-check against paho-mqtt 2.1.0, counted apart
- Seed: 20261026
- Inputs: 4855
- Failures: 0

Tool: the Lean command line program, one process per section, requests batched. The harness checks parsed structure through the re-encoding the tool prints, together with its own oracle, and checks that every input the tool accepts among the mutations and named cases reprints byte for byte. Inputs counts the sections that run on every machine.

Paho's Python library (`paho-mqtt`, version 2.1.0) was importable in the interpreter that ran this harness; the Paho cross-check ran. It covers variable byte integers and PUBLISH property blocks, the pieces the library exposes without a broker. Its inputs are listed below and are not part of Inputs.

The plan's third oracle, MQTT 5.0 specification test material, was NOT used: the standard ships no conformance test suite, and the nearest material, the MQTTV5 codec in Eclipse paho.mqtt.testing, is not wired into this harness.

Mosquitto was NOT present on this machine (no `mosquitto` or `mosquitto_sub` binary), so no Mosquitto tests ran.

| Section | Inputs | Agreements |
| --- | --- | --- |
| Fixed cases (spec VBI table, one packet per type, richer hand built packets) | 37 | 37 |
| Oracle differential, random packets of all seven types (seed 20261026) | 3000 | 3000 |
| Mutations and named rejections, settled by the oracle | 325 | 325 |
| Forbidden classes drawn from the seed (property values, Response Topics, Authentication Data, topic filters of 1 to 6 levels), with controls, settled by the oracle | 1484 | 1484 |
| Line protocol cases | 9 | 9 |
| Paho 2.1.0 cross-check (variable byte integers as Subscription Identifiers, and PUBLISH property blocks; not counted in Inputs) | 378 | 378 |

Named differences from the oracles:
- paho-mqtt's VariableByteIntegers.decode reads the longer writing 128, 0 as (0, 2) (value, bytes read); this reader refuses that writing, as MQTT-1.5.5-1 requires, so the run does not take Paho's answer there.
