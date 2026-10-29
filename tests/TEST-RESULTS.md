# Test results: mqtt

- Oracle: the strict reference decoder and encoder in tests/run_tests.py, written from the OASIS MQTT Version 5.0 standard (OASIS Standard, 7 March 2019) and SPEC.md, run on Python 3.13.17; with a cross-check against paho-mqtt 2.1.0, counted apart
- Seed: 20261026
- Inputs: 4855
- Failures: 0

Tool: the Lean command line program, one process per section, requests batched. The harness checks parsed structure through the re-encoding the tool prints, together with its own oracle, and checks that every input the tool accepts among the mutations and named cases reprints byte for byte. Inputs counts the sections that run on every machine.

Paho's Python library (`paho-mqtt`, version 2.1.0) was importable in the interpreter that ran this harness; the Paho cross-check ran. Each of its inputs compares an answer of the Lean tool with Paho's: Paho's encoder output for variable byte integers must come back unchanged, and Paho's Properties.unpack judges property blocks of all six kinds, accepted and refused, the pieces the library exposes without a broker. It does not judge whole packets. Its inputs are listed below and are not part of Inputs.

The plan's third oracle, MQTT 5.0 specification test material, was NOT used: the standard ships no conformance test suite, and the nearest material, the MQTTV5 codec in Eclipse paho.mqtt.testing, is not wired into this harness.

Mosquitto was NOT present on this machine (no `mosquitto` or `mosquitto_sub` binary), so no Mosquitto tests ran.

| Section | Inputs | Agreements |
| --- | --- | --- |
| Fixed cases (spec VBI table, one packet per type, richer hand built packets) | 37 | 37 |
| Oracle differential, random packets of all seven types (seed 20261026) | 3000 | 3000 |
| Mutations and named rejections, settled by the oracle | 325 | 325 |
| Forbidden classes drawn from the seed (property values, Response Topics, Authentication Data, topic filters of 1 to 6 levels), with controls, settled by the oracle | 1484 | 1484 |
| Line protocol cases | 9 | 9 |
| Paho 2.1.0 cross-check, each a Lean answer judged by Paho: its variable byte integer writings as Subscription Identifiers, and property blocks of all six kinds judged by Properties.unpack (Lean accepted 375, refused 352; not counted in Inputs) | 727 | 727 |

Named differences from the oracles:
- Payload Format Indicator 2 on PUBLISH, and the like: section 3.3.2.3.2 names 0 and 1 but does not call another value a Protocol Error, so this reader accepts it; Paho refuses it. Checked on single blocks, not counted as comparisons.
- Response Topic with a wildcard on PUBLISH, and the like: MQTT-3.3.2-14 forbids wildcards in a Response Topic and 4.7.3-1 an empty one, so this reader refuses them; Paho accepts them. Checked on single blocks, not counted as comparisons.
- Authentication Data without a Method on CONNECT, and the like: section 3.1.2.11.10 makes Authentication Data without an Authentication Method a Protocol Error, so this reader refuses it; Paho accepts it. Checked on single blocks, not counted as comparisons.
- Maximum Packet Size 4294967295 on CONNECT, and the like: section 3.1.2.11.4 makes the Maximum Packet Size a Four Byte Integer and calls only 0 (or a repeat) a Protocol Error, so this reader accepts values up to 2^32 - 1; Paho refuses those above 268435455. Checked on single blocks, not counted as comparisons.
- two Subscription Identifiers on SUBSCRIBE, and the like: section 3.8.2.1.2 makes a second Subscription Identifier on SUBSCRIBE a Protocol Error, so this reader refuses it; Paho allows the repeat on any packet. Checked on single blocks, not counted as comparisons.
- paho-mqtt's VariableByteIntegers.decode reads the longer writing 128, 0 as (0, 2) (value, bytes read); this reader refuses that writing, as MQTT-1.5.5-1 requires (the fixed cases check it), so the property blocks Paho judges hold only shortest writings.
