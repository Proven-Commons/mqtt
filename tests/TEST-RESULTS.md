# Test results: mqtt

Seed: 20261026. Tool: the Lean command line program, one process per section, requests batched. The harness checks parsed structure through the re-encoding the tool prints, together with its own oracle.

Paho's Python library (`paho-mqtt`, version 2.1.0) was importable in the interpreter that ran this harness; the Paho cross-check ran. It covers variable byte integers and PUBLISH property blocks, the pieces the library exposes without a broker.

Mosquitto was NOT present on this machine (no `mosquitto` or `mosquitto_sub` binary), so no Mosquitto tests ran.

| Section | Inputs | Agreements |
| --- | --- | --- |
| Fixed cases (spec VBI table, one packet per type, richer hand built packets) | 30 | 30 |
| Oracle differential, random packets of all seven types (seed 20261026) | 3000 | 3000 |
| Paho 2.1.0 cross-check (variable byte integers and PUBLISH property blocks) | 629 | 629 |
| Mutations and named rejections, settled by the oracle | 258 | 258 |
| Line protocol cases | 9 | 9 |

Named differences from the oracles:
- Paho's variable byte integer decoder also accepts the non-minimal encoding 128, 0 as the value 0, matching the pinned reading in SPEC.md.

Failures: none.
