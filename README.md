# mqtt

A Lean parser for MQTT 5.0 packet framing. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

MQTT 5.0 packets over TCP. Fixed header, remaining length as a variable byte integer capped at four bytes, and packet types CONNECT, PUBLISH, SUBSCRIBE, SUBACK, PINGREQ, PINGRESP, and DISCONNECT first. Properties are parsed per packet type. A property on a packet type that does not allow it is rejected.

This is distinct from the websocket repo. MQTT can run over websockets as a transport, but this slice is MQTT packets over TCP, not websocket frames.

## Main claim

Decoding an encoding gives the same packet back. The decoder returns an error instead of reading past the end of its input. A variable byte integer longer than four bytes is rejected.

## Test oracles

- Eclipse Paho clients.
- The Mosquitto broker test suite.
- MQTT 5.0 specification test material.

## Score

16 out of 18, first pass score in mission issue 19, the round 4 sheet. Created at the org owner's direction on that sheet, on the judgement that the slice, claim, and oracles are sound and that it duplicates no existing repo.

## What is not in this slice

- A broker.
- Session state.
- Delivery guarantees.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
