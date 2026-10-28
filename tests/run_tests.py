#!/usr/bin/env python3
"""Test harness for the Lean MQTT 5.0 packet codec.

Layers, all settled against independent expectations:

1. Fixed cases: the variable byte integer table from section
   2.1.4 of the standard, hand built packets for each of the
   seven packet types in this slice, and the DISCONNECT one
   byte body form, which is legal and reprints as it came.

2. A differential against a strict oracle written here from
   the standard and from SPEC.md: random packets of all seven
   types with varied properties are encoded by the oracle,
   read by the Lean tool, and the answer must be the same
   bytes reprinted.

3. A cross-check against Paho's Python library when it is
   importable, in which Paho judges each Lean answer: variable
   byte integers written by its encoder are fed to the Lean
   tool as Subscription Identifiers and must come back
   unchanged, and property blocks of all six kinds, accepted
   and refused, are judged by Paho's Properties.unpack and by
   the Lean tool, whose verdicts must agree. The classes where
   Paho departs from the standard are checked apart for their
   documented direction, as named differences. When the
   library is absent, the run says so and the oracle carries
   accept and reject alone. The Mosquitto
   test suite is a separate program, not a Python library; the
   run checks for its binary and the results file states
   whether it was present.

Mutations of rich packets (truncation at every length, byte
flips at every position) and a list of named rejection cases
are settled by comparing the Lean answer with the oracle's
answer on the same bytes.

Forbidden classes are drawn from the seed as well: random valid
packets with one rule broken, for every Request Problem
Information and Request Response Information value from 2 to
255, the value 0 of the Subscription Identifier, Receive
Maximum, Topic Alias and Maximum Packet Size, Response Topics
with a wildcard or empty, Authentication Data without a Method,
and topic filters of 1 to 6 levels that break a wildcard or
shared subscription rule. The oracle settles them, and the run
checks that the oracle's own rule checks (prop_value_ok,
filter_ok) call each one forbidden. Controls that keep the rule
must be accepted.

Results are written to tests/TEST-RESULTS.md. Seed 20261026.

Usage: python3 tests/run_tests.py [--skip-build]
Run it with the work directory's virtual environment
(./venv/bin/python tests/run_tests.py) to get the Paho
cross-check; without the library that part is skipped and
the results file says so.
"""

import os
import random
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXE = os.path.join(ROOT, ".lake", "build", "bin", "mqtt")
SEED = 20261026

failures = []
paho_named = []


def check(cond, label, detail=""):
    if not cond:
        failures.append(f"{label}: {detail}")
        print(f"FAIL {label}: {detail}")


# ---------------------------------------------------------------------------
# Batch runner: one process for many requests.
# ---------------------------------------------------------------------------

class Tool:
    def __init__(self):
        self.lines = []

    def ask(self, line):
        self.lines.append(line)
        return len(self.lines) - 1

    def run(self):
        proc = subprocess.run([EXE], input="\n".join(self.lines) + "\n",
                              capture_output=True, text=True, timeout=1200)
        if proc.returncode != 0:
            raise RuntimeError(f"tool exited {proc.returncode}: {proc.stderr[:500]}")
        self.answers = proc.stdout.splitlines()
        if len(self.answers) != len(self.lines):
            raise RuntimeError(
                f"answer count {len(self.answers)} != request count {len(self.lines)}")
        return self.answers


def req(bs):
    return "parse " + ",".join(str(b) for b in bs)


def want_ok(canon):
    return "ok:" + ",".join(str(b) for b in canon)


# ---------------------------------------------------------------------------
# Oracle: canonical encoder and strict decoder, written from the
# MQTT 5.0 standard and SPEC.md.
#
# Packet representation:
#   ("connect", clean, keep_alive, props, client_id, will,
#               username, password)
#     will is None or (qos, retain, props, topic, payload bytes)
#     username is None or str; password is None or bytes
#   ("publish", dup, qos, retain, topic, packet_id, props, payload)
#     packet_id is None at QoS 0
#   ("subscribe", packet_id, props, filters)
#     filters is a list of (str, (qos, no_local, retain_as_published,
#                                  retain_handling))
#   ("suback", packet_id, props, [reason, ...])
#   ("pingreq",)  ("pingresp",)
#   ("disconnect", None), ("disconnect", (reason, None)) for the
#     one byte body, or ("disconnect", (reason, props))
# A property is (id, value): an int for byte, two byte, four byte,
# and variable byte integer values; a str for a UTF-8 string value;
# a (str, str) pair for a user property; bytes for binary data.
# ---------------------------------------------------------------------------

class Reject(Exception):
    pass


def enc_vbi(n):
    out = bytearray()
    while True:
        d = n % 128
        n //= 128
        if n:
            out.append(d + 128)
        else:
            out.append(d)
            return bytes(out)


def dec_vbi(bs, i):
    """Section 1.5.5: at most four bytes, and the writing must be
    the shortest one for its value [MQTT-1.5.5-1], checked here
    by writing the value again and comparing."""
    start = i
    value = 0
    mult = 1
    for _ in range(4):
        if i >= len(bs):
            raise Reject()
        b = bs[i]
        i += 1
        value += (b % 128) * mult
        if b < 128:
            if enc_vbi(value) != bytes(bs[start:i]):
                raise Reject()
            return value, i
        mult *= 128
    raise Reject()


def be16(n):
    return n.to_bytes(2, "big")


def dec_uint(bs, i, w):
    if i + w > len(bs):
        raise Reject()
    return int.from_bytes(bs[i:i + w], "big"), i + w


def enc_str(s):
    raw = s.encode("utf-8")
    return be16(len(raw)) + raw


def dec_str(bs, i):
    ln, i = dec_uint(bs, i, 2)
    if i + ln > len(bs):
        raise Reject()
    raw = bytes(bs[i:i + ln])
    try:
        s = raw.decode("utf-8")
    except UnicodeDecodeError:
        raise Reject()
    if "\x00" in s:
        raise Reject()
    return s, i + ln


def enc_bin(b):
    return be16(len(b)) + bytes(b)


def dec_bin(bs, i):
    ln, i = dec_uint(bs, i, 2)
    if i + ln > len(bs):
        raise Reject()
    return bytes(bs[i:i + ln]), i + ln


PROP_TYPE = {
    0x01: "byte", 0x02: "four", 0x03: "utf8", 0x08: "utf8",
    0x09: "binary", 0x0B: "var", 0x11: "four", 0x12: "utf8",
    0x13: "two", 0x15: "utf8", 0x16: "binary", 0x17: "byte",
    0x18: "four", 0x19: "byte", 0x1A: "utf8", 0x1C: "utf8",
    0x1F: "utf8", 0x21: "two", 0x22: "two", 0x23: "two",
    0x24: "byte", 0x25: "byte", 0x26: "pair", 0x27: "four",
    0x28: "byte", 0x29: "byte", 0x2A: "byte",
}

ALLOWED = {
    "connect": [0x11, 0x15, 0x16, 0x17, 0x19, 0x21, 0x22, 0x26, 0x27],
    "will": [0x01, 0x02, 0x03, 0x08, 0x09, 0x18, 0x26],
    "publish": [0x01, 0x02, 0x03, 0x08, 0x09, 0x0B, 0x23, 0x26],
    "subscribe": [0x0B, 0x26],
    "suback": [0x1F, 0x26],
    "disconnect": [0x11, 0x1C, 0x1F, 0x26],
}


def repeatable(setname, pid):
    return pid == 0x26 or (pid == 0x0B and setname == "publish")


def prop_value_ok(pid, v):
    """The value rules the standard sets on single property values
    (SPEC.md, Properties): a value breaking one is a Protocol
    Error."""
    if pid == 0x08:
        # Response Topic: used as a Topic Name (3.3.2.3.5, 4.7).
        return v != "" and "+" not in v and "#" not in v
    if pid in (0x0B, 0x21, 0x23, 0x27):
        # Subscription Identifier (3.3.2.3.8, 3.8.2.1.2), Receive
        # Maximum (3.1.2.11.3), Topic Alias (3.3.2.3.4), Maximum
        # Packet Size (3.1.2.11.4): never 0.
        return v != 0
    if pid in (0x17, 0x19):
        # Request Problem Information, Request Response
        # Information (3.1.2.11.7, 3.1.2.11.6): 0 or 1.
        return v in (0, 1)
    return True


def enc_prop_val(t, v):
    if t == "byte":
        return bytes([v])
    if t == "two":
        return be16(v)
    if t == "four":
        return v.to_bytes(4, "big")
    if t == "var":
        return enc_vbi(v)
    if t == "utf8":
        return enc_str(v)
    if t == "pair":
        return enc_str(v[0]) + enc_str(v[1])
    if t == "binary":
        return enc_bin(v)
    raise ValueError(t)


def dec_prop_val(t, bs, i):
    if t == "byte":
        return dec_uint(bs, i, 1)
    if t == "two":
        return dec_uint(bs, i, 2)
    if t == "four":
        return dec_uint(bs, i, 4)
    if t == "var":
        return dec_vbi(bs, i)
    if t == "utf8":
        return dec_str(bs, i)
    if t == "pair":
        k, i = dec_str(bs, i)
        v, i = dec_str(bs, i)
        return (k, v), i
    if t == "binary":
        return dec_bin(bs, i)
    raise ValueError(t)


def enc_props(ps):
    body = b"".join(enc_vbi(pid) + enc_prop_val(PROP_TYPE[pid], v)
                    for pid, v in ps)
    return enc_vbi(len(body)) + body


def dec_props(setname, bs, i):
    ln, i = dec_vbi(bs, i)
    if i + ln > len(bs):
        raise Reject()
    seg = bytes(bs[i:i + ln])
    end = i + ln
    ps = []
    seen = []
    j = 0
    while j < len(seg):
        pid, j = dec_vbi(seg, j)
        if pid not in PROP_TYPE or pid not in ALLOWED[setname]:
            raise Reject()
        if pid in seen and not repeatable(setname, pid):
            raise Reject()
        seen.append(pid)
        v, j = dec_prop_val(PROP_TYPE[pid], seg, j)
        if not prop_value_ok(pid, v):
            raise Reject()
        ps.append((pid, v))
    if j != len(seg):
        raise Reject()
    # Authentication Data only with an Authentication Method
    # (3.1.2.11.10).
    if 0x16 in seen and 0x15 not in seen:
        raise Reject()
    return ps, end


def filter_ok(f, no_local):
    """The topic filter rules of sections 4.7.1, 4.7.3, 4.8.2 and
    3.8.3.1, written from the standard's text."""
    if f.startswith("$share/"):
        rest = f[len("$share/"):]
        if "/" not in rest:
            return False      # ShareName followed by "/" [MQTT-4.8.2-2]
        name, f = rest.split("/", 1)
        if name == "" or "+" in name or "#" in name:
            return False      # [MQTT-4.8.2-1] [MQTT-4.8.2-2]
        if no_local:
            return False      # [MQTT-3.8.3-4]
    if f == "":
        return False          # [MQTT-4.7.3-1]
    levels = f.split("/")
    for k, level in enumerate(levels):
        if "+" in level and level != "+":
            return False      # [MQTT-4.7.1-2]
        if "#" in level and (level != "#" or k != len(levels) - 1):
            return False      # [MQTT-4.7.1-1]
    return True


def check_topic(s):
    if s == "" or "+" in s or "#" in s:
        raise Reject()
    return s


def flagbit(n, k):
    return (n // (2 ** k)) % 2 == 1


def enc_opts(o):
    qos, no_local, rap, rh = o
    return qos + (4 if no_local else 0) + (8 if rap else 0) + rh * 16


def dec_opts(b):
    if b >= 64 or b % 4 == 3 or (b // 16) % 4 == 3:
        raise Reject()
    return (b % 4, (b // 4) % 2 == 1, (b // 8) % 2 == 1, (b // 16) % 4)


def enc_packet(pkt):
    tag = pkt[0]
    if tag == "connect":
        _, clean, ka, props, cid, will, username, password = pkt
        flags = ((128 if username is not None else 0)
                 + (64 if password is not None else 0)
                 + ((32 if will[1] else 0) + will[0] * 8 + 4
                    if will is not None else 0)
                 + (2 if clean else 0))
        body = enc_str("MQTT") + bytes([5, flags]) + be16(ka)
        body += enc_props(props)
        body += enc_str(cid)
        if will is not None:
            body += enc_props(will[2]) + enc_str(will[3]) + enc_bin(will[4])
        if username is not None:
            body += enc_str(username)
        if password is not None:
            body += enc_bin(password)
        header = 0x10
    elif tag == "publish":
        _, dup, qos, retain, topic, pid, props, payload = pkt
        header = 0x30 + (8 if dup else 0) + qos * 2 + (1 if retain else 0)
        body = enc_str(topic)
        if pid is not None:
            body += be16(pid)
        body += enc_props(props) + bytes(payload)
    elif tag == "subscribe":
        _, pid, props, filters = pkt
        header = 0x82
        body = be16(pid) + enc_props(props)
        for f, o in filters:
            body += enc_str(f) + bytes([enc_opts(o)])
    elif tag == "suback":
        _, pid, props, reasons = pkt
        header = 0x90
        body = be16(pid) + enc_props(props) + bytes(reasons)
    elif tag == "pingreq":
        header, body = 0xC0, b""
    elif tag == "pingresp":
        header, body = 0xD0, b""
    elif tag == "disconnect":
        header = 0xE0
        if pkt[1] is None:
            body = b""
        elif pkt[1][1] is None:
            body = bytes([pkt[1][0]])
        else:
            body = bytes([pkt[1][0]]) + enc_props(pkt[1][1])
    else:
        raise ValueError(tag)
    return bytes([header]) + enc_vbi(len(body)) + body


def raw_packet(header, body):
    return bytes([header]) + enc_vbi(len(body)) + bytes(body)


def dec_connect(seg):
    proto, i = dec_str(seg, 0)
    if proto != "MQTT":
        raise Reject()
    level, i = dec_uint(seg, i, 1)
    if level != 5:
        raise Reject()
    flags, i = dec_uint(seg, i, 1)
    if flags % 2 != 0 or (flags // 8) % 4 == 3:
        raise Reject()
    # With the will flag clear, will QoS and will retain are 0
    # [MQTT-3.1.2-11] [MQTT-3.1.2-13].
    if not flagbit(flags, 2) and (flags & 0x38) != 0:
        raise Reject()
    ka, i = dec_uint(seg, i, 2)
    props, i = dec_props("connect", seg, i)
    cid, i = dec_str(seg, i)
    will = None
    if flagbit(flags, 2):
        wprops, i = dec_props("will", seg, i)
        wtopic, i = dec_str(seg, i)
        check_topic(wtopic)
        wpay, i = dec_bin(seg, i)
        will = ((flags // 8) % 4, flagbit(flags, 5), wprops, wtopic, wpay)
    username = None
    if flagbit(flags, 7):
        username, i = dec_str(seg, i)
    password = None
    if flagbit(flags, 6):
        password, i = dec_bin(seg, i)
    if i != len(seg):
        raise Reject()
    return ("connect", flagbit(flags, 1), ka, props, cid, will,
            username, password)


def dec_publish(flags, seg):
    topic, i = dec_str(seg, 0)
    # No wildcard in a Topic Name [MQTT-3.3.2-2]; an empty one
    # needs a Topic Alias, checked after the properties (3.3.2.1).
    if "+" in topic or "#" in topic:
        raise Reject()
    qos = (flags // 2) % 4
    # DUP is 0 for all QoS 0 messages [MQTT-3.3.1-2].
    if qos == 0 and flagbit(flags, 3):
        raise Reject()
    pid = None
    if qos != 0:
        pid, i = dec_uint(seg, i, 2)
        if pid == 0:
            raise Reject()
    props, i = dec_props("publish", seg, i)
    if topic == "" and not any(p == 0x23 for p, _ in props):
        raise Reject()
    return ("publish", flagbit(flags, 3), qos, flagbit(flags, 0),
            topic, pid, props, bytes(seg[i:]))


def dec_subscribe(seg):
    pid, i = dec_uint(seg, 0, 2)
    if pid == 0:
        raise Reject()
    props, i = dec_props("subscribe", seg, i)
    filters = []
    while i < len(seg):
        f, i = dec_str(seg, i)
        if i >= len(seg):
            raise Reject()
        o = dec_opts(seg[i])
        i += 1
        if not filter_ok(f, o[1]):
            raise Reject()
        filters.append((f, o))
    if not filters:
        raise Reject()
    return ("subscribe", pid, props, filters)


def dec_suback(seg):
    pid, i = dec_uint(seg, 0, 2)
    if pid == 0:
        raise Reject()
    props, i = dec_props("suback", seg, i)
    reasons = list(seg[i:])
    if not reasons:
        raise Reject()
    return ("suback", pid, props, reasons)


def dec_disconnect(seg):
    if len(seg) == 0:
        return ("disconnect", None)
    if len(seg) == 1:
        # No property length when the remaining length is below 2
        # (3.14.2.2.1).
        return ("disconnect", (seg[0], None))
    props, j = dec_props("disconnect", seg, 1)
    if j != len(seg):
        raise Reject()
    return ("disconnect", (seg[0], props))


def oracle_parse(bs):
    """The whole input form: exactly one packet, nothing after it.
    Returns the packet, or None when the oracle rejects."""
    try:
        if not bs:
            return None
        header = bs[0]
        ln, i = dec_vbi(bs, 1)
        if i + ln > len(bs):
            return None
        seg = bytes(bs[i:i + ln])
        rest = i + ln
        typ, flags = header // 16, header % 16
        if typ == 1 and flags == 0:
            pkt = dec_connect(seg)
        elif typ == 3 and (flags // 2) % 4 != 3:
            pkt = dec_publish(flags, seg)
        elif typ == 8 and flags == 2:
            pkt = dec_subscribe(seg)
        elif typ == 9 and flags == 0:
            pkt = dec_suback(seg)
        elif typ == 12 and flags == 0 and not seg:
            pkt = ("pingreq",)
        elif typ == 13 and flags == 0 and not seg:
            pkt = ("pingresp",)
        elif typ == 14 and flags == 0:
            pkt = dec_disconnect(seg)
        else:
            return None
    except Reject:
        return None
    if rest != len(bs):
        return None
    return pkt


def settled_answer(bs):
    pkt = oracle_parse(bs)
    return want_ok(enc_packet(pkt)) if pkt is not None else "none"


# ---------------------------------------------------------------------------
# Random packets.
# ---------------------------------------------------------------------------

TEXT = "abcdefgXYZ 019._-/"
UNICODE = ["é", "ü", "世", "☕"]


def rand_text(rng, lo=0, hi=10, topic_safe=False):
    n = rng.randint(lo, hi)
    pool = TEXT if topic_safe else TEXT + "".join(UNICODE)
    return "".join(rng.choice(pool) for _ in range(n))


def rand_topic(rng):
    parts = [rand_text(rng, 1, 5, topic_safe=True)
             for _ in range(rng.randint(1, 3))]
    return "/".join(parts)


def rand_filter(rng):
    """A random topic filter that keeps the filter rules: `+` as a
    whole level anywhere, `#` only as the whole last level, and
    now and then a shared subscription prefix. Broken filters are
    forbidden packets, which the named rejection cases cover."""
    n = rng.randint(1, 3)
    parts = []
    for k in range(n):
        choices = ["+", rand_text(rng, 1, 4, topic_safe=True)]
        if k == n - 1:
            choices.append("#")
        parts.append(rng.choice(choices))
    f = "/".join(parts)
    if rng.random() < 0.15:
        name = "".join(rng.choice("abcdefgXYZ019._-")
                       for _ in range(rng.randint(1, 4)))
        f = "$share/" + name + "/" + f
    return f


def rand_bytes(rng, hi=12):
    return bytes(rng.randrange(256) for _ in range(rng.randint(0, hi)))


def rand_prop_value(rng, pid):
    """A random value for a property, kept to the standard's value
    rules: a value that breaks one is a forbidden packet, which
    the named rejection cases cover instead."""
    while True:
        if pid == 0x08:
            v = rand_topic(rng)
        else:
            v = rand_typed_value(rng, PROP_TYPE[pid])
        if prop_value_ok(pid, v):
            return v


def rand_typed_value(rng, t):
    if t == "byte":
        return rng.choice([0, 1, 2, 255, rng.randrange(256)])
    if t == "two":
        return rng.choice([0, 1, 256, 65535, rng.randrange(65536)])
    if t == "four":
        return rng.choice([0, 1, 65536, 4294967295,
                           rng.randrange(1 << 32)])
    if t == "var":
        return rng.choice([0, 1, 127, 128, 16383, 16384, 2097151,
                           268435455, rng.randrange(1 << 28)])
    if t == "utf8":
        return rand_text(rng, 0, 8)
    if t == "pair":
        return (rand_text(rng, 1, 5), rand_text(rng, 0, 5))
    if t == "binary":
        return rand_bytes(rng, 8)
    raise ValueError(t)


def rand_props(rng, setname):
    ids = list(ALLOWED[setname])
    rng.shuffle(ids)
    ids = ids[:rng.randint(0, min(4, len(ids)))]
    if 0x16 in ids and 0x15 not in ids:
        ids.append(0x15)
    ps = []
    for pid in ids:
        ps.append((pid, rand_prop_value(rng, pid)))
        if repeatable(setname, pid) and rng.random() < 0.4:
            ps.append((pid, rand_prop_value(rng, pid)))
    return ps


def rand_packet(rng):
    tag = rng.choice(["connect", "publish", "publish", "subscribe",
                      "suback", "pingreq", "pingresp", "disconnect"])
    if tag == "connect":
        will = None
        if rng.random() < 0.5:
            will = (rng.randint(0, 2), rng.random() < 0.5,
                    rand_props(rng, "will"), rand_topic(rng),
                    rand_bytes(rng))
        return ("connect", rng.random() < 0.5,
                rng.choice([0, 1, 60, 65535, rng.randrange(65536)]),
                rand_props(rng, "connect"), rand_text(rng, 0, 8), will,
                rand_text(rng, 1, 6) if rng.random() < 0.4 else None,
                rand_bytes(rng) if rng.random() < 0.4 else None)
    if tag == "publish":
        qos = rng.choice([0, 1, 2])
        # DUP only at QoS 1 and 2: at QoS 0 it is a forbidden
        # packet, which the named rejection cases cover.
        props = rand_props(rng, "publish")
        topic = rand_topic(rng)
        # Now and then an empty topic name with a Topic Alias,
        # which section 3.3.2.1 allows.
        if rng.random() < 0.1:
            topic = ""
            if not any(p == 0x23 for p, _ in props):
                props.append((0x23, rand_prop_value(rng, 0x23)))
        return ("publish", qos != 0 and rng.random() < 0.5, qos,
                rng.random() < 0.5, topic,
                rng.randint(1, 65535) if qos else None,
                props, rand_bytes(rng, 20))
    if tag == "subscribe":
        filters = []
        for _ in range(rng.randint(1, 3)):
            f = rand_filter(rng)
            # No Local is not set on a shared subscription
            # [MQTT-3.8.3-4].
            no_local = (not f.startswith("$share/")) and rng.random() < 0.5
            filters.append((f, (rng.randint(0, 2), no_local,
                                rng.random() < 0.5, rng.randint(0, 2))))
        return ("subscribe", rng.randint(1, 65535),
                rand_props(rng, "subscribe"), filters)
    if tag == "suback":
        return ("suback", rng.randint(1, 65535),
                rand_props(rng, "suback"),
                [rng.choice([0, 1, 2, 128, 131, 135, 144, 161,
                             rng.randrange(256)])
                 for _ in range(rng.randint(1, 4))])
    if tag == "pingreq":
        return ("pingreq",)
    if tag == "pingresp":
        return ("pingresp",)
    if rng.random() < 0.3:
        return ("disconnect", None)
    reason = rng.choice([0, 4, 129, 135, 142, rng.randrange(256)])
    if rng.random() < 0.3:
        return ("disconnect", (reason, None))
    return ("disconnect", (reason, rand_props(rng, "disconnect")))


# ---------------------------------------------------------------------------
# Test sections.
# ---------------------------------------------------------------------------

VBI_TABLE = [
    (0, [0]), (127, [127]), (128, [128, 1]), (16383, [255, 127]),
    (16384, [128, 128, 1]), (2097151, [255, 255, 127]),
    (2097152, [128, 128, 128, 1]),
    (268435455, [255, 255, 255, 127]),
]


def fixed_cases():
    tool = Tool()
    entries = []

    def add(label, bs, expected=None):
        idx = tool.ask(req(bs))
        entries.append((label, idx,
                        expected if expected is not None
                        else want_ok(bytes(bs))))

    # The section 2.1.4 table, checked at the oracle first, then
    # exercised through the tool as Subscription Identifier values
    # on SUBSCRIBE packets, and as remaining lengths where the
    # body size is practical.
    for value, enc in VBI_TABLE:
        check(list(enc_vbi(value)) == enc, f"fixed/vbi {value}",
              "oracle encoder differs from the spec table")
        pkt = ("subscribe", 1, [(0x0B, value)],
               [("a", (0, False, False, 0))])
        if value == 0:
            # A Subscription Identifier of 0 is a Protocol Error.
            add("vbi 0 as a subscription identifier, refused",
                enc_packet(pkt), "none")
        else:
            add(f"vbi {value} as a property value", enc_packet(pkt))
    for value in (0, 127, 128, 16383, 16384):
        if value == 0:
            add("remaining length 0", bytes([192, 0]))
        else:
            body_len = value
            payload = bytes(body_len - 4)
            pkt = ("publish", False, 0, False, "a", None, [], payload)
            bs = enc_packet(pkt)
            check(list(bs[1:1 + len(enc_vbi(value))]) == list(enc_vbi(value)),
                  f"fixed/remaining length {value}", "header bytes differ")
            add(f"remaining length {value}", bs)
    # Section 1.5.5: a writing longer than the value needs is
    # refused, wherever a variable byte integer stands.
    add("vbi non-minimal 134,0 as remaining length",
        bytes([48, 134, 0, 0, 1, 97, 0, 1, 2]), "none")
    add("vbi non-minimal 128,0 as remaining length",
        bytes([192, 128, 0]), "none")
    add("vbi non-minimal 128,128,0 as remaining length",
        bytes([192, 128, 128, 0]), "none")
    add("vbi non-minimal 128,0 as property length",
        bytes([48, 5, 0, 1, 97, 128, 0]), "none")
    add("vbi non-minimal 129,0 as property identifier",
        bytes([48, 7, 0, 1, 97, 3, 129, 0, 1]), "none")
    add("vbi non-minimal 129,128,0 as subscription identifier",
        bytes([130, 10, 0, 1, 3, 11, 129, 128, 0, 0, 1, 97, 0]), "none")
    add("vbi with rest in one packet stream position",
        bytes([192, 0]), want_ok(bytes([192, 0])))

    # One hand built packet per type; the literal ones are the
    # same bytes proved in Proofs/Examples.lean.
    add("pingreq", bytes([192, 0]))
    add("pingresp", bytes([208, 0]))
    add("disconnect empty", bytes([224, 0]))
    add("disconnect reason only, reprinted as it came",
        bytes([224, 1, 0]))
    add("disconnect reason 142 only", bytes([224, 1, 142]))
    add("disconnect reason and empty properties", bytes([224, 2, 0, 0]))
    add("publish qos0", bytes([48, 6, 0, 1, 97, 0, 1, 2]))
    add("publish qos1", bytes([50, 6, 0, 1, 97, 0, 1, 0]))
    add("subscribe one filter", bytes([130, 7, 0, 1, 0, 0, 1, 97, 0]))
    add("suback", bytes([144, 4, 0, 1, 0, 0]))
    add("connect plain",
        bytes([16, 14, 0, 4, 77, 81, 84, 84, 5, 2, 0, 0, 0, 0, 1, 120]))

    richer = [
        ("connect with will, username, password",
         ("connect", True, 60,
          [(0x11, 3600), (0x26, ("k", "v"))], "client-1",
          (1, True, [(0x18, 30), (0x03, "text/plain")],
           "last/will", b"\x01\x02"),
          "user", b"secret")),
        ("publish qos2 with properties",
         ("publish", True, 2, True, "sensors/temp", 4242,
          [(0x01, 1), (0x02, 600), (0x0B, 7), (0x0B, 9),
           (0x26, ("a", "b")), (0x23, 3)], b"hello")),
        ("subscribe two filters",
         ("subscribe", 9, [(0x0B, 12)],
          [("sensors/+", (1, True, False, 1)),
           ("alerts/#", (2, False, True, 2))])),
        ("suback with reason string",
         ("suback", 9, [(0x1F, "done")], [0, 1, 128])),
        ("disconnect with properties",
         ("disconnect", (142, [(0x11, 0), (0x1F, "bye")]))),
        ("disconnect reason with empty properties",
         ("disconnect", (0, []))),
    ]
    for label, pkt in richer:
        bs = enc_packet(pkt)
        check(oracle_parse(bs) == pkt, f"fixed/{label}",
              "oracle does not read its own packet back")
        add(label, bs)

    answers = tool.run()
    for label, idx, expected in entries:
        check(answers[idx] == expected, f"fixed/{label}",
              f"got {answers[idx]}, want {expected}")
    return len(entries)


def oracle_differential(rng, count):
    tool = Tool()
    entries = []
    for _ in range(count):
        pkt = rand_packet(rng)
        bs = enc_packet(pkt)
        idx = tool.ask(req(bs))
        entries.append((idx, want_ok(bs), pkt[0]))
    answers = tool.run()
    agree = 0
    seen_types = set()
    for idx, expected, tag in entries:
        seen_types.add(tag)
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, "oracle differential",
                  f"got {answers[idx]}, want {expected}")
    check(seen_types == {"connect", "publish", "subscribe", "suback",
                         "pingreq", "pingresp", "disconnect"},
          "oracle differential coverage", f"types seen: {seen_types}")
    return len(entries), agree


PAHO_PACKET = {"connect": "CONNECT", "will": "WILLMESSAGE",
               "publish": "PUBLISH", "subscribe": "SUBSCRIBE",
               "suback": "SUBACK", "disconnect": "DISCONNECT"}

UNKNOWN_IDS = [0x00, 0x04, 0x07, 0x0A, 0x2B, 0x30, 0x7F]


def block_packet(setname, block):
    """A valid packet around the raw property block `block` (its
    length included), standing as the block of kind `setname`."""
    if setname == "connect":
        return raw_packet(0x10, enc_str("MQTT") + bytes([5, 2]) + be16(0)
                          + block + enc_str("c"))
    if setname == "will":
        return raw_packet(0x10, enc_str("MQTT") + bytes([5, 6]) + be16(0)
                          + b"\x00" + enc_str("c") + block + enc_str("w")
                          + enc_bin(b""))
    if setname == "publish":
        return raw_packet(0x30, enc_str("a") + block + b"x")
    if setname == "subscribe":
        return raw_packet(0x82, be16(1) + block + enc_str("a") + b"\x00")
    if setname == "suback":
        return raw_packet(0x90, be16(1) + block + b"\x00")
    if setname == "disconnect":
        return raw_packet(0xE0, b"\x00" + block)
    raise ValueError(setname)


def raw_block(entries):
    """A property block from (identifier, value) pairs, any
    identifier, written as given: an unknown identifier gets one
    value byte."""
    body = b""
    for pid, v in entries:
        if pid in PROP_TYPE:
            body += enc_vbi(pid) + enc_prop_val(PROP_TYPE[pid], v)
        else:
            body += enc_vbi(pid) + bytes([v])
    return enc_vbi(len(body)) + body


def judge_entries(rng, setname):
    """Random properties for a block of kind `setname`, for Paho
    to judge: mostly allowed ones, some known identifiers that the
    block does not allow, some unknown identifiers, values drawn
    across their whole width (so forbidden values such as 0 come
    up), and now and then a repeat. The five classes where Paho
    departs from the standard are left out here and checked on
    their own: a Payload Format Indicator above 1, a Response
    Topic that is empty or holds a wildcard, Authentication Data
    without a Method, a repeated Subscription Identifier on
    SUBSCRIBE, and a Maximum Packet Size above 268435455."""
    out = []
    for _ in range(rng.randint(0, 4)):
        r = rng.random()
        if r < 0.65:
            pid = rng.choice(ALLOWED[setname])
        elif r < 0.92:
            pid = rng.choice(sorted(PROP_TYPE))
        else:
            out.append((rng.choice(UNKNOWN_IDS), rng.randrange(256)))
            continue
        if pid == 0x01:
            v = rng.randint(0, 1)
        elif pid == 0x27:
            v = rng.choice([0, 1, 65536, rng.randrange(1, 1 << 28)])
        elif pid == 0x08:
            v = rand_topic(rng)
        else:
            v = rand_typed_value(rng, PROP_TYPE[pid])
        out.append((pid, v))
        if rng.random() < 0.15:
            out.append((pid, v if pid in (0x01, 0x08, 0x27)
                        else rand_typed_value(rng, PROP_TYPE[pid])))
    ids = [i for i, _ in out]
    if 0x16 in ids and 0x15 not in ids:
        out.append((0x15, rand_text(rng, 1, 4, topic_safe=True)))
    if setname == "subscribe" and ids.count(0x0B) > 1:
        first = ids.index(0x0B)
        out = [e for k, e in enumerate(out) if e[0] != 0x0B or k == first]
    rng.shuffle(out)
    return out


def paho_section(rng, count_blocks):
    """Cross-checks in which Paho judges an answer of the Lean
    tool. Returns (comparisons, agreements, accepted, refused).

    1. Paho's encoder writes variable byte integers; each, as the
       Subscription Identifier of a SUBSCRIBE, must be accepted
       by the Lean tool and reprinted as the same bytes.
    2. Paho's Properties.unpack judges property blocks of all six
       kinds that the Lean tool accepts and refuses: the tool's
       verdict on the block inside a valid packet must equal
       Paho's verdict on the block alone.
    The classes where Paho departs from the standard are checked
    apart: each must show the documented difference, and they are
    not counted as comparisons."""
    from paho.mqtt.properties import Properties, VariableByteIntegers
    from paho.mqtt.packettypes import PacketTypes
    tool = Tool()
    entries = []

    def paho_accepts(setname, block):
        props = Properties(getattr(PacketTypes, PAHO_PACKET[setname]))
        try:
            _, used = props.unpack(block)
        except Exception:
            return False
        return used == len(block)

    # 1. Paho's writing of each value as a Subscription Identifier.
    values = [v for v, _ in VBI_TABLE if v != 0]
    values += [rng.randrange(1, 1 << 28) for _ in range(120)]
    for v in values:
        enc = bytes(VariableByteIntegers.encode(v))
        block = bytes([11]) + enc
        body = be16(1) + enc_vbi(len(block)) + block + enc_str("a") + b"\x00"
        bs = raw_packet(0x82, body)
        entries.append(("paho vbi", tool.ask(req(bs)), want_ok(bs), bs))

    # 2. Paho judges property blocks.
    kinds = sorted(PAHO_PACKET)
    for _ in range(count_blocks):
        setname = rng.choice(kinds)
        block = raw_block(judge_entries(rng, setname))
        bs = block_packet(setname, block)
        verdict = paho_accepts(setname, block)
        entries.append((f"paho judges a {setname} block {list(block)}",
                        tool.ask(req(bs)),
                        want_ok(bs) if verdict else "none", bs))

    # The documented differences, each checked for its direction.
    diffs = [
        ("Payload Format Indicator 2 on PUBLISH", "publish",
         [(0x01, 2)], False, True,
         "section 3.3.2.3.2 names 0 and 1 but does not call another "
         "value a Protocol Error, so this reader accepts it; Paho "
         "refuses it"),
        ("Payload Format Indicator 255 in the will", "will",
         [(0x01, 255)], False, True, None),
        ("Response Topic with a wildcard on PUBLISH", "publish",
         [(0x08, "a/#")], True, False,
         "MQTT-3.3.2-14 forbids wildcards in a Response Topic and "
         "4.7.3-1 an empty one, so this reader refuses them; Paho "
         "accepts them"),
        ("empty Response Topic in the will", "will", [(0x08, "")],
         True, False, None),
        ("Authentication Data without a Method on CONNECT", "connect",
         [(0x16, b"x")], True, False,
         "section 3.1.2.11.10 makes Authentication Data without an "
         "Authentication Method a Protocol Error, so this reader "
         "refuses it; Paho accepts it"),
        ("Maximum Packet Size 4294967295 on CONNECT", "connect",
         [(0x27, 4294967295)], False, True,
         "section 3.1.2.11.4 makes the Maximum Packet Size a Four Byte "
         "Integer and calls only 0 (or a repeat) a Protocol Error, so "
         "this reader accepts values up to 2^32 - 1; Paho refuses those "
         "above 268435455"),
        ("Maximum Packet Size 268435456 on CONNECT", "connect",
         [(0x27, 268435456)], False, True, None),
        ("two Subscription Identifiers on SUBSCRIBE", "subscribe",
         [(0x0B, 1), (0x0B, 2)], True, False,
         "section 3.8.2.1.2 makes a second Subscription Identifier on "
         "SUBSCRIBE a Protocol Error, so this reader refuses it; Paho "
         "allows the repeat on any packet"),
    ]
    diff_entries = []
    for label, setname, props, paho_ok, lean_ok, why in diffs:
        block = raw_block(props)
        bs = block_packet(setname, block)
        diff_entries.append((label, tool.ask(req(bs)), paho_ok, lean_ok, bs,
                             setname, block, why))

    answers = tool.run()
    agree = accepted = refused = 0
    for label, idx, expected, bs in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, label, f"Lean {answers[idx]}, Paho's verdict {expected}")
        if answers[idx] == "none":
            refused += 1
        else:
            accepted += 1
            check(answers[idx] == want_ok(bs), label,
                  f"accepted, but reprinted as {answers[idx]}")
    for label, idx, paho_ok, lean_ok, bs, setname, block, why in diff_entries:
        got_paho = paho_accepts(setname, block)
        got_lean = answers[idx] != "none"
        check(got_paho == paho_ok and got_lean == lean_ok,
              f"paho difference/{label}",
              f"Paho {'accepts' if got_paho else 'refuses'}, Lean "
              f"{'accepts' if got_lean else 'refuses'}; documented: Paho "
              f"{'accepts' if paho_ok else 'refuses'}, Lean "
              f"{'accepts' if lean_ok else 'refuses'}")
        if why:
            paho_named.append(f"{label}, and the like: {why}. Checked on "
                              "single blocks, not counted as comparisons.")
    paho_named.append(
        "paho-mqtt's VariableByteIntegers.decode reads the longer "
        "writing 128, 0 as "
        f"{VariableByteIntegers.decode(bytes([128, 0]))!r} (value, "
        "bytes read); this reader refuses that writing, as "
        "MQTT-1.5.5-1 requires (the fixed cases check it), so the "
        "property blocks Paho judges hold only shortest writings.")
    return len(entries), agree, accepted, refused


def mutation_cases(rng):
    tool = Tool()
    entries = []

    def settle(label, bs):
        idx = tool.ask(req(bs))
        entries.append((label, idx, settled_answer(bs), bs))

    def expect(label, bs, expected):
        idx = tool.ask(req(bs))
        entries.append((label, idx, expected, bs))
        check(settled_answer(bs) == expected, f"mutation/{label}",
              "oracle disagrees with the named expectation")

    rich_connect = enc_packet(
        ("connect", True, 60, [(0x11, 3600), (0x26, ("k", "v"))],
         "client-1",
         (1, True, [(0x18, 30)], "last/will", b"\x01\x02"),
         "user", b"secret"))
    rich_publish = enc_packet(
        ("publish", False, 1, False, "sensors/temp", 4242,
         [(0x02, 600), (0x26, ("a", "b"))], b"hello world"))
    for name, base in (("connect", rich_connect),
                       ("publish", rich_publish)):
        for cut in range(len(base)):
            settle(f"{name} truncate {cut}", base[:cut])
        for off in range(len(base)):
            mut = bytearray(base)
            mut[off] = (mut[off] + 37) % 256
            settle(f"{name} flip at {off}", bytes(mut))

    def props_packet(setname_header, body_props, tail):
        return raw_packet(setname_header, body_props + tail)

    named = []
    # Five byte remaining length: a continuation mark on the
    # fourth byte.
    named.append(("five byte remaining length",
                  bytes([192, 255, 255, 255, 255, 127]), "none"))
    # The value of these five byte writings fits the input, so a
    # reader with a cap above four bytes would accept them: they
    # separate the four byte cap from a plain shortage of input.
    named.append(("five byte remaining length whose value fits",
                  bytes([192, 128, 128, 128, 128, 0]), "none"))
    named.append(("five byte subscription identifier",
                  bytes([130, 13, 0, 1, 6, 11, 128, 128, 128, 128, 1,
                         0, 1, 97, 0]), "none"))
    named.append(("remaining length larger than input",
                  bytes([192, 5, 0]), "none"))
    named.append(("remaining length larger than a publish body",
                  bytes([48, 100, 0, 1, 97]), "none"))
    named.append(("truncated connect variable header",
                  bytes([16, 8, 0, 4, 77, 81, 84, 84, 5]), "none"))
    named.append(("wrong flags on connect", bytes([17, 0]), "none"))
    named.append(("wrong flags on suback",
                  bytes([146, 4, 0, 1, 0, 0]), "none"))
    named.append(("wrong flags on pingreq", bytes([193, 0]), "none"))
    sub_body = be16(1) + b"\x00" + enc_str("a") + b"\x00"
    named.append(("subscribe with flags 0000",
                  raw_packet(0x80, sub_body), "none"))
    pub_body = enc_str("a") + be16(1) + b"\x00" + b"x"
    named.append(("publish qos 3", raw_packet(0x36, pub_body), "none"))
    q0_body = enc_str("a") + b"\x00"
    named.append(("publish dup at qos 0", raw_packet(0x38, q0_body), "none"))
    named.append(("publish dup at qos 0 with retain",
                  raw_packet(0x39, q0_body), "none"))
    named.append(("publish qos 0, dup clear (control)",
                  raw_packet(0x30, q0_body),
                  want_ok(raw_packet(0x30, q0_body))))
    named.append(("publish dup at qos 1 (control)",
                  raw_packet(0x3A, pub_body),
                  want_ok(raw_packet(0x3A, pub_body))))
    wild_body = enc_str("a/#") + b"\x00" + b"x"
    named.append(("publish wildcard topic",
                  raw_packet(0x30, wild_body), "none"))
    named.append(("publish wildcard + in topic",
                  raw_packet(0x30, enc_str("a/+") + b"\x00"), "none"))
    named.append(("publish empty topic, no topic alias",
                  raw_packet(0x30, enc_str("") + b"\x00"), "none"))
    named.append(("publish empty topic, other properties only",
                  raw_packet(0x30, enc_str("") + enc_props([(0x02, 5)])),
                  "none"))
    alias_pub = raw_packet(0x30, enc_str("") + enc_props([(0x23, 1)]))
    named.append(("publish empty topic with topic alias, accepted",
                  alias_pub, want_ok(alias_pub)))
    alias_pub1 = raw_packet(0x32, enc_str("") + be16(9)
                            + enc_props([(0x26, ("k", "v")), (0x23, 7)])
                            + b"pay")
    named.append(("publish qos 1, empty topic with topic alias, accepted",
                  alias_pub1, want_ok(alias_pub1)))
    badname = (enc_str("MQTU") + bytes([5, 2]) + be16(0) + b"\x00"
               + enc_str("x"))
    named.append(("connect wrong protocol name",
                  raw_packet(0x10, badname), "none"))
    reserved = bytearray(rich_connect)
    # The connect flags byte: header(1) + length(1) + name(6)
    # + level(1) puts it at index 9.
    reserved[9] = reserved[9] | 1
    named.append(("connect reserved flag bit", bytes(reserved), "none"))
    willqos = (enc_str("MQTT") + bytes([5, 2 | 4 | 24]) + be16(0)
               + b"\x00" + enc_str("x") + b"\x00" + enc_str("w")
               + enc_bin(b""))
    named.append(("connect will qos 3", raw_packet(0x10, willqos), "none"))
    plain_tail = be16(0) + b"\x00" + enc_str("x")
    for flags, label in ((0x0A, "will qos 1 without the will flag"),
                         (0x12, "will qos 2 without the will flag"),
                         (0x22, "will retain without the will flag"),
                         (0x3A, "will qos and retain without the will flag")):
        named.append(("connect " + label,
                      raw_packet(0x10, enc_str("MQTT") + bytes([5, flags])
                                 + plain_tail), "none"))
    plain = raw_packet(0x10, enc_str("MQTT") + bytes([5, 0x02]) + plain_tail)
    named.append(("connect flags 0x02 (control)", plain, want_ok(plain)))
    wrong_prop = (enc_str("MQTT") + bytes([5, 2]) + be16(0)
                  + enc_props([(0x0B, 5)]) + enc_str("x"))
    named.append(("subscription identifier on connect",
                  raw_packet(0x10, wrong_prop), "none"))
    table_only = raw_packet(0xE0, bytes([0]) + enc_props([(0x12, "x")]))
    named.append(("assigned client identifier on disconnect",
                  table_only, "none"))
    unknown_prop = raw_packet(
        0x30, enc_str("a") + b"\x04\x7f\x01\x00\x00" + b"")
    named.append(("unknown property identifier", unknown_prop, "none"))
    repeated = raw_packet(
        0x32, enc_str("a") + be16(3) + enc_props([(0x23, 1), (0x23, 2)]))
    named.append(("repeated single use property", repeated, "none"))
    overrun = raw_packet(0x30, enc_str("a") + b"\x0a\x01\x01")
    named.append(("property block length overruns", overrun, "none"))
    named.append(("packet identifier 0 in subscribe",
                  raw_packet(0x82, be16(0) + b"\x00" + enc_str("a")
                             + b"\x00"), "none"))
    named.append(("packet identifier 0 in publish qos1",
                  raw_packet(0x32, enc_str("a") + be16(0) + b"\x00"),
                  "none"))
    named.append(("empty topic filter list",
                  raw_packet(0x82, be16(1) + b"\x00"), "none"))
    named.append(("empty reason list in suback",
                  raw_packet(0x90, be16(1) + b"\x00"), "none"))
    named.append(("disconnect body of length 1, accepted",
                  bytes([224, 1, 0]), want_ok(bytes([224, 1, 0]))))
    named.append(("pingreq with a body", bytes([192, 1, 0]), "none"))
    named.append(("packet type 2, outside this slice",
                  bytes([32, 0]), "none"))
    named.append(("packet type 0", bytes([0, 0]), "none"))
    named.append(("trailing byte after one packet",
                  bytes([192, 0, 0]), "none"))
    named.append(("empty input", b"", "none"))
    nul_topic = raw_packet(0x30, be16(2) + b"a\x00" + b"\x00")
    named.append(("null character in publish topic", nul_topic, "none"))
    bad_utf8 = raw_packet(0x30, be16(1) + b"\xff" + b"\x00")
    named.append(("ill formed utf-8 in publish topic", bad_utf8, "none"))
    overlong = raw_packet(0x30, be16(2) + b"\xc0\x80" + b"\x00")
    named.append(("overlong utf-8 in publish topic", overlong, "none"))
    # Property values the standard calls a Protocol Error, each
    # beside a control that differs in the value alone.
    connect_head = enc_str("MQTT") + bytes([5, 2]) + be16(0)
    for label, setname, props, ok_props in (
            ("subscription identifier 0 on subscribe", "subscribe",
             [(0x0B, 0)], [(0x0B, 1)]),
            ("subscription identifier 0 on publish", "publish",
             [(0x0B, 0)], [(0x0B, 5)]),
            ("topic alias 0", "publish", [(0x23, 0)], [(0x23, 1)]),
            ("response topic with #", "publish", [(0x08, "a/#")],
             [(0x08, "a/b")]),
            ("response topic with +", "publish", [(0x08, "+")],
             [(0x08, "x")]),
            ("empty response topic", "publish", [(0x08, "")],
             [(0x08, "r")]),
            ("receive maximum 0", "connect", [(0x21, 0)], [(0x21, 1)]),
            ("maximum packet size 0", "connect", [(0x27, 0)],
             [(0x27, 1)]),
            ("request problem information 2", "connect", [(0x17, 2)],
             [(0x17, 1)]),
            ("request response information 2", "connect",
             [(0x19, 2)], [(0x19, 0)]),
            ("authentication data without method", "connect",
             [(0x16, b"x")], [(0x15, "m"), (0x16, b"x")]),
            ("response topic with # in will properties", "will",
             [(0x08, "#")], [(0x08, "w")])):
        for props_here, want in ((props, "none"), (ok_props, None)):
            if setname == "subscribe":
                bs = raw_packet(0x82, be16(1) + enc_props(props_here)
                                + enc_str("a") + b"\x00")
            elif setname == "publish":
                bs = raw_packet(0x30, enc_str("a") + enc_props(props_here)
                                + b"x")
            elif setname == "connect":
                bs = raw_packet(0x10, connect_head + enc_props(props_here)
                                + enc_str("x"))
            else:
                bs = raw_packet(0x10, enc_str("MQTT") + bytes([5, 6])
                                + be16(0) + b"\x00" + enc_str("x")
                                + enc_props(props_here) + enc_str("w")
                                + enc_bin(b""))
            named.append((label if want else label + " (control)", bs,
                          want if want else want_ok(bs)))
    # Topic filter rules (sections 4.7.1, 4.7.3, 4.8.2, 3.8.3.1).
    for flt, opts, good in (
            ("a/#/b", 0, False), ("a#", 0, False), ("a+", 0, False),
            ("+a", 0, False), ("a/b+", 0, False), ("#/a", 0, False),
            ("", 0, False), ("a/##", 0, False),
            ("$share/g/t", 4, False), ("$share/g", 0, False),
            ("$share//t", 0, False), ("$share/g/", 0, False),
            ("$share/+/t", 0, False), ("$share/g#/t", 0, False),
            ("$share/g/a/#/b", 0, False),
            ("a/+/#", 0, True), ("#", 0, True), ("+", 0, True),
            ("/", 0, True), ("+/+", 0, True), ("a//b", 0, True),
            ("$share/g/t", 0, True), ("$share/g/#", 1, True),
            ("$share/g/a/b", 0, True), ("$share", 4, True),
            ("$sharex/a", 4, True), ("$SYS/#", 0, True)):
        bs = raw_packet(0x82, be16(1) + b"\x00" + enc_str(flt)
                        + bytes([opts]))
        label = f"topic filter {flt!r} options {opts}"
        named.append((label + (" (accepted)" if good else ""), bs,
                      want_ok(bs) if good else "none"))
    for opts_byte, label in ((64, "options byte reserved bits set"),
                             (3, "options byte qos 3"),
                             (48, "options byte retain handling 3")):
        named.append((label,
                      raw_packet(0x82, be16(1) + b"\x00" + enc_str("a")
                                 + bytes([opts_byte])), "none"))
    for label, bs, expected in named:
        expect(label, bs, expected)
    answers = tool.run()
    agree = 0
    for label, idx, expected, bs in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, f"mutation/{label}",
                  f"got {answers[idx]}, want {expected}")
        # Every input the tool accepts reprints byte for byte.
        check(answers[idx] in ("none", want_ok(bs)), f"mutation/{label}",
              f"accepted, but reprinted as {answers[idx]}")
    return len(entries), agree


# ---------------------------------------------------------------------------
# Forbidden classes, drawn from the seed.
# ---------------------------------------------------------------------------

def put_prop(ps, pid, value):
    """The property list with every (pid, _) removed and (pid,
    value) put at a random place: the value under test is the
    only one of its identifier in the block."""
    out = [(i, v) for i, v in ps if i != pid]
    return out + [(pid, value)]


def packet_with_block(rng, setname, props):
    """A random valid packet of the kind that carries a `setname`
    property block, with `props` as that block."""
    if setname in ("connect", "will"):
        will = (rng.randint(0, 2), rng.random() < 0.5,
                rand_props(rng, "will"), rand_topic(rng), rand_bytes(rng))
        cprops = rand_props(rng, "connect")
        if setname == "connect":
            cprops = props
            if rng.random() < 0.5:
                will = None
        else:
            will = (will[0], will[1], props, will[3], will[4])
        return ("connect", rng.random() < 0.5, rng.randrange(65536), cprops,
                rand_text(rng, 0, 6), will,
                rand_text(rng, 1, 5) if rng.random() < 0.4 else None,
                rand_bytes(rng, 6) if rng.random() < 0.4 else None)
    if setname == "publish":
        qos = rng.choice([0, 1, 2])
        return ("publish", qos != 0 and rng.random() < 0.5, qos,
                rng.random() < 0.5, rand_topic(rng),
                rng.randint(1, 65535) if qos else None, props,
                rand_bytes(rng, 10))
    if setname == "subscribe":
        return ("subscribe", rng.randint(1, 65535), props,
                [(rand_filter(rng), (rng.randint(0, 2), False,
                                     rng.random() < 0.5, rng.randint(0, 2)))
                 for _ in range(rng.randint(1, 3))])
    raise ValueError(setname)


def wild_topic(rng):
    """A topic name with `+` or `#` put in at a random place."""
    t = rand_topic(rng)
    k = rng.randint(0, len(t))
    return t[:k] + rng.choice("+#") + t[k:]


def safe_level(rng):
    return "".join(rng.choice("abcXYZ019._-") for _ in range(rng.randint(1, 4)))


def good_plain_filter(rng):
    n = rng.randint(1, 6)
    parts = [rng.choice(["+", safe_level(rng)]) for _ in range(n)]
    if rng.random() < 0.4:
        parts[-1] = "#"
    return "/".join(parts)


def bad_plain_filter(rng):
    """A filter of 1 to 6 levels that breaks a wildcard rule:
    `#` as a whole level other than the last, or `+` or `#`
    inside a level beside other characters."""
    kind = rng.choice(["hash_not_last", "plus_in_level", "hash_in_level"])
    if kind == "hash_not_last":
        n = rng.randint(2, 6)
        parts = [rng.choice(["+", safe_level(rng)]) for _ in range(n)]
        parts[rng.randint(0, n - 2)] = "#"
        return kind, "/".join(parts)
    n = rng.randint(1, 6)
    parts = [rng.choice(["+", safe_level(rng)]) for _ in range(n)]
    lvl = safe_level(rng)
    k = rng.randint(0, len(lvl))
    ch = "+" if kind == "plus_in_level" else "#"
    parts[rng.randrange(n)] = lvl[:k] + ch + lvl[k:]
    return kind, "/".join(parts)


def bad_filter(rng):
    """A filter that breaks a rule of sections 4.7.1, 4.7.3 or
    4.8.2, with the No Local option to send it with."""
    kind = rng.choice(["plain", "plain", "plain", "share_name_empty",
                       "share_name_wild", "share_no_slash",
                       "share_empty_filter", "share_bad_filter",
                       "share_no_local", "empty"])
    name = safe_level(rng)
    if kind == "plain":
        return bad_plain_filter(rng) + (rng.random() < 0.5,)
    if kind == "share_name_empty":
        return kind, "$share//" + good_plain_filter(rng), False
    if kind == "share_name_wild":
        k = rng.randint(0, len(name))
        return kind, ("$share/" + name[:k] + rng.choice("+#") + name[k:]
                      + "/" + good_plain_filter(rng)), False
    if kind == "share_no_slash":
        return kind, "$share/" + name, False
    if kind == "share_empty_filter":
        return kind, "$share/" + name + "/", False
    if kind == "share_bad_filter":
        return kind, "$share/" + name + "/" + bad_plain_filter(rng)[1], False
    if kind == "share_no_local":
        return kind, "$share/" + name + "/" + good_plain_filter(rng), True
    return kind, "", False


def forbidden_cases(rng):
    """Inputs of each forbidden class, drawn from the seed: every
    Request Problem Information and Request Response Information
    value from 2 to 255, the value 0 for the Subscription
    Identifier, Receive Maximum, Topic Alias and Maximum Packet
    Size, Response Topics that hold a wildcard or are empty,
    Authentication Data without a Method, and topic filters of 1
    to 6 levels that break a wildcard or shared subscription
    rule. Each is a random valid packet with one rule broken.
    The oracle settles each answer, and the run checks that the
    oracle (prop_value_ok, filter_ok) does call each one
    forbidden; about one in five comes with a control, the same
    packet with the rule kept, which must be accepted."""
    tool = Tool()
    entries = []

    def add(label, bs, forbidden):
        want = settled_answer(bs)
        if forbidden:
            check(want == "none", f"forbidden/{label}",
                  f"the oracle accepts {list(bs)}, which the generator "
                  "meant to break a rule")
        else:
            check(want != "none", f"forbidden/{label}",
                  f"the oracle refuses the control {list(bs)}")
        idx = tool.ask(req(bs))
        entries.append((label, idx, want, bs))

    def value_case(label, setname, pid, bad, good):
        base = rand_props(rng, setname)
        if pid == 0x16:
            base = [(i, v) for i, v in base if i not in (0x15, 0x16)]
        seed_state = rng.getstate()
        pkt = packet_with_block(rng, setname, put_prop(base, pid, bad))
        add(label, enc_packet(pkt), True)
        if rng.random() < 0.2:
            # The same draws again, so the control differs from the
            # case in the value under test alone (for Authentication
            # Data, in an added Authentication Method).
            rng2 = random.Random()
            rng2.setstate(seed_state)
            good_props = (put_prop(base, pid, bad) + [(0x15, "m")]
                          if pid == 0x16 else put_prop(base, pid, good))
            ok = packet_with_block(rng2, setname, good_props)
            add(label + " (control)", enc_packet(ok), False)

    for pid, name in ((0x17, "request problem information"),
                      (0x19, "request response information")):
        for v in range(2, 256):
            value_case(f"{name} {v}", "connect", pid, v, rng.randint(0, 1))
    for setname, pid, name, good in (
            ("subscribe", 0x0B, "subscription identifier 0 on subscribe",
             lambda: rng.randint(1, 268435455)),
            ("publish", 0x0B, "subscription identifier 0 on publish",
             lambda: rng.randint(1, 268435455)),
            ("connect", 0x21, "receive maximum 0", lambda: rng.randint(1, 65535)),
            ("connect", 0x27, "maximum packet size 0",
             lambda: rng.randint(1, (1 << 32) - 1)),
            ("publish", 0x23, "topic alias 0", lambda: rng.randint(1, 65535))):
        for _ in range(30):
            value_case(name, setname, pid, 0, good())
    for setname in ("publish", "will"):
        for _ in range(50):
            value_case(f"response topic with a wildcard in {setname}",
                       setname, 0x08, wild_topic(rng), rand_topic(rng))
        for _ in range(10):
            value_case(f"empty response topic in {setname}", setname, 0x08,
                       "", rand_topic(rng))
    for _ in range(30):
        value_case("authentication data without a method", "connect", 0x16,
                   rand_bytes(rng, 6), None)

    for _ in range(400):
        kind, flt, no_local = bad_filter(rng)
        check(not filter_ok(flt, no_local), f"forbidden/filter {flt!r}",
              "the generator made a filter the oracle's filter_ok keeps")
        others = [(rand_filter(rng), (rng.randint(0, 2), False,
                                      rng.random() < 0.5, rng.randint(0, 2)))
                  for _ in range(rng.randint(0, 2))]
        k = rng.randint(0, len(others))
        opts = (rng.randint(0, 2), no_local, rng.random() < 0.5,
                rng.randint(0, 2))
        fs = others[:k] + [(flt, opts)] + others[k:]
        pid = rng.randint(1, 65535)
        props = rand_props(rng, "subscribe")
        add(f"topic filter {kind} {flt!r}",
            enc_packet(("subscribe", pid, props, fs)), True)
        if rng.random() < 0.25:
            good = good_plain_filter(rng)
            if kind.startswith("share"):
                good = "$share/" + safe_level(rng) + "/" + good
            fs2 = others[:k] + [(good, (opts[0], False, opts[2], opts[3]))] \
                + others[k:]
            add(f"topic filter control {good!r}",
                enc_packet(("subscribe", pid, props, fs2)), False)

    answers = tool.run()
    agree = 0
    for label, idx, expected, bs in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, f"forbidden/{label}",
                  f"input {list(bs)}: got {answers[idx]}, want {expected}")
        check(answers[idx] in ("none", want_ok(bs)), f"forbidden/{label}",
              f"accepted, but reprinted as {answers[idx]}")
    return len(entries), agree


def protocol_cases():
    lines = ["parse 192,0", "parse", "parse 01", "parse 256",
             "parse 192,0,0", "bogus 1", "parse 1 2", "Parse 192,0",
             "parse 0", ""]
    expected = ["ok:192,0", "none", "error", "error", "none",
                "error", "error", "error", "none"]
    proc = subprocess.run([EXE], input="\n".join(lines) + "\n",
                          capture_output=True, text=True, timeout=120)
    got = proc.stdout.splitlines()
    check(got == expected, "protocol", f"got {got}, want {expected}")
    return len(expected)


# ---------------------------------------------------------------------------

def main():
    if "--skip-build" not in sys.argv:
        subprocess.run(["lake", "build"], cwd=ROOT, check=True,
                       capture_output=True, text=True, timeout=1200)
    rng = random.Random(SEED)
    # The sections that run on every machine; their inputs make the
    # recorded input count. The Paho cross-check needs the paho-mqtt
    # library, so it is listed apart and left out of that count, and
    # a run without the library records the same count.
    sections = []
    extra = []

    n_fixed = fixed_cases()
    sections.append(("Fixed cases (spec VBI table, one packet per type, "
                     "richer hand built packets)", n_fixed, n_fixed))

    n_or, a_or = oracle_differential(rng, 3000)
    sections.append(("Oracle differential, random packets of all seven "
                     "types (seed 20261026)", n_or, a_or))

    try:
        import paho.mqtt
        import importlib.metadata as md
        try:
            paho_version = md.version("paho-mqtt")
        except Exception:
            paho_version = "unknown"
        paho_present = True
    except ImportError:
        paho_present = False
        paho_version = None
    # The Paho section draws from its own generator, so whether it
    # runs does not change the inputs of the sections after it.
    if paho_present:
        n_pa, a_pa, acc_pa, ref_pa = paho_section(random.Random(SEED + 1), 600)
        extra.append((f"Paho {paho_version} cross-check, each a Lean answer "
                      "judged by Paho: its variable byte integer writings "
                      "as Subscription Identifiers, and property blocks of "
                      "all six kinds judged by Properties.unpack (Lean "
                      f"accepted {acc_pa}, refused {ref_pa}; not counted in "
                      "Inputs)", n_pa, a_pa))
    named = paho_named

    n_mut, a_mut = mutation_cases(rng)
    sections.append(("Mutations and named rejections, settled by the "
                     "oracle", n_mut, a_mut))
    # Its own generator, so the sections before it keep their inputs.
    n_fb, a_fb = forbidden_cases(random.Random(SEED + 2))
    sections.append(("Forbidden classes drawn from the seed (property "
                     "values, Response Topics, Authentication Data, topic "
                     "filters of 1 to 6 levels), with controls, settled by "
                     "the oracle", n_fb, a_fb))
    n_proto = protocol_cases()
    sections.append(("Line protocol cases", n_proto, n_proto))

    mosquitto = shutil.which("mosquitto") or shutil.which("mosquitto_sub")
    failed = len(failures)
    total = sum(t for _, t, _ in sections)
    oracle = ("the strict reference decoder and encoder in "
              "tests/run_tests.py, written from the OASIS MQTT Version "
              "5.0 standard (OASIS Standard, 7 March 2019) and SPEC.md, "
              f"run on Python {sys.version.split()[0]}")
    if paho_present:
        oracle += (f"; with a cross-check against paho-mqtt "
                   f"{paho_version}, counted apart")
    lines = []
    lines.append("# Test results: mqtt")
    lines.append("")
    lines.append(f"- Oracle: {oracle}")
    lines.append(f"- Seed: {SEED}")
    lines.append(f"- Inputs: {total}")
    lines.append(f"- Failures: {failed}")
    lines.append("")
    lines.append("Tool: the Lean command line program, one process per "
                 "section, requests batched. The harness checks parsed "
                 "structure through the re-encoding the tool prints, "
                 "together with its own oracle, and checks that every "
                 "input the tool accepts among the mutations and named "
                 "cases reprints byte for byte. Inputs counts the "
                 "sections that run on every machine.")
    lines.append("")
    if paho_present:
        lines.append(f"Paho's Python library (`paho-mqtt`, version "
                     f"{paho_version}) was importable in the interpreter "
                     "that ran this harness; the Paho cross-check ran. "
                     "Each of its inputs compares an answer of the Lean "
                     "tool with Paho's: Paho's encoder output for "
                     "variable byte integers must come back unchanged, "
                     "and Paho's Properties.unpack judges property "
                     "blocks of all six kinds, accepted and refused, the "
                     "pieces the library exposes without a broker. It "
                     "does not judge whole packets. Its inputs are "
                     "listed below and are not part of Inputs.")
    else:
        lines.append("Paho's Python library (`paho-mqtt`) was NOT "
                     "importable in the interpreter that ran this "
                     "harness; the Paho cross-check did not run, and "
                     "the strict oracle carried accept and reject "
                     "alone.")
    lines.append("")
    lines.append("The plan's third oracle, MQTT 5.0 specification test "
                 "material, was NOT used: the standard ships no "
                 "conformance test suite, and the nearest material, the "
                 "MQTTV5 codec in Eclipse paho.mqtt.testing, is not "
                 "wired into this harness.")
    lines.append("")
    if mosquitto:
        lines.append(f"A Mosquitto binary was found at {mosquitto}; "
                     "no Mosquitto test cases are wired into this "
                     "harness.")
    else:
        lines.append("Mosquitto was NOT present on this machine (no "
                     "`mosquitto` or `mosquitto_sub` binary), so no "
                     "Mosquitto tests ran.")
    lines.append("")
    lines.append("| Section | Inputs | Agreements |")
    lines.append("| --- | --- | --- |")
    for name, n, agree in sections + extra:
        lines.append(f"| {name} | {n} | {agree} |")
    lines.append("")
    if named:
        lines.append("Named differences from the oracles:")
        for d in named:
            lines.append(f"- {d}")
    else:
        lines.append("Named differences from the oracles: none.")
    lines.append("")
    if failed:
        lines.append("Failures, the first 40:")
        for f in failures[:40]:
            lines.append(f"- {f}")
        lines.append("")
    with open(os.path.join(HERE, "TEST-RESULTS.md"), "w") as fh:
        fh.write("\n".join(lines))
    agree = sum(a for _, _, a in sections)
    print(f"sections={len(sections)} inputs={total} agreements={agree} "
          f"failures={failed} paho={'yes ' + str(paho_version) if paho_present else 'no'} "
          f"mosquitto={'yes' if mosquitto else 'no'}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
