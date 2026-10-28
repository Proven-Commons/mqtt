#!/usr/bin/env python3
"""Test harness for the Lean MQTT 5.0 packet codec.

Layers, all settled against independent expectations:

1. Fixed cases: the variable byte integer table from section
   2.1.4 of the standard, hand built packets for each of the
   seven packet types in this slice, and the DISCONNECT one
   byte body form, which is legal and reprints in the longer
   canonical form.

2. A differential against a strict oracle written here from
   the standard and from SPEC.md (including the pinned
   reading that the DISCONNECT body of length 1 is a reason
   code with an empty property block): random packets of all
   seven types with varied properties are encoded by the
   oracle, read by the Lean tool, and the answer must be the
   canonical reprint.

3. A cross-check against Paho's Python library when it is
   importable: variable byte integers written by its encoder
   are fed to the Lean tool as Subscription Identifiers, and
   property blocks it packs for PUBLISH are read by the
   oracle, wrapped in packets, and fed to the Lean tool. Its
   decoder accepts writings longer than the value needs, which
   MQTT-1.5.5-1 forbids; the run records that as a named
   difference. When the library is absent, the run says so and
   the oracle carries accept and reject alone. The Mosquitto
   test suite is a separate program, not a Python library; the
   run checks for its binary and the results file states
   whether it was present.

Mutations of rich packets (truncation at every length, byte
flips at every position) and a list of named rejection cases
are settled by comparing the Lean answer with the oracle's
answer on the same bytes.

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
#   ("disconnect", None) or ("disconnect", (reason, props))
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
        ps.append((pid, v))
    if j != len(seg):
        raise Reject()
    return ps, end


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
    check_topic(topic)
    qos = (flags // 2) % 4
    pid = None
    if qos != 0:
        pid, i = dec_uint(seg, i, 2)
        if pid == 0:
            raise Reject()
    props, i = dec_props("publish", seg, i)
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
        return ("disconnect", (seg[0], []))
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
    parts = []
    for _ in range(rng.randint(1, 3)):
        parts.append(rng.choice(["+", "#", rand_text(rng, 1, 4,
                                                     topic_safe=True)]))
    return "/".join(parts)


def rand_bytes(rng, hi=12):
    return bytes(rng.randrange(256) for _ in range(rng.randint(0, hi)))


def rand_prop_value(rng, t):
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
    ps = []
    for pid in ids:
        ps.append((pid, rand_prop_value(rng, PROP_TYPE[pid])))
        if repeatable(setname, pid) and rng.random() < 0.4:
            ps.append((pid, rand_prop_value(rng, PROP_TYPE[pid])))
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
        return ("publish", rng.random() < 0.5, qos, rng.random() < 0.5,
                rand_topic(rng),
                rng.randint(1, 65535) if qos else None,
                rand_props(rng, "publish"), rand_bytes(rng, 20))
    if tag == "subscribe":
        filters = [(rand_filter(rng),
                    (rng.randint(0, 2), rng.random() < 0.5,
                     rng.random() < 0.5, rng.randint(0, 2)))
                   for _ in range(rng.randint(1, 3))]
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
    return ("disconnect",
            (rng.choice([0, 4, 129, 135, 142, rng.randrange(256)]),
             rand_props(rng, "disconnect")))


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
    add("disconnect reason only, canonical reprint",
        bytes([224, 1, 0]), want_ok(bytes([224, 2, 0, 0])))
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


def paho_section(rng, count_props):
    """Cross-checks against Paho: variable byte integers, and
    PUBLISH property blocks packed by the library. Returns
    (inputs, agreements)."""
    from paho.mqtt.properties import Properties, VariableByteIntegers
    from paho.mqtt.packettypes import PacketTypes
    tool = Tool()
    entries = []
    total = 0
    agree = 0

    # Paho's writing of each value, as the Subscription Identifier
    # of a SUBSCRIBE: the Lean tool must accept the packet and
    # print the same bytes back. Value 0 is left out: it is not a
    # valid Subscription Identifier.
    values = [v for v, _ in VBI_TABLE if v != 0]
    values += [rng.randrange(1, 1 << 28) for _ in range(120)]
    for v in values:
        enc = bytes(VariableByteIntegers.encode(v))
        block = bytes([11]) + enc
        body = be16(1) + enc_vbi(len(block)) + block + enc_str("a") + b"\x00"
        bs = raw_packet(0x82, body)
        idx = tool.ask(req(bs))
        entries.append((idx, want_ok(bs)))
        total += 1
    # Paho's decoder on the longer writing 128, 0 of the value 0.
    # The standard forbids that writing [MQTT-1.5.5-1]; the Lean
    # tool must refuse it as a remaining length, and Paho's
    # answer is recorded, not taken.
    paho_named.append(
        "paho-mqtt's VariableByteIntegers.decode reads the longer "
        "writing 128, 0 as "
        f"{VariableByteIntegers.decode(bytes([128, 0]))!r} (value, "
        "bytes read); this reader refuses that writing, as "
        "MQTT-1.5.5-1 requires, so the run does not take Paho's "
        "answer there.")
    idx = tool.ask(req(bytes([192, 128, 0])))
    entries.append((idx, "none"))
    total += 1

    attr = {0x01: "PayloadFormatIndicator", 0x02: "MessageExpiryInterval",
            0x03: "ContentType", 0x08: "ResponseTopic",
            0x09: "CorrelationData", 0x0B: "SubscriptionIdentifier",
            0x23: "TopicAlias", 0x26: "UserProperty"}
    for _ in range(count_props):
        props = Properties(PacketTypes.PUBLISH)
        chosen = []
        if rng.random() < 0.7:
            props.PayloadFormatIndicator = rng.randint(0, 1)
        if rng.random() < 0.5:
            props.MessageExpiryInterval = rng.randrange(1 << 32)
        if rng.random() < 0.5:
            props.ContentType = rand_text(rng, 1, 6, topic_safe=True)
        if rng.random() < 0.4:
            props.ResponseTopic = rand_topic(rng)
        if rng.random() < 0.4:
            props.CorrelationData = rand_bytes(rng, 6)
        if rng.random() < 0.5:
            props.SubscriptionIdentifier = [rng.randint(1, 1000)
                                            for _ in range(rng.randint(1, 2))]
        if rng.random() < 0.5:
            props.TopicAlias = rng.randint(1, 65535)
        if rng.random() < 0.5:
            props.UserProperty = [(rand_text(rng, 1, 4, topic_safe=True),
                                   rand_text(rng, 0, 4, topic_safe=True))]
        packed = bytes(props.pack())
        try:
            parsed, j = dec_props("publish", packed, 0)
            okshape = j == len(packed)
        except Reject:
            okshape = False
        if not okshape or enc_props(parsed) != packed:
            check(False, "paho properties",
                  f"oracle cannot read paho block {list(packed)}")
            continue
        pkt = ("publish", False, 1, False, "paho/topic", 7, parsed,
               b"\x10\x20")
        bs = enc_packet(pkt)
        idx = tool.ask(req(bs))
        entries.append((idx, want_ok(bs)))
        total += 1
    answers = tool.run()
    for idx, expected in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, "paho packet",
                  f"got {answers[idx]}, want {expected}")
    return total, agree


def mutation_cases(rng):
    tool = Tool()
    entries = []

    def settle(label, bs):
        idx = tool.ask(req(bs))
        entries.append((label, idx, settled_answer(bs)))

    def expect(label, bs, expected):
        idx = tool.ask(req(bs))
        entries.append((label, idx, expected))
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
    wild_body = enc_str("a/#") + b"\x00" + b"x"
    named.append(("publish wildcard topic",
                  raw_packet(0x30, wild_body), "none"))
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
                  bytes([224, 1, 0]), want_ok(bytes([224, 2, 0, 0]))))
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
    for label, idx, expected in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, f"mutation/{label}",
                  f"got {answers[idx]}, want {expected}")
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
    sections = []

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
    named = paho_named
    if paho_present:
        n_pa, a_pa = paho_section(rng, 250)
        sections.append((f"Paho {paho_version} cross-check (variable byte "
                         "integers as Subscription Identifiers, and "
                         "PUBLISH property blocks)", n_pa, a_pa))

    n_mut, a_mut = mutation_cases(rng)
    sections.append(("Mutations and named rejections, settled by the "
                     "oracle", n_mut, a_mut))
    n_proto = protocol_cases()
    sections.append(("Line protocol cases", n_proto, n_proto))

    mosquitto = shutil.which("mosquitto") or shutil.which("mosquitto_sub")
    failed = len(failures)
    lines = []
    lines.append("# Test results: mqtt")
    lines.append("")
    lines.append(f"Seed: {SEED}. Tool: the Lean command line program, "
                 "one process per section, requests batched. The harness "
                 "checks parsed structure through the re-encoding the "
                 "tool prints, together with its own oracle.")
    lines.append("")
    if paho_present:
        lines.append(f"Paho's Python library (`paho-mqtt`, version "
                     f"{paho_version}) was importable in the interpreter "
                     "that ran this harness; the Paho cross-check ran. "
                     "It covers variable byte integers and PUBLISH "
                     "property blocks, the pieces the library exposes "
                     "without a broker.")
    else:
        lines.append("Paho's Python library (`paho-mqtt`) was NOT "
                     "importable in the interpreter that ran this "
                     "harness; the Paho cross-check did not run, and "
                     "the strict oracle carried accept and reject "
                     "alone.")
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
    for name, total, agree in sections:
        lines.append(f"| {name} | {total} | {agree} |")
    lines.append("")
    if named:
        lines.append("Named differences from the oracles:")
        for d in named:
            lines.append(f"- {d}")
    else:
        lines.append("Named differences from the oracles: none.")
    lines.append("")
    if failed:
        lines.append(f"Failures: {failed}.")
        for f in failures[:40]:
            lines.append(f"- {f}")
    else:
        lines.append("Failures: none.")
    lines.append("")
    with open(os.path.join(HERE, "TEST-RESULTS.md"), "w") as fh:
        fh.write("\n".join(lines))
    total = sum(t for _, t, _ in sections)
    agree = sum(a for _, _, a in sections)
    print(f"sections={len(sections)} inputs={total} agreements={agree} "
          f"failures={failed} paho={'yes ' + str(paho_version) if paho_present else 'no'} "
          f"mosquitto={'yes' if mosquitto else 'no'}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
