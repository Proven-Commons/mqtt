#!/usr/bin/env python3
"""Planted bugs: does a wrong reader get caught?

Each plant below is a small change to the reader or to its rules
in Mqtt/, the kind of bug the statements and the tests are meant
to catch. For each one, in a scratch copy of the repo, the script:

1. builds the command line tool (`lake build mqtt`), which does
   not need the proofs, and runs the test harness against it
   (`tests/run_tests.py --skip-build`). The plant is caught by the
   tests when the harness reports a failure.
2. builds everything (`lake build`), the proofs included. The
   plant is caught by the proofs when that build fails: the proofs
   of the approved statements in Spec.lean no longer go through.
   For a planted bug that makes a statement false, no proof can
   go through. The script reports the first error.

A run with no plant comes first, as the control: it must build and
pass. The outcome is written to tests/PLANTED-BUGS.md.

Among the plants are the ones review 1 (finding 10) and the
independent check asked for: a reader with a five byte cap, a
reader that accepts longer writings of a variable byte integer, a
reader that pads a short input with zeros, and a partial weakening
of the filter and value rules (`#` before the last level when three
or more levels follow, and Request Problem Information 3).

Usage: python3 tests/plant_bugs.py [--keep] [names...]
--keep leaves the scratch copies in place. Names pick plants.
"""

import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# (name, the approved statement the plant makes false, what it
#  does, file, text to replace, replacement). The failing test
#  input is the witness: the planted reader accepts it, and the
#  statement says no reader that meets it does.
PLANTS = [
    ("cap5", "Spec.decVBI_four_byte_cap",
     "variable byte integers may take five bytes",
     "Mqtt/Parse.lean", "  decVBIGo 4 bs", "  decVBIGo 5 bs"),
    ("longer_writings", "Spec.decVBI_length",
     "a variable byte integer written in more bytes than needed is "
     "accepted (128, 0 for 0)",
     "Mqtt/Parse.lean",
     "| some (v, r) => if v = 0 then none else some",
     "| some (v, r) => if v = 0 ∧ False then none else some"),
    ("zero_padding", "Spec.parse_sound",
     "a field cut short by the end of the input is padded with zero "
     "bytes",
     "Mqtt/Parse.lean",
     "  if bs.length ≥ n then some (bs.take n, bs.drop n) else none",
     "  some ((bs ++ List.replicate n 0).take n, bs.drop n)"),
    ("subscribe_flags", "Spec.header_rule",
     "a SUBSCRIBE with flags 0000 is accepted as well as 0010",
     "Mqtt/Parse.lean",
     "  | 8 => if flags = 2 then readSubscribeBody seg else none",
     "  | 8 => if flags = 2 ∨ flags = 0 then readSubscribeBody seg else none"),
    ("dup_qos0", "Spec.header_rule",
     "a PUBLISH with DUP set at QoS 0 is accepted",
     "Mqtt/Parse.lean",
     "else if (flags / 2) % 4 = 0 ∧ flagBit flags 3 = true then none",
     "else if False then none"),
    ("will_bits", "Spec.connect_rule",
     "will QoS and will retain bits are accepted with the will flag "
     "clear",
     "Mqtt/Parse.lean",
     "if flagBit flags 2 || (flags / 8) % 8 = 0 then", "if true then"),
    ("empty_topic", "Spec.publish_rule",
     "an empty PUBLISH topic is accepted without a Topic Alias",
     "Mqtt/Parse.lean",
     "  if topic.isEmpty && !hasTopicAlias props then none",
     "  if false then none"),
    ("disconnect_form", "Spec.disconnect_short_form",
     "the one byte DISCONNECT body is read as the long form",
     "Mqtt/Parse.lean",
     "if r1.isEmpty then some (.disconnect (some (rc.toNat, none)))",
     "if r1.isEmpty then some (.disconnect (some (rc.toNat, some [])))"),
    ("filters_unchecked", "Spec.subscribe_rule",
     "SUBSCRIBE topic filters are not checked at all",
     "Mqtt/Parse.lean", "          if filterOK f o then",
     "          if true then"),
    ("filter_partial", "Spec.subscribe_rule",
     "a # level is accepted before the last level when three or more "
     "levels follow it (a/#/b/c/d)",
     "Mqtt/Value.lean", "  | l :: ls => levelOK l && levelsOK ls",
     "  | l :: ls => (levelOK l || (l == ['#'] && 3 ≤ ls.length)) "
     "&& levelsOK ls"),
    ("value_partial", "Spec.property_rule",
     "Request Problem Information 3 is accepted",
     "Mqtt/Value.lean", "  | 0x17, .byte n => n ≤ 1\n",
     "  | 0x17, .byte n => n ≤ 1 || n = 3\n"),
    ("subid_zero", "Spec.property_rule",
     "a Subscription Identifier of 0 is accepted",
     "Mqtt/Value.lean", "  | 0x0B, .varByte n => n != 0\n", ""),
    ("response_topic_hash", "Spec.property_rule",
     "a Response Topic holding # is accepted (+ is still refused)",
     "Mqtt/Value.lean",
     "  | 0x08, .utf8 s => !s.isEmpty && !s.contains '+' && !s.contains '#'",
     "  | 0x08, .utf8 s => !s.isEmpty && !s.contains '+'"),
    ("auth_unchecked", "Spec.property_rule",
     "Authentication Data is accepted without a Method",
     "Mqtt/Value.lean",
     "  !(ps.any fun p => p.id == 0x16) || ps.any fun p => p.id == 0x15",
     "  true"),
]


def run(cmd, cwd, timeout=3600):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env.get("PATH", "")
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                          text=True, timeout=timeout)


def copy_repo(dest):
    files = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT,
                           capture_output=True, text=True,
                           check=True).stdout.split("\0")
    for rel in files:
        if not rel:
            continue
        os.makedirs(os.path.join(dest, os.path.dirname(rel)), exist_ok=True)
        shutil.copy2(os.path.join(ROOT, rel), os.path.join(dest, rel))
    # Reuse the build of the unplanted repo, so only what the plant
    # touches is rebuilt.
    build = os.path.join(ROOT, ".lake")
    if os.path.isdir(build):
        shutil.copytree(build, os.path.join(dest, ".lake"), symlinks=True)


def try_plant(name, stmt, desc, rel, old, new, keep):
    d = tempfile.mkdtemp(prefix=f"mqtt-plant-{name}-")
    try:
        copy_repo(d)
        if rel:
            path = os.path.join(d, rel)
            with open(path) as fh:
                text = fh.read()
            if text.count(old) != 1:
                return dict(name=name, stmt=stmt, desc=desc, error=(
                    f"the text to replace stands {text.count(old)} times "
                    f"in {rel}"))
            with open(path, "w") as fh:
                fh.write(text.replace(old, new))
        tool = run(["lake", "build", "mqtt"], d)
        if tool.returncode != 0:
            return dict(name=name, stmt=stmt, desc=desc,
                        error="the tool does not build: "
                        + (tool.stdout + tool.stderr).strip()[-300:])
        t = run([sys.executable, "tests/run_tests.py", "--skip-build"], d)
        fails = [l for l in t.stdout.splitlines() if l.startswith("FAIL")]
        summary = [l for l in t.stdout.splitlines() if l.startswith("sections=")]
        full = run(["lake", "build"], d)
        errs = [l for l in (full.stdout + full.stderr).splitlines()
                if l.startswith("error: ") and "build failed" not in l]
        return dict(name=name, stmt=stmt, desc=desc,
                    tests_failed=t.returncode != 0,
                    n_fail=len(fails), first_fail=fails[0] if fails else "",
                    summary=summary[0] if summary else "",
                    proofs_failed=full.returncode != 0, n_err=len(errs),
                    first_err=errs[0] if errs else "")
    finally:
        if not keep:
            shutil.rmtree(d, ignore_errors=True)


def plural(n, word):
    return f"{n} {word}" + ("" if n == 1 else "s")


def short(text, n=150):
    text = text.replace("|", "/")
    return text if len(text) <= n else text[:n] + "..."


def main():
    keep = "--keep" in sys.argv
    picked = [a for a in sys.argv[1:] if not a.startswith("--")]
    plants = [p for p in PLANTS if not picked or p[0] in picked]
    results = [try_plant("none", "", "no plant: the repo as committed",
                         None, None, None, keep)]
    print(results[0])
    for p in plants:
        r = try_plant(*p, keep)
        print(r)
        results.append(r)
    lines = ["# Planted bugs: mqtt", "",
             "Written by `python3 tests/plant_bugs.py`. Each plant is a "
             "small change to the reader or its rules, put in a scratch "
             "copy of the repo. Tests: the harness run against the "
             "planted tool, caught when it reports a failure. Proofs: "
             "`lake build` with the planted code, caught when the proofs "
             "of the approved statements no longer build. Each plant "
             "makes the statement named in its row false, and the first "
             "failing test input is a witness: the planted reader "
             "accepts it, and the statement says no reader that meets it "
             "does. So no proof can be repaired to go through. The first "
             "row is the control, with no plant: it must pass both.", "",
             "| Plant | What it changes | Statement it makes false | "
             "Caught by the tests | Caught by the proofs |",
             "| --- | --- | --- | --- | --- |"]
    ok = True
    for r in results:
        if "error" in r:
            ok = False
            lines.append(f"| {r['name']} | {short(r['desc'])} | "
                         f"`{r['stmt']}` | could not run: "
                         f"{short(r['error'])} | |")
            continue
        if r["name"] == "none":
            good = not r["tests_failed"] and not r["proofs_failed"]
            ok = ok and good
            lines.append(f"| none | {r['desc']} | | "
                         f"{'no failure' if not r['tests_failed'] else 'FAILED'}"
                         f" ({short(r['summary'])}) | "
                         f"{'builds' if not r['proofs_failed'] else 'FAILED'} |")
            continue
        ok = ok and r["tests_failed"] and r["proofs_failed"]
        tests = (f"yes, {plural(r['n_fail'], 'failure')}; first: "
                 f"{short(r['first_fail'])}" if r["tests_failed"]
                 else "NO: the harness passes")
        proofs = (f"yes, {plural(r['n_err'], 'error')}; first: "
                  f"{short(r['first_err'])}"
                  if r["proofs_failed"] else "NO: the proofs build")
        lines.append(f"| {r['name']} | {short(r['desc'])} | `{r['stmt']}` "
                     f"| {tests} | {proofs} |")
    lines.append("")
    lines.append("Every plant caught by both: " + ("yes." if ok else "NO."))
    lines.append("")
    if not picked:
        with open(os.path.join(HERE, "PLANTED-BUGS.md"), "w") as fh:
            fh.write("\n".join(lines))
    print("\n".join(lines))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
