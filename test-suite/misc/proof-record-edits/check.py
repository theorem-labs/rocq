#!/usr/bin/env python3
"""BET-84 P2: the edit pairs of misc/proof-record-edits.sh.

A replay may reuse a proof's stored term only when everything the proof read
still has the value it had. Each case directory holds two variants of one
file, A.v and B.v, that differ in one input of the proofs its `expect` file
names; both variants compile. The record of each variant must REFUSE the
other compile: its entry for the proof must hold a witness that the input
changed.

A witness is one of:
- the entry is ineligible: a replay never reuses it;
- the statement, the sentences, the position or the toolchain key differ;
- a read (or start table) that BOTH entries hold under the same row,
  channel and key, with different values.
A read that only one entry holds is not a witness: a replay evaluates the
reads of the record it holds, so a read the other compile made, and this
record lacks, is never compared.

Lines of `expect`:
  refuse-by-read <proof> <channel>
      Both entries are eligible, and in both directions a read on <channel>
      is a witness: the recorder saw the edited input.
  refuse-ineligible <proof> <reason>
      Both entries carry the ineligibility <reason>.

Usage: check.py CASE_DIR A_RECORD B_RECORD
"""

import json
import sys

FIELDS = ("statement", "sentences", "position", "toolchain_key")


def entries(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(line) for line in f]
    return {l["name"].rsplit(".", 1)[-1]: l for l in lines if l["kind"] == "proof"}


def reads(entry):
    return {(r["row"], r["channel"], r["key"]): r["value"]
            for r in entry["reads"] + entry["start_tables"]}


def witnesses(x, y):
    """What refuses a replay of entry x in the compile that wrote entry y."""
    found = []
    if x["ineligible"]:
        found.append("ineligible " + ",".join(i["reason"] for i in x["ineligible"]))
    found += ["field " + f for f in FIELDS if x[f] != y[f]]
    ry = reads(y)
    found += ["read %s/%s/%s" % k for k, v in sorted(reads(x).items()) if k in ry and ry[k] != v]
    return found


def main():
    case, path_a, path_b = sys.argv[1:4]
    a, b = entries(path_a), entries(path_b)
    failed = False

    def fail(msg):
        nonlocal failed
        print("FAIL: %s: %s" % (case, msg), file=sys.stderr)
        failed = True

    with open(case + "/expect", encoding="utf-8") as f:
        expect = [l.split() for l in f if l.strip() and not l.startswith("#")]
    for mode, proof, what in expect:
        if proof not in a or proof not in b:
            fail("%s: no entry in %s" % (proof, "A" if proof not in a else "B"))
            continue
        pa, pb = a[proof], b[proof]
        wab, wba = witnesses(pa, pb), witnesses(pb, pa)
        print("%s %s: A->B %s" % (case, proof, wab or "NO WITNESS"))
        print("%s %s: B->A %s" % (case, proof, wba or "NO WITNESS"))
        if mode == "refuse-by-read":
            for side, p in (("A", pa), ("B", pb)):
                if p["ineligible"]:
                    fail("%s is ineligible in %s (%r): the read is not what refuses it"
                         % (proof, side, p["ineligible"]))
            for direction, w in (("A->B", wab), ("B->A", wba)):
                if not any(x.startswith("read ") and x.split("/", 2)[1] == what for x in w):
                    fail("%s %s: no %s read differs, so a replay would reuse the term"
                         % (proof, direction, what))
        elif mode == "refuse-ineligible":
            for side, p in (("A", pa), ("B", pb)):
                if not any(i["reason"] == what for i in p["ineligible"]):
                    fail("%s in %s carries no %s reason (%r)" % (proof, side, what, p["ineligible"]))
        else:
            fail("unknown expectation %r" % mode)
    sys.exit(1 if failed else 0)


main()
