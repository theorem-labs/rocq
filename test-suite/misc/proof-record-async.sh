#!/usr/bin/env bash

# BET-84 P2. With async proofs the proofs of a file run in worker processes,
# and the recorder's counters, caches and fences count per process: a record
# made in the master describes the master only. [rocq compile -proof-record]
# must therefore mark EVERY proof of such a file ineligible
# (toplevel/ccompile.ml, Proof_recorder.trip_fence ~reason:"async_proofs").
#
# Two compiles of Proofs.v, each with -proof-record, each in its own
# directory:
# - sync:  the ordinary compile. Every proof entry must carry an EMPTY
#          ineligible list, or the test below proves nothing;
# - async: the same bytes with -async-proofs on. Every proof entry must carry
#          the reason async_proofs.
# The two records must hold the same proofs: a fence that worked by dropping
# the entries would pass a weaker test.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-record-async/

rm -rf out
mkdir -p out/sync out/async
cp Proofs.v out/sync/Proofs.v
cp Proofs.v out/async/Proofs.v

rocq c -proof-record out/sync/Proofs.v
rocq c -async-proofs on -proof-record out/async/Proofs.v

python3 - out/sync/Proofs.proof-record.jsonl out/async/Proofs.proof-record.jsonl <<'PY'
import json, sys

def proofs(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(line) for line in f]
    entries = [l for l in lines if l["kind"] == "proof"]
    if len(entries) < 2:
        sys.exit("%s: expected the entries of two proofs, found %d" % (path, len(entries)))
    return entries

sync, asyn = (proofs(p) for p in sys.argv[1:3])
failed = False

for p in sync:
    print("sync  %-28s ineligible %s" % (p["name"], p["ineligible"]))
    if p["ineligible"]:
        print("FAIL: %s is ineligible in an ordinary compile" % p["name"], file=sys.stderr)
        failed = True

for p in asyn:
    print("async %-28s ineligible %s" % (p["name"], p["ineligible"]))
    if not any(i["reason"] == "async_proofs" for i in p["ineligible"]):
        print("FAIL: %s carries no async_proofs reason" % p["name"], file=sys.stderr)
        failed = True

if [p["name"] for p in sync] != [p["name"] for p in asyn]:
    print("FAIL: the two records do not hold the same proofs: %s against %s"
          % ([p["name"] for p in sync], [p["name"] for p in asyn]), file=sys.stderr)
    failed = True

sys.exit(1 if failed else 0)
PY
