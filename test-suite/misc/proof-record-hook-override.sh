#!/usr/bin/env bash

# BET-84 P2. [rocq compile -proof-record] records the active typeclass solvers
# of a proof that runs typeclass resolution (census row 8, channel
# typeclass_solver, key active). [Class_tactics.register_solver ~override:true]
# replaces the solver behind an unchanged name, so a record of the names only
# would let a replay accept a proof whose solver changed. The plugin in
# misc/proof-record-hook-override/src registers a solver whose condition is
# always false, so it never runs and no behaviour changes: only its
# registrations differ between the compiles below.
#
# Three compiles of theories/Probe.v, each with -proof-record, each in a new
# process and its own directory:
# - A:  the file as it is: the plugin registers the solver once, at its load;
# - A2: the same bytes compiled again: the control;
# - B:  the same file with a second registration under the same name
#       (TestSolverRegister) before the proof.
# The recorded value must be EQUAL in A and A2: an ordinary plugin load must
# not make a proof unreplayable. It must DIFFER between A and B: an override
# must be seen.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-record-hook-override/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/hook_override_plugin.cmxs

rm -rf out
mkdir -p out/A out/A2 out/B
cp theories/Probe.v out/A/Probe.v
cp theories/Probe.v out/A2/Probe.v
sed 's/^(\* OVERRIDE \*)$/TestSolverRegister./' theories/Probe.v > out/B/Probe.v
cmp out/A/Probe.v out/A2/Probe.v
grep -q '^TestSolverRegister\.$' out/B/Probe.v

for d in A A2 B; do
  rocq c -I src -R "out/$d" HookOverride -proof-record "out/$d/Probe.v"
done

A=out/A/Probe.proof-record.jsonl
A2=out/A2/Probe.proof-record.jsonl
B=out/B/Probe.proof-record.jsonl

python3 - "$A" "$A2" "$B" <<'PY'
import json, sys

def solver_read(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(line) for line in f]
    proofs = [l for l in lines if l["kind"] == "proof" and l["name"].endswith(".uses_solver")]
    if len(proofs) != 1:
        sys.exit("%s: expected one proof uses_solver, found %d" % (path, len(proofs)))
    reads = [r for r in proofs[0]["reads"] if r["channel"] == "typeclass_solver"]
    if len(reads) != 1:
        sys.exit("%s: uses_solver holds %d typeclass_solver reads, expected 1:"
                 " the proof no longer reaches Class_tactics.find_solver" % (path, len(reads)))
    r = reads[0]
    if r["row"] != "8" or r["key"] != "active" or r["value"] is None:
        sys.exit("%s: unexpected typeclass_solver read %r" % (path, r))
    return r["value"]

a, a2, b = (solver_read(p) for p in sys.argv[1:4])
print("A  (registered once):           ", a)
print("A2 (same file, new process):    ", a2)
print("B  (override, same solver name):", b)
failed = False
if a != a2:
    print("FAIL: an ordinary second compile moved the recorded value", file=sys.stderr)
    failed = True
if a == b:
    print("FAIL: a second registration with ~override:true did not move the recorded value", file=sys.stderr)
    failed = True
sys.exit(1 if failed else 0)
PY
