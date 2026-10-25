#!/usr/bin/env bash

# BET-84 P2. [rocq compile -proof-record] records the NAMES of the registered
# hooks and solvers that a proof reads. Three registries take ~override:true,
# which replaces the closure behind an unchanged name, from a plugin whose
# files are unchanged. A record of the names only would let a replay accept a
# proof whose solver or hook changed, so each registry counts how many times
# each name was registered and the recorded value is the (name, generation)
# list:
# - census row 8, channel typeclass_solver, key active
#   ([Class_tactics.register_solver] / [find_solver]);
# - census row 14, channel coercion_hooks ([Coercion.register_hook] /
#   [apply_hooks]);
# - census row 14, channel canonical_hooks ([Evarconv.register_hook] /
#   [apply_hooks]).
#
# The plugin in misc/proof-record-hook-override/src registers one probe in
# each registry: a solver whose condition is always false, and two hooks that
# always return None. None of them changes behaviour: only their
# registrations differ between the compiles below.
#
# Three compiles of theories/Probe.v, each with -proof-record, each in a new
# process and its own directory:
# - A:  the file as it is: the plugin registers each probe once, at its load;
# - A2: the same bytes compiled again: the control;
# - B:  the same file with a second registration of ALL THREE names before the
#       proofs (TestHookRegister).
# The recorded value must be EQUAL in A and A2 on each channel: an ordinary
# plugin load must not make a proof unreplayable. It must DIFFER between A and
# B on each channel: an override must be seen.

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
sed 's/^(\* OVERRIDE \*)$/TestHookRegister./' theories/Probe.v > out/B/Probe.v
cmp out/A/Probe.v out/A2/Probe.v
grep -q '^TestHookRegister\.$' out/B/Probe.v

for d in A A2 B; do
  rocq c -I src -R "out/$d" HookOverride -proof-record "out/$d/Probe.v"
done

A=out/A/Probe.proof-record.jsonl
A2=out/A2/Probe.proof-record.jsonl
B=out/B/Probe.proof-record.jsonl

python3 - "$A" "$A2" "$B" <<'PY'
import json, sys

# (proof, channel, row, key): the proof of Probe.v that reaches that choke
# point, and the read it must hold.
CHANNELS = [
    ("uses_solver", "typeclass_solver", "8", "active"),
    ("uses_coercion", "coercion_hooks", "14", ""),
    ("uses_canonical", "canonical_hooks", "14", ""),
]

def hook_reads(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(line) for line in f]
    proofs = [l for l in lines if l["kind"] == "proof"]
    values = {}
    for name, channel, row, key in CHANNELS:
        entries = [p for p in proofs if p["name"].endswith("." + name)]
        if len(entries) != 1:
            sys.exit("%s: expected one proof %s, found %d" % (path, name, len(entries)))
        if entries[0]["ineligible"]:
            sys.exit("%s: %s is ineligible (%r): a replay would refuse it whatever"
                     " the recorded value is" % (path, name, entries[0]["ineligible"]))
        reads = [r for r in entries[0]["reads"] if r["channel"] == channel]
        if len(reads) != 1:
            sys.exit("%s: %s holds %d %s reads, expected 1: the proof no longer"
                     " reaches that choke point" % (path, name, len(reads), channel))
        r = reads[0]
        if r["row"] != row or r["key"] != key or r["value"] is None:
            sys.exit("%s: unexpected %s read %r" % (path, channel, r))
        values[channel] = r["value"]
    return values

a, a2, b = (hook_reads(p) for p in sys.argv[1:4])
failed = False
for _, channel, _, _ in CHANNELS:
    print("%-18s A %s  A2 %s  B %s" % (channel, a[channel], a2[channel], b[channel]))
    if a[channel] != a2[channel]:
        print("FAIL: %s: an ordinary second compile moved the recorded value"
              % channel, file=sys.stderr)
        failed = True
    if a[channel] == b[channel]:
        print("FAIL: %s: a second registration with ~override:true did not move"
              " the recorded value" % channel, file=sys.stderr)
        failed = True
sys.exit(1 if failed else 0)
PY
