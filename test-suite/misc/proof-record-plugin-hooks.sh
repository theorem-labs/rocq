#!/usr/bin/env bash

# BET-84 P2. Three registries let a plugin take over part of elaboration with
# a closure registered under a name: typeclass solvers
# ([Class_tactics.register_solver]), coercion hooks ([Coercion.register_hook])
# and canonical-solution hooks ([Evarconv.register_hook]). What such a closure
# does can depend on state that neither its name nor the plugin's files fix:
# rocq-elpi's hooks and solver run elpi programs that commands change (Claude
# gate at 0f8d815732, finding 4). So a proof that asks an ACTIVE hook or
# solver stores no term (reason plugin_hook), and a proof that asks none
# records the empty active list, so that a replay where one is active refuses
# it:
# - census row 8, channel typeclass_solver, key active;
# - census row 14, channel coercion_hooks;
# - census row 14, channel canonical_hooks.
#
# The plugin in misc/proof-record-plugin-hooks/src registers one probe in each
# registry, each of which always declines, and TestHookActivate activates
# them. Two compiles of theories/Probe.v, each with -proof-record, each in a
# new process and its own directory:
# - off: the TestHookActivate line commented out. Each probe proof must be
#        ELIGIBLE and hold its channel's read, or the test below proves
#        nothing;
# - on:  the file as it is. Each probe proof must carry reason plugin_hook
#        with a detail that names its channel, and its read must differ from
#        the one of "off".

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-record-plugin-hooks/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/plugin_hooks_plugin.cmxs

rm -rf out
mkdir -p out/off out/on
cp theories/Probe.v out/on/Probe.v
sed 's/^TestHookActivate\.$/(* TestHookActivate. *)/' theories/Probe.v > out/off/Probe.v
grep -q '^TestHookActivate\.$' out/on/Probe.v
grep -q '^(\* TestHookActivate\. \*)$' out/off/Probe.v

for d in off on; do
  rocq c -I src -R "out/$d" PluginHooks -proof-record "out/$d/Probe.v"
done

python3 - out/off/Probe.proof-record.jsonl out/on/Probe.proof-record.jsonl <<'PY'
import json, sys

# (proof, channel, row, key): the proof of Probe.v that reaches that choke
# point, and the read it must hold.
CHANNELS = [
    ("uses_solver", "typeclass_solver", "8", "active"),
    ("uses_coercion", "coercion_hooks", "14", ""),
    ("uses_canonical", "canonical_hooks", "14", ""),
]

def probes(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(line) for line in f]
    proofs = [l for l in lines if l["kind"] == "proof"]
    out = {}
    for name, channel, row, key in CHANNELS:
        entries = [p for p in proofs if p["name"].endswith("." + name)]
        if len(entries) != 1:
            sys.exit("%s: expected one proof %s, found %d" % (path, name, len(entries)))
        reads = [r for r in entries[0]["reads"] if r["channel"] == channel]
        if len(reads) != 1:
            sys.exit("%s: %s holds %d %s reads, expected 1: the proof no longer"
                     " reaches that choke point" % (path, name, len(reads), channel))
        r = reads[0]
        if r["row"] != row or r["key"] != key or r["value"] is None:
            sys.exit("%s: unexpected %s read %r" % (path, channel, r))
        out[channel] = (entries[0]["ineligible"], r["value"])
    return out

off, on = (probes(p) for p in sys.argv[1:3])
failed = False
for name, channel, _, _ in CHANNELS:
    (off_inel, off_value), (on_inel, on_value) = off[channel], on[channel]
    print("%-16s off %s %s" % (channel, off_value, off_inel))
    print("%-16s on  %s %s" % (channel, on_value, on_inel))
    if off_inel:
        print("FAIL: %s: %s is ineligible with no hook active" % (channel, name), file=sys.stderr)
        failed = True
    if not any(i["reason"] == "plugin_hook" and i["detail"].startswith(channel + ":") for i in on_inel):
        print("FAIL: %s: %s asked an active hook and carries no plugin_hook reason"
              % (channel, name), file=sys.stderr)
        failed = True
    if off_value == on_value:
        print("FAIL: %s: the read is the same with and without an active hook" % channel,
              file=sys.stderr)
        failed = True
sys.exit(1 if failed else 0)
PY
