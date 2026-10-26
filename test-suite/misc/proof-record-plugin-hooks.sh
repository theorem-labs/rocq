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
# them. Its TestSetClosures calls ONCE each process-wide closure setter of
# Rocq's core that the recorder fences (Evarconv.set_evar_conv, which unicoq's
# Set Use Unicoq calls, and the others): process-wide plugin state that no
# read sees (Claude reviews of 467292ce69 and beb759fef3), so every proof
# after it must store no term. One call each is one more than Rocq's own
# modules make, so a stock count set too high shows as a missing detail. Two
# compiles of theories/Probe.v, each with -proof-record, each in a new process
# and its own directory:
# - off: the TestHookActivate and TestSetClosures lines commented out. Each
#        probe proof must be ELIGIBLE and hold its channel's read, and so must
#        after_closures, or the test below proves nothing;
# - on:  the file as it is. Each probe proof must carry reason plugin_hook
#        with a detail that names its channel, and its read must differ from
#        the one of "off"; after_closures must carry plugin_hook with the
#        detail of each of those setters.
#
# The second plugin, library_closures, does the same for the fenced setters
# that belong to Ltac2 and ssreflect (Claude review of e16e9d2ae4), in
# theories/Library.v, which loads both. Off (TestSetLibraryClosures commented
# out): after_library must be eligible, so loading Ltac2 and ssreflect trips
# nothing (no stock count too low). On: after_library must carry the detail
# of each of their setters (no stock count too high).

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-record-plugin-hooks/

rocq makefile -f _CoqProject -o Makefile

make clean

make CAMLPKGS="-package rocq-runtime.plugins.ltac2,rocq-runtime.plugins.ssreflect" \
  src/plugin_hooks_plugin.cmxs src/library_closures_plugin.cmxs

rm -rf out
mkdir -p out/off out/on
cp theories/Probe.v out/on/Probe.v
sed -e 's/^TestHookActivate\.$/(* TestHookActivate. *)/' \
    -e 's/^TestSetClosures\.$/(* TestSetClosures. *)/' theories/Probe.v > out/off/Probe.v
grep -q '^TestHookActivate\.$' out/on/Probe.v
grep -q '^TestSetClosures\.$' out/on/Probe.v
grep -q '^(\* TestHookActivate\. \*)$' out/off/Probe.v
grep -q '^(\* TestSetClosures\. \*)$' out/off/Probe.v

for d in off on; do
  rocq c -I src -R "out/$d" PluginHooks -proof-record "out/$d/Probe.v"
done

status=0
python3 - out/off/Probe.proof-record.jsonl out/on/Probe.proof-record.jsonl <<'PY' || status=1
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

# Every setter of Rocq's core that Proof_recorder.closure_setter fences,
# called once by TestSetClosures (those of Ltac2 and ssreflect are below).
SETTERS = [
    "Evarconv.set_evar_conv", "Evarconv.set_solve_evars",
    "Typeclasses.set_solve_all_instances", "Typeclasses.set_solve_one_instance",
    "Namegen.set_reserved_typed_name", "CClosure.set_conv",
    "Coercionops.install_path_comparator", "Tactics.declare_intro_decomp_eq",
    "Equality.set_eq_dec_scheme_kind", "Ind_tables.set_declare_definition_scheme",
    "Ind_tables.set_register_definition_scheme", "Tacenv.register_ml_tactic ~overwrite",
    "Declare.Obls.set_default_tactic", "Proof_bullet.register_behavior",
]

def after_closures(path):
    with open(path, encoding="utf-8") as f:
        entries = [l for l in map(json.loads, f)
                   if l["kind"] == "proof" and l["name"].endswith(".after_closures")]
    if len(entries) != 1:
        sys.exit("%s: expected one proof after_closures, found %d" % (path, len(entries)))
    return entries[0]["ineligible"]

off_c, on_c = (after_closures(p) for p in sys.argv[1:3])
print("after_closures   off %s" % off_c)
print("after_closures   on  %s" % sorted(i["detail"] for i in on_c if i["reason"] == "plugin_hook"))
if off_c:
    print("FAIL: after_closures is ineligible with no plugin closure", file=sys.stderr)
    failed = True
seen = {i["detail"] for i in on_c if i["reason"] == "plugin_hook"}
for s in SETTERS:
    if s not in seen:
        print("FAIL: after_closures follows a call of %s and carries no plugin_hook for it" % s,
              file=sys.stderr)
        failed = True
sys.exit(1 if failed else 0)
PY

mkdir -p out/liboff out/libon
cp theories/Library.v out/libon/Library.v
sed -e 's/^TestSetLibraryClosures\.$/(* TestSetLibraryClosures. *)/' theories/Library.v \
  > out/liboff/Library.v
grep -q '^TestSetLibraryClosures\.$' out/libon/Library.v
grep -q '^(\* TestSetLibraryClosures\. \*)$' out/liboff/Library.v

for d in liboff libon; do
  rocq c -I src -R "out/$d" PluginHooks -proof-record "out/$d/Library.v"
done

python3 - out/liboff/Library.proof-record.jsonl out/libon/Library.proof-record.jsonl <<'PY' || status=1
import json, sys

# Every setter of Ltac2 and ssreflect that Proof_recorder.closure_setter
# fences, called once by TestSetLibraryClosures.
SETTERS = [
    "Ssrcommon.set_ssrautoprop_tac", "Tac2env.define_primitive",
    "Tac2env.define_ml_object", "Tac2env.set_compiled_global",
]

def marks(path):
    with open(path, encoding="utf-8") as f:
        entries = {l["name"].rsplit(".", 1)[-1]: l["ineligible"]
                   for l in map(json.loads, f) if l["kind"] == "proof"}
    for name in ("before_library", "after_library"):
        if name not in entries:
            sys.exit("%s: no proof %s" % (path, name))
    return entries

off, on = (marks(p) for p in sys.argv[1:3])
failed = False
for name in ("before_library", "after_library"):
    print("%-15s off %s" % (name, off[name]))
for name in ("before_library", "after_library"):
    print("%-15s on  %s" % (name, sorted(i["detail"] for i in on[name])))
for name in ("before_library", "after_library"):
    if off[name]:
        print("FAIL: %s is ineligible in a file that only loads Ltac2 and ssreflect" % name,
              file=sys.stderr)
        failed = True
if on["before_library"]:
    print("FAIL: before_library is ineligible before any extra setter call", file=sys.stderr)
    failed = True
seen = {i["detail"] for i in on["after_library"] if i["reason"] == "plugin_hook"}
for s in SETTERS:
    if s not in seen:
        print("FAIL: after_library follows a call of %s and carries no plugin_hook for it" % s,
              file=sys.stderr)
        failed = True
sys.exit(1 if failed else 0)
PY

exit $status
