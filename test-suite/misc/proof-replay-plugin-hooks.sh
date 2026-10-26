#!/usr/bin/env bash

# BET-84 P3. Replay must refuse a stored term when a plugin's closure could
# have decided the proof, in each of the three ways the recorder knows:
# - the proof asked an ACTIVE typeclass solver, coercion hook or
#   canonical-solution hook: the recorder marks it ineligible (reason
#   plugin_hook), and replay never uses it;
# - the registration's proof asked the hooks when none was active, and the
#   grade activates one: the recorded read of the active list (the digest of
#   its names) differs, and the proof misses on that channel;
# - a plugin installs a closure over Rocq's own (Evarconv.set_evar_conv and
#   the other fenced setters): the process-wide fence trips, and no proof of
#   the process after it is replayed, though its record is clean.
# And it must still replay a proof whose hook lists are unchanged. The proof
# that asks the canonical-solution hooks also reads the notation = and the
# canonical_structure table, channels replay does not evaluate yet, so
# uses_canonical misses on one of them (the runs show notation) in every
# grade; for it the test requires only that it is never replayed.
#
# The plugin is misc/proof-record-plugin-hooks/src, built here in a copy so
# that the two tests can run at the same time. Probe.v has two switch lines,
# TestHookActivate and TestSetClosures; each variant comments some out. Every
# compile is of out/w/Probe.v under the logical name PluginHooks, in a new
# process; a registration's record is moved to out/rec, made read-only, and
# given to the grade compile with its SHA-256.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-replay-plugin-hooks/
here=$PWD

rm -rf build out
mkdir -p build/src out/v out/rec
for f in META.coq-test-suite pluginHooks.mlg pluginHooksImpl.ml pluginHooksImpl.mli \
         plugin_hooks_plugin.mlpack; do
  cp "../proof-record-plugin-hooks/src/$f" build/src/
done
printf '%s\n' src/META.coq-test-suite '-I src' '' src/pluginHooks.mlg src/pluginHooksImpl.ml \
  src/pluginHooksImpl.mli src/plugin_hooks_plugin.mlpack > build/_CoqProject
(cd build && rocq makefile -f _CoqProject -o Makefile && make src/plugin_hooks_plugin.cmxs)

grep -q '^TestHookActivate\.$' Probe.v
grep -q '^TestSetClosures\.$' Probe.v
off_hooks='s/^TestHookActivate\.$/(* TestHookActivate. *)/'
off_closures='s/^TestSetClosures\.$/(* TestSetClosures. *)/'
sed -e "$off_hooks" -e "$off_closures" Probe.v > out/v/off.v
sed -e "$off_closures" Probe.v > out/v/hooks.v
sed -e "$off_hooks" Probe.v > out/v/closures.v
cp Probe.v out/v/on.v

compile() {
  local v=$1; shift
  rm -rf out/w
  mkdir -p out/w
  cp "out/v/$v.v" out/w/Probe.v
  (cd out/w && rocq c -I "$here/build/src" -R . PluginHooks "$@" Probe.v)
}

register() {
  compile "$1" -proof-record
  mv out/w/Probe.proof-record.jsonl "out/rec/$1.jsonl"
  chmod 0444 "out/rec/$1.jsonl"
}

grade() {
  local variant=$1 record=$2 digest
  digest=$(sha256sum "out/rec/$record.jsonl" | cut -d ' ' -f 1)
  compile "$variant" -proof-replay "$here/out/rec/$record.jsonl" -proof-replay-digest "$digest" \
    -proof-replay-ratio 1
  cp out/w/Probe.proof-replay.json "out/$variant-on-$record.json"
}

register off
register on
grade off off
grade hooks off
grade closures off
grade on on

python3 - out <<'PY'
import json, sys

out = sys.argv[1]
# The proofs whose hook read decides their replay, with that read's channel.
HOOKED = [("uses_solver", "typeclass_solver"), ("uses_coercion", "coercion_hooks")]
AFTER = ["after_closures", "after_closures_2"]
failed = False

def not_hit(case, proof):
    global failed
    s, got = summary(case)
    o = got.get(proof)
    print("%-20s %-18s %s%s" % (case, proof, o and o["outcome"], o and o.get("channel") and " " + o["channel"] or ""))
    if o is None or o["outcome"] == "hit":
        print("FAIL: %s: %s must not be replayed, got %r" % (case, proof, o), file=sys.stderr)
        failed = True

def summary(name):
    with open("%s/%s.json" % (out, name), encoding="utf-8") as f:
        s = json.load(f)
    return s, {o["name"].rsplit(".", 1)[-1]: o for o in s["outcomes"]}

def want(case, proof, outcome, channel=None):
    global failed
    s, got = summary(case)
    o = got.get(proof)
    ok = o is not None and o["outcome"] == outcome and o.get("channel") == channel
    print("%-20s %-18s %s%s" % (case, proof, o and o["outcome"], o and o.get("channel") and " " + o["channel"] or ""))
    if not ok:
        print("FAIL: %s: %s should be %s%s, got %r" % (case, proof, outcome,
              " on " + channel if channel else "", o), file=sys.stderr)
        failed = True

def want_fence(case, tripped):
    global failed
    s, _ = summary(case)
    fence = s.get("fence")
    print("%-20s fence %r" % (case, fence))
    ok = (fence or "").startswith("plugin_hook: ") if tripped else fence is None
    if not ok:
        print("FAIL: %s: fence %r, wanted %s" % (case, fence, "plugin_hook" if tripped else "none"),
              file=sys.stderr)
        failed = True

# Nothing a proof read changed: every proof replays, the hook proofs too.
for p, _ in HOOKED:
    want("off-on-off", p, "hit")
for p in ["before_closures"] + AFTER:
    want("off-on-off", p, "hit")
not_hit("off-on-off", "uses_canonical")
want_fence("off-on-off", False)

# The grade activates the hooks the registration did not: each hook proof
# misses on its own channel's read; the others still replay.
for p, channel in HOOKED:
    want("hooks-on-off", p, "read", channel)
not_hit("hooks-on-off", "uses_canonical")
for p in ["before_closures"] + AFTER:
    want("hooks-on-off", p, "hit")
want_fence("hooks-on-off", False)

# The grade installs plugin closures the registration did not: the proofs
# before replay, every proof after is refused by the fence.
for p, _ in HOOKED:
    want("closures-on-off", p, "hit")
want("closures-on-off", "before_closures", "hit")
for p in AFTER:
    want("closures-on-off", p, "ineligible")
want_fence("closures-on-off", True)

# The registration itself asked active hooks and ran after plugin closures:
# those proofs are ineligible in the record and never replayed.
for p in [p for p, _ in HOOKED] + ["uses_canonical"] + AFTER:
    want("on-on-on", p, "ineligible")
want("on-on-on", "before_closures", "hit")
with open("%s/rec/on.jsonl" % out, encoding="utf-8") as f:
    on = {l["name"].rsplit(".", 1)[-1]: l for l in map(json.loads, f) if l["kind"] == "proof"}
for p in [p for p, _ in HOOKED] + ["uses_canonical"] + AFTER:
    reasons = [i["reason"] for i in on[p]["ineligible"]]
    if "plugin_hook" not in reasons or on[p]["replay"] is not None:
        print("FAIL: record on: %s carries %r and %s a term" % (p, reasons,
              "stores" if on[p]["replay"] is not None else "stores no"), file=sys.stderr)
        failed = True

sys.exit(1 if failed else 0)
PY
