#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 8 (Lean round 7 review, "kd1").
# CRITICAL SOUNDNESS BUG, confirmed exploitable at ed2153adf8: X declares a
# nested `M.foo := 1` AND a top-level `foo := 1` -- SAME initial value,
# hence IDENTICAL digests, hence [Safe_typing.comp_iface] (round 7's own
# recursive walk) records TWO entries both keyed bare "foo" with the SAME
# digest. B proves `b : X.foo = 1` (the TOP-LEVEL one). X is rebuilt with
# ONLY the top-level `foo` changed to 2 (`M.foo` untouched).
#
# At ed2153adf8, [Safe_typing.iface_subset_ok]'s `Array.find_opt` always
# returns the FIRST "foo" entry it finds in the LIVE table, regardless of
# which RECORDED "foo" entry triggered the lookup. Since B's two recorded
# "foo" entries started IDENTICAL, checking the SECOND one against live's
# FIRST match (M.foo, unchanged) silently reports a MATCH even though the
# declaration B actually used (top-level foo) changed. B.vo was wrongly
# REUSED, and C could derive `False` from it with no axioms -- an
# unconditional, kernel-accepted unsoundness, not merely an imprecision.
#
# Round 8 closes this: every [iface_table] entry is now keyed by its FULL
# qualified path ("foo" vs "M.foo"), never a bare [Id.t], so there is
# nothing left to mask.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/X_before.v" "$WORK/X.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, X.foo = 1): $(cat "$WORK/setup.log")"

# Sanity: the two X.v variants really do have equal-at-first digests
# (same declared value) so this isn't just an ordinary content change.
grep -q 'foo := 1' "$D/X_before.v" || uc_fail "SANITY: X_before.v's top-level foo isn't 1, fixture is miswritten."

cp "$D/X_after.v" "$WORK/X.v"
build X.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD X (AFTER, top-level foo: 1 -> 2) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "CRITICAL: coqc C.v accepted a proof of False after reusing B.vo across X's top-level foo:1->2 change -- the bare-Id.t masking bug (binary-equivalence-taiga#841 round 8 kd1) is back or was never actually closed."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "top-level foo's change correctly refused, no False proved ($(echo "$c_out" | grep -im1 'inconsistent assumptions'))"
