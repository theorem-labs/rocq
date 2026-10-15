#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 8 (Lean round 7 review, "kd2"). Same
# bug and shape as `kd1_toplevel_bare_id_mask_refused`, mirrored: B proves
# `b : X.M.foo = 1` (the NESTED one this time), and X is rebuilt with
# ONLY `M.foo` changed to 2 (the top-level `foo` untouched). See that
# sibling fixture's header for the full argument.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/X_before.v" "$WORK/X.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, X.M.foo = 1): $(cat "$WORK/setup.log")"

cp "$D/X_after.v" "$WORK/X.v"
build X.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD X (AFTER, M.foo: 1 -> 2) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "CRITICAL: coqc C.v accepted a proof of False after reusing B.vo across X's nested M.foo:1->2 change -- the bare-Id.t masking bug (binary-equivalence-taiga#841 round 8 kd2) is back or was never actually closed."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "nested M.foo's change correctly refused, no False proved ($(echo "$c_out" | grep -im1 'inconsistent assumptions'))"
