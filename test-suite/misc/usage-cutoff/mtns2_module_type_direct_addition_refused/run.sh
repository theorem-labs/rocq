#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mtns2"). CONTROL for mtns1: the SAME
# shape of addition, `Module Type T2. Parameter zzq : nat. End T2.`, added
# DIRECTLY to A's own source (not reached transitively through a
# dependency's `Require Export`). Already correctly refused with no fix
# needed -- A's own content changing moves A's own exact objects digest, so
# ANY dependent of A is refused regardless of the G7 shadow mechanism
# mtns1 exercises.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, T resolves to X.T): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, direct Module Type T2 addition) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A directly added an unrelated Module Type T2 -- this control is expected to already refuse via A's own exact digest, with no G7 fix needed."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "direct Module Type T2 addition in A correctly refused reuse via A's own digest (control, unaffected by the G7 fix): $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
