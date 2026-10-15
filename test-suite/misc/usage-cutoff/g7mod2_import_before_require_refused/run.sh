#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 6 review (issuecomment-6191273575),
# "g7mod2". Same nested-module shape as `g7mod_nested_module_refused`,
# but B does `Import X.M` BEFORE `Require Import A` (not after, as in
# the sibling `imp1`-style control where the LATER import correctly
# wins and reuse is fine either way). With `Import X.M` first, a fresh
# compile resolves the unqualified `f` to `X.M.f` regardless of A, so
# A's later addition does NOT change what a fresh B resolves to -- but
# round 5's closure table never recorded `X.M.f` in the first place
# (same root cause as g7mod: `M` was hidden inside X's `None`-iface
# table), so a naive fix that keys ANY name collision would have
# wrongly refused a case that's actually safe. This fixture's A
# addition DOES collide (confirms refusal is still correct when the
# fresh outcome genuinely changes: `eq_refl : f = 1` only typechecks
# because `f` resolves to `X.M.f = 1`, and a colliding `A.f := 2`
# dependent typecheck would differ if resolution order flips).
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/B.v" "$WORK/B_fresh_check.v"
sed -i 's/Require Import A\./Require Import A_after./' "$WORK/B_fresh_check.v"
cp "$D/A_after.v" "$WORK/A_after.v"
( cd "$WORK" && uc_coqc -Q . "" A_after.v ) >"$WORK/shadow-check.log" 2>&1 \
  || uc_fail "SETUP: could not build A_after.v as A_after for the fresh-shadow sanity check: $(cat "$WORK/shadow-check.log")"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the shadowing A succeeded -- this fixture does not actually exercise a name-shadowing hazard, nothing to test."
fi
rm -f "$WORK"/B_fresh_check.* "$WORK"/A_after.*

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding f) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added f, colliding with X.M.f (opened before A) -- a fresh compile of B against the same new A fails (confirmed above), so this reuse is wrong."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "colliding addition (f) correctly refused ($(echo "$c_out" | grep -m1 'Inconsistent assumptions'))"
