#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 3, test "i1_arguments_override_refused"
# (new). A adds `Arguments foo {x} y.` to an EXISTING declaration `foo`
# (x becomes implicit). B's `foo 1 2` (both explicit, pre-change) would,
# under a fresh compile against the changed A, misapply (1 to y, then 2 as
# a spurious extra argument) and fail. Reusing B.vo must now refuse too
# (round 3's fix: a per-name digest of the EFFECTIVE resolved implicits,
# not the raw Arguments libobject set -- an earlier revision's raw-leaf
# SET check wrongly tolerated this as an ignorable "addition").
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, foo 1 2 both explicit): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the Arguments-overridden A fails.
cp "$D/A_after.v" "$WORK/A_fresh.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh.v ) >"$WORK/fresh-a.log" 2>&1 \
  || uc_fail "SETUP: A_after.v failed to compile standalone: $(cat "$WORK/fresh-a.log")"
cp "$D/B.v" "$WORK/B_fresh.v"
sed -i 's/Require Import A\./Require Import A_fresh./' "$WORK/B_fresh.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh.v 2>&1)
fresh_rc=$?
rm -f "$WORK"/A_fresh.* "$WORK"/B_fresh.*
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the Arguments-overridden A succeeded -- this fixture doesn't exercise a real override hazard."
fi

# AFTER: A's foo gains the Arguments override. Rebuild A ONLY.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, Arguments foo {x} y) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A overrode foo's Arguments -- a fresh compile of B fails, so the reuse must be refused."
fi
echo "$c_out" | grep -q 'makes inconsistent assumptions over library' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected message -- got: $c_out"

uc_ok "Arguments override (foo {x} y) correctly refused reuse: $(echo "$c_out" | grep -m1 'makes inconsistent assumptions')"
