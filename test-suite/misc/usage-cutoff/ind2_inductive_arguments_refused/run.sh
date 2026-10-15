#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 5, test "ind2" (new,
# issuecomment-6189455137). Same shape as "ind1" but the `Arguments`
# override targets the INDUCTIVE TYPE itself, not a constructor.
#
# A declares `Inductive box (A : Type) := mk (a : A).`. B does
# `Require Import A.` and uses `box nat` (the parameter explicit,
# matching A's original signature). A is rebuilt to ADD
# `Arguments box {A}.` (the parameter becomes implicit). Once G1 makes
# this kind of override reusable, a FRESH compile of B would now try to
# apply the (now nullary-explicit) `box` to an extra explicit argument --
# Illegal application. A REUSED B.vo stays green regardless -- the
# Declaremods `G1Partition`/`DeclareInd` INDUCTIVE classifier fix (keying
# one entry per `IndRef`/`ConstructRef` target, round 5) must refuse
# reuse instead.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, box nat with explicit param): $(cat "$WORK/setup.log")"
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

# AFTER: A's inductive box gains the Arguments override. Rebuild A ONLY.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, Arguments box {A}) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A overrode box's Arguments -- a fresh compile of B fails, so the reuse must be refused."
fi
echo "$c_out" | grep -qE 'Inconsistent assumptions over module|makes inconsistent assumptions over library' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected message -- got: $c_out"

uc_ok "inductive-type Arguments override (box {A}) correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
