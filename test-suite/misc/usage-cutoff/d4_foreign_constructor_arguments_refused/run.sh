#!/usr/bin/env bash
# binary-equivalence-taiga#841, test "d4" (new, CutoffG7b). Not itself a
# Review841-numbered finding: this fixture fills the one GlobRef-kind gap
# none of g7ctor/ind1/ind2/forg individually cover. g7ctor is about G7's
# closure-table name collision (not Arguments); ind1 is a LOCAL
# constructor's own Arguments override; forg is a FOREIGN CONSTANT's
# Arguments override. This is the remaining combination: a
# `#[global] Arguments` override, issued in A, on a FOREIGN CONSTRUCTOR
# (declared in X, not A) -- the one GlobRef variant that exercises
# `Declaremods.G1Partition.modpath_of_gr`'s `ConstructRef` branch
# specifically (an attempt to "forge" coverage by picking a target kind
# none of the other new fixtures individually exercise).
#
# X declares `Inductive t := c (n : nat).`. A (before) only
# `Require Import X.` plus an unrelated definition. B does
# `Require Import X A.` and uses `c 3` (the argument explicit, matching
# c's ORIGINAL signature). A is rebuilt to ADD
# `#[global] Arguments X.c {n}.`, overriding a constructor it does not
# own. Once G1 makes this kind of addition reusable, a FRESH compile of
# B would now try to apply the (now nullary-explicit) constructor `c` to
# an extra explicit argument -- Illegal application. A REUSED B.vo stays
# green regardless -- the same `G1Partition.classify`/`modpath_of_gr`/
# `is_local` fix that closes "forg" for constants must also refuse this
# (its `modpath_of_gr` already has an explicit `ConstructRef` case, so no
# new code is needed if the mechanism is sound for this target kind too).
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, c 3 with explicit arg): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the foreign-constructor Arguments
# override really does fail.
cp "$D/A_after.v" "$WORK/A_fresh.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh.v ) >"$WORK/fresh-a.log" 2>&1 \
  || uc_fail "SETUP: A_after.v failed to compile standalone: $(cat "$WORK/fresh-a.log")"
cp "$D/B.v" "$WORK/B_fresh.v"
sed -i 's/Require Import X A\./Require Import X. Require Import A_fresh./' "$WORK/B_fresh.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh.v 2>&1)
fresh_rc=$?
rm -f "$WORK"/A_fresh.* "$WORK"/B_fresh.*
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the foreign-constructor Arguments override succeeded -- this fixture doesn't exercise a real override hazard."
fi

# AFTER: A gains a foreign Arguments override on X's constructor c.
# Rebuild A ONLY.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, foreign Arguments X.c {n}) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added a foreign Arguments override on constructor X.c -- a fresh compile of B fails, so the reuse must be refused."
fi
echo "$c_out" | grep -qE 'Inconsistent assumptions over module|makes inconsistent assumptions over library' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected message -- got: $c_out"

uc_ok "foreign Arguments override on a CONSTRUCTOR (X.c {n}, issued in A but not owned by A) correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
