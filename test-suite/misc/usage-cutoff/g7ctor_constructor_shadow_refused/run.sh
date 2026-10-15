#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 4, test "g7ctor" (new,
# issuecomment-6189398514). The round-4 reviewer's own repro: the
# colliding name is a CONSTRUCTOR's own label, not its inductive type's --
# the kernel `iface_table` (pre-round-5) keyed an inductive block only by
# its TYPE's label, so a dependency adding a declaration that collides
# with an EXISTING constructor name was invisible to the shadow check.
#
# X declares `Inductive t := c | d.`. B does `Require Import X A.` and
# proves `b : t := c` -- at B's own compile time A has no `c`, so the
# unqualified `c` resolves to the constructor `X.c`. A is rebuilt to ADD
# `Definition c := 5.` -- a genuine, allowed-by-G1 addition (nothing that
# referenced A's OLD content changed). Once G1 makes this kind of
# addition reusable, a FRESH compile of B would now have `Import A`
# shadow the constructor `X.c` with the NEW `A.c : nat`, so `t := c` no
# longer typechecks (`"c" has type "nat"` where `"t"` is expected). A
# REUSED B.vo stays green regardless (its own absolute kernel reference
# to the constructor `X.c` is unaffected), silently diverging from what a
# fresh compile would now do -- G7 round 5's constructor-keyed
# `iface_entries_of_sfb` fix (emitting one entry per constructor, not
# just the inductive type's own label) must refuse reuse instead.
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, c resolves to constructor X.c): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing A really does fail.
cp "$D/A_after.v" "$WORK/A_fresh_check.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh_check.v ) >"$WORK/agent-standalone.log" 2>&1 \
  || uc_fail "SETUP: A_after.v (the shadowing addition) failed to compile standalone: $(cat "$WORK/agent-standalone.log")"
rm -f "$WORK"/A_fresh_check.*
cp "$D/B.v" "$WORK/B_fresh_check.v"
sed -i 's/Require Import X A\./Require Import X. Require Import A_after./' "$WORK/B_fresh_check.v" 2>/dev/null
cp "$D/A_after.v" "$WORK/A_after.v"
( cd "$WORK" && uc_coqc -Q . "" A_after.v ) >"$WORK/shadow-check.log" 2>&1 \
  || uc_fail "SETUP: could not build A_after.v as A_after for the fresh-shadow sanity check: $(cat "$WORK/shadow-check.log")"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the shadowing A succeeded -- this fixture does not actually exercise a constructor-shadowing hazard."
fi
rm -f "$WORK"/B_fresh_check.* "$WORK"/A_after.*

# AFTER: A grows a declaration that collides with the constructor X.c.
# Rebuild A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding c) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added a declaration (c) that collides with constructor X.c -- G7 must refuse this, since a fresh compile of B would now resolve c differently."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "constructor-label shadowing (c) correctly refused reuse: $(echo "$c_out" | grep -m1 'Inconsistent assumptions')"
