#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 G7, test "g7_shadowing_refused"
# (new). Depends on: G1 (the per-declaration subset split that makes an
# added declaration reusable in the first place -- without G1, this
# scenario is already refused for an unrelated reason, the exact-equality
# objects digest, and would never exercise G7's own code at all) and G7
# itself (kernel/safe_typing.ml's `flatten_closure`/`closure_subset_ok`,
# called from `dep_ok`).
#
# Review841's own "sh" experiment, lifted directly: X declares `f := 1`.
# B does `Require Import X A.` and proves `b : f = 1 := eq_refl` -- at B's
# own compile time A has no `f`, so the unqualified `f` resolves to `X.f`.
# A (which B also directly requires, for an unrelated declaration) is
# rebuilt to ADD `Definition f := 2.` -- a genuine, allowed-by-G1 addition
# (nothing that referenced A's OLD content changed). Once G1 makes this
# kind of addition reusable, a FRESH compile of B would now have `Import A`
# shadow `X.f` with the NEW `A.f`, resolving `f = 1` against `A.f := 2`
# instead and failing to typecheck (`eq_refl` would not have type
# `A.f = 1`). A REUSED B.vo would stay green regardless (its own absolute
# kernel reference to `X.f` is unaffected), silently diverging from what a
# fresh compile would now do -- exactly the gap G7 exists to close by
# refusing reuse instead.
#
# A second A variant (`A_after_noncolliding.v`, adding an UNRELATED name
# `g` instead of `f`) confirms G7 does not over-trigger: an addition that
# doesn't collide with anything B's closure resolved must still reuse.
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, f resolves to X.f): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing A really does
# fail (or at least resolve differently) -- otherwise this fixture doesn't
# exercise a real shadowing hazard at all.
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
  uc_fail "SANITY: a fresh compile of B against the shadowing A succeeded -- this fixture does not actually exercise a name-shadowing hazard, nothing to test."
fi
rm -f "$WORK"/B_fresh_check.* "$WORK"/A_after.*

# AFTER: A grows a declaration that collides with a name B's closure
# resolved (through X). Rebuild A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding f) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added a declaration (f) that collides with a name B's own closure resolved (X.f) -- G7's whole point is this must be refused, since a fresh compile of B would now resolve f differently."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

# Non-colliding addition must still reuse (G7 must not over-trigger).
cp "$D/A_before.v" "$WORK/A.v"
build A.v >"$WORK/rebuild2.log" 2>&1 || uc_fail "REBUILD A (back to BEFORE) failed unexpectedly: $(cat "$WORK/rebuild2.log")"
build B.v >>"$WORK/rebuild2.log" 2>&1 || uc_fail "REBUILD B (back to BEFORE) failed unexpectedly: $(cat "$WORK/rebuild2.log")"
build C.v >>"$WORK/rebuild2.log" 2>&1 || uc_fail "REBUILD C (back to BEFORE) failed unexpectedly: $(cat "$WORK/rebuild2.log")"
before_hash=$(uc_sha256 "$WORK/B.vo")
cp "$D/A_after_noncolliding.v" "$WORK/A.v"
build A.v >"$WORK/rebuild3.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds non-colliding g) failed unexpectedly: $(cat "$WORK/rebuild3.log")"
noncol_out=$(build C.v 2>&1)
noncol_rc=$?
if [ "$noncol_rc" -ne 0 ]; then
  echo "$noncol_out" >&2
  uc_fail "coqc C.v was refused after A added a NON-colliding declaration (g) -- G7 is over-triggering on an unrelated addition: $noncol_out"
fi
after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C with a non-colliding addition to A -- B was silently recompiled rather than genuinely reused."

uc_ok "colliding addition (f) correctly refused ($(echo "$c_out" | grep -m1 'Inconsistent assumptions')), non-colliding addition (g) correctly reused unchanged (sha256 $after_hash)"
