#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 4, test "g7pre" (new,
# issuecomment-6189398514). The round-4 reviewer's own repro: the
# colliding name is the PRELUDE's own `negb` (auto-opened by every file
# via the implicit prelude `Import`, never a direct `Require` of the
# dependent's -- the prelude's own DirPath never appears in a dependent's
# "direct needed" array, only in its FULL transitive closure).
#
# A (before) declares only an unrelated definition, so `negb` resolves to
# the prelude's own `negb` throughout. B does `Require Import A.` and
# proves `b : negb true = false := eq_refl` against the PRELUDE's negb.
# A is rebuilt to ADD its OWN `Definition negb (b : bool) := b.` (the
# identity, NOT the real negation) -- a genuine, allowed-by-G1 addition
# (nothing B's proof referenced about A's OLD content changed). Once G1
# makes this kind of addition reusable, a FRESH compile of B would now
# have `Import A` shadow the prelude's `negb` with A's own (identity)
# `negb`, so `negb true = false` no longer typechecks (`negb true`
# reduces to `true`, not `false`, under A's new definition). A REUSED
# B.vo stays green regardless (its own absolute kernel reference to the
# PRELUDE's negb is unaffected), silently diverging from what a fresh
# compile would now do -- G7's round-5 fix (closing this gap, since the
# prelude is never a direct dependency recorded in anyone's own `needed`
# array, only present via the full transitive closure every compile
# implicitly loads) must refuse reuse instead.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, negb resolves to the prelude's negb): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the negb-shadowing A really does fail.
cp "$D/A_after.v" "$WORK/A_fresh_check.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh_check.v ) >"$WORK/agent-standalone.log" 2>&1 \
  || uc_fail "SETUP: A_after.v (the negb-shadowing addition) failed to compile standalone: $(cat "$WORK/agent-standalone.log")"
rm -f "$WORK"/A_fresh_check.*
cp "$D/B.v" "$WORK/B_fresh_check.v"
sed -i 's/Require Import A\./Require Import A_after./' "$WORK/B_fresh_check.v"
cp "$D/A_after.v" "$WORK/A_after.v"
( cd "$WORK" && uc_coqc -Q . "" A_after.v ) >"$WORK/shadow-check.log" 2>&1 \
  || uc_fail "SETUP: could not build A_after.v as A_after for the fresh-shadow sanity check: $(cat "$WORK/shadow-check.log")"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the negb-shadowing A succeeded -- this fixture does not actually exercise a prelude-shadowing hazard."
fi
rm -f "$WORK"/B_fresh_check.* "$WORK"/A_after.*

# AFTER: A grows its own negb, shadowing the prelude's. Rebuild A ONLY --
# B.vo (and C.vo) are left stale.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding negb) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added a declaration (negb) that collides with the prelude's own negb -- G7 must refuse this, since a fresh compile of B would now resolve negb differently."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "prelude-name shadowing (negb) correctly refused reuse: $(echo "$c_out" | grep -m1 'Inconsistent assumptions')"
