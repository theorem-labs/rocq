#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 4, test "g7exp" (new,
# issuecomment-6189398514). The round-4 reviewer's own repro: the
# colliding name arrives through a dependency's `Require Export`, several
# hops below the dependent whose recorded closure must notice it.
#
# X declares `f := 1`. W (before) has no `f`. A does `Require Export W.`
# plus an unrelated declaration -- A's OWN source never mentions `f` at
# all. B does `Require Import X A.` and proves `b : f = 1 := eq_refl`;
# at B's own compile time `Import A` only brings in W's (f-less) exports,
# so the unqualified `f` resolves to `X.f`. W is then rebuilt to ADD
# `Definition f := 2.` -- A's OWN source is untouched, but A is rebuilt
# too (its recorded dependency on W must reflect the new W either way).
# Once G1 makes an unrelated-looking addition reusable, a FRESH compile
# of B would now see TWO `f` bindings in scope through `Import A`
# (A's own re-export of W's NEW `f`, alongside X's unchanged `f`) --
# shadowing or ambiguity, not the old `X.f = 1` proof obligation. A
# REUSED B.vo stays green regardless (its own absolute kernel reference
# to `X.f` is unaffected), silently diverging from what a fresh compile
# would now do -- G7's round-5 full-transitive-closure fix (closing this
# exact gap, since W is only reachable through A's OWN `Require Export`,
# never a DIRECT dependency of B at all) must refuse reuse instead.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W_before.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, f resolves to X.f): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing W (re-exported
# unchanged through A) really does fail.
cp "$D/W_after.v" "$WORK/W.v"
build W.v >"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild W.v (AFTER) for the sanity check: $(cat "$WORK/sanity-rebuild.log")"
build A.v >>"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild A.v (same source) against W_after.v: $(cat "$WORK/sanity-rebuild.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the Export-shadowing W succeeded -- this fixture does not actually exercise a shadowing hazard."
fi
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly (W, and A rebuilt against it again) so
# the main test starts from the same baseline B.vo/C.vo built above.
cp "$D/W_before.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W_before.v: $(cat "$WORK/restore.log")"

# AFTER: W grows `f`, re-exported unchanged through A. Rebuild W and A
# ONLY -- B.vo (and C.vo) are left stale.
cp "$D/W_after.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds colliding f) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W_after.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after W added a declaration (f) re-exported unchanged through A -- G7 must refuse this, since a fresh compile of B would now see f shadowed/ambiguous."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "Require-Export-transitive shadowing (W's new f, re-exported through A) correctly refused reuse: $(echo "$c_out" | grep -m1 'Inconsistent assumptions')"
