#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 11 follow-up (Main, after
# round 11's full-path module-label key): fixture "nd5", a TRUE shadow
# round 11's full-path key WRONGLY REUSED -- the reason round 12 reverted
# to the reviewer's original basename-only, namespaced key.
#
# X declares a 2-level-nested `Module M. Module N. Definition f := 1. End
# N. End M.`. B's requires/imports are INTERLEAVED, unlike nd1/nd3's
# upfront `Require Import X A.`: `Require Import X. Import M. Require
# Import A. Import N.` -- `Import M.` runs BEFORE `Require Import A.`
# (which transitively re-exports W). W is then rebuilt to add an
# UNRELATED TOP-LEVEL `Module N` (no "M." prefix), reachable only through
# A's `Require Export`. A fresh compile of B now has `Import N.` resolve
# to W's TOP-LEVEL N (the one most recently brought into scope by
# `Require Import A`), not X's nested M.N, even though `Import M.` ran
# first: Rocq's bare-name resolution for a fresh `Import <name>` statement
# is REQUIRE/IMPORT-ORDER-sensitive, not merely nesting-depth-sensitive --
# confirmed directly, a fresh compile fails with "f was not found".
# Reuse must be refused: round 11's full-path key ("M#N" vs "N", never
# colliding) wrongly allowed it; round 12's basename-only key ("N" vs
# "N", via module_label_marker) correctly refuses it, the same way it
# refuses nd1/nd4.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE, no module N): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, interleaved Require/Import resolves N to X.M.N): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing W really does
# fail -- a genuine, order-dependent ambiguity for the bare Import N.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild W.v (AFTER) for the sanity check: $(cat "$WORK/sanity-rebuild.log")"
build A.v >>"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild A.v (same source) against W1.v: $(cat "$WORK/sanity-rebuild.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the order-dependent-shadowing W succeeded -- this fixture does not actually exercise a real shadowing hazard."
fi
echo "$fresh_out" | grep -q "was not found" \
  || uc_fail "fresh B.v compile against the shadowing W did not fail with the expected 'reference not found' error -- got: $fresh_out"
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly so the main test starts from the same
# baseline B.vo/C.vo built above.
cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W0.v: $(cat "$WORK/restore.log")"

# AFTER: W grows an unrelated, top-level Module N, re-exported unchanged
# through A. Rebuild W and A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds an unrelated top-level Module N) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after W added an order-dependent-shadowing top-level Module N -- this is a TRUE shadow (confirmed by a failing fresh compile) and must be refused."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "Require/Import-order-dependent shadow correctly refused: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
