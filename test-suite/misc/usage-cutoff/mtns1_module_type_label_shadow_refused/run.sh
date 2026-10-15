#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mtns1", P1). Same cause as mns1, with a
# Module Type's own LABEL instead of a Module's. X declares `Module Type T.
# Parameter x : nat. End T.`; W (before) has no Module Type T. A does
# `Require Export W.` and nothing else. B does `Require Import X A. Module
# M : T. Definition x := 1. End M.` -- at B's own compile time, X.T is the
# ONLY module type named T reachable, so `T` resolves to X.T and `M`'s
# single field `x` satisfies it. W is then rebuilt to ADD `Module Type T.
# Parameter zzq : nat. End T.` -- a DIFFERENT module type, also named T,
# reachable only transitively through A's own `Require Export`. A fresh
# compile of B now has TWO module types named T in scope; the unqualified
# `T` resolves to W's, which requires a field `zzq` that `M` never
# provides. A REUSED B.vo stays green regardless. Without a shadow-table
# entry for the module type name "T" itself (its FIELDS are marked
# uncollidable and excluded from the shadow table on purpose, round 9 P3 --
# but the type's own NAME was never an entry there at all, P1), G7 has
# nothing to refuse this reuse against.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE, no Module Type T): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, T resolves to X.T): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing W (re-exported
# unchanged through A) really does fail, because T now resolves to W's T.
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
  uc_fail "SANITY: a fresh compile of B against the module-type-shadowing W succeeded -- this fixture does not actually exercise a shadowing hazard."
fi
echo "$fresh_out" | grep -q "is missing in" \
  || uc_fail "fresh B.v compile against the shadowing W did not fail with the expected missing-field error -- got: $fresh_out"
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly so the main test starts from the same
# baseline B.vo/C.vo built above.
cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W0.v: $(cat "$WORK/restore.log")"

# AFTER: W grows a second, colliding Module Type T, re-exported unchanged
# through A. Rebuild W and A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds colliding Module Type T) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after W added a second Module Type T re-exported unchanged through A -- the module type's own name must enter the G7 shadow table, since a fresh compile of B would now see T shadowed."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "Require-Export-transitive Module-Type-T shadowing correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
