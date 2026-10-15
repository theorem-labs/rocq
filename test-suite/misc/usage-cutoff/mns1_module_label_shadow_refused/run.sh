#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mns1", P1). A Module's own LABEL never
# entered the G7 shadow table -- only fields nested inside it did
# (`iface_entries_of_sfb`). X declares `Module M. Definition f := 1. End
# M.`; W (before) has no Module M at all. A does `Require Export W.` and
# nothing else. B does `Require Import X A. Import M. Definition b : f = 1
# := eq_refl.` -- at B's own compile time, X.M is the ONLY module named M
# reachable, so `Import M` unambiguously opens X.M and `f` resolves to
# X.M.f. W is then rebuilt to ADD `Module M. Definition zzq := 2. End M.`
# -- a DIFFERENT module, also named M, reachable only transitively through
# A's own `Require Export`. A fresh compile of B now has TWO modules named
# M in scope; `Import M` resolves to W's (the one from the directly
# `Require`d chain, per Rocq's Nametab precedence), so the unqualified `f`
# is no longer in scope at all. A REUSED B.vo stays green regardless (its
# own absolute kernel reference to X.M.f is unaffected), silently
# diverging from what a fresh compile would now do. Without a shadow-table
# entry for the module name "M" itself, G7's existing shadow check has no
# "M" record to compare W's new "M" against, so nothing refuses this reuse.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE, no Module M): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, Import M resolves to X.M): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing W (re-exported
# unchanged through A) really does fail, because Import M now opens W's M.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild W.v (AFTER) for the sanity check: $(cat "$WORK/sanity-rebuild.log")"
build A.v >>"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild A.v (same source) against W_after.v: $(cat "$WORK/sanity-rebuild.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the module-shadowing W succeeded -- this fixture does not actually exercise a shadowing hazard."
fi
echo "$fresh_out" | grep -q "was not found" \
  || uc_fail "fresh B.v compile against the shadowing W did not fail with the expected 'reference not found' error -- got: $fresh_out"
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly so the main test starts from the same
# baseline B.vo/C.vo built above.
cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W0.v: $(cat "$WORK/restore.log")"

# AFTER: W grows a second, colliding Module M, re-exported unchanged
# through A. Rebuild W and A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds colliding Module M) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after W added a second Module M re-exported unchanged through A -- the module's own name must enter the G7 shadow table, since a fresh compile of B would now see M shadowed."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "Require-Export-transitive Module-M shadowing correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
