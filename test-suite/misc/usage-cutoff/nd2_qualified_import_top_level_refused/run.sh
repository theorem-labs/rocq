#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 10 (Lean round 10 review,
# issuecomment-6198625773, fixture "nd2", P3). X declares the same
# 2-level-nested `Module M. Module N. Definition f := 1. End N. End M.`
# as nd1. B does the QUALIFIED `Import M.N.` and uses `f`, resolving
# unambiguously to X's nested M.N. W is then rebuilt to add an UNRELATED,
# TOP-LEVEL (non-nested) `Module N` -- a DIFFERENT path than X's M.N (no
# "M." prefix at all), reachable only transitively through A's `Require
# Export`. Rocq's qualid resolution requires a matching path SUFFIX to
# disambiguate a query like `M.N`, not merely a matching innermost
# segment: W's bare top-level N can never match the 2-segment query
# "M.N", so a fresh compile of B is unaffected and still succeeds.
#
# Round 11 tried fixing this by encoding each label's FULL nesting path
# instead of just its innermost name -- then Main found (nd5, a BARE
# `Import N.` whose resolution DOES depend on Require/Import ORDER, not
# just nesting depth) that the full-path key is UNSOUND: it misses a
# genuine order-dependent shadow. Round 12 reverted to the reviewer's
# original shape (basename-only, namespaced away from constants via
# `module_label_marker`), which refuses this case and nd3/nd5/nd5b too.
# This IS an over-refusal -- a fresh compile succeeds here -- but it is
# SOUND, the same accepted category as the pre-existing coarse G7 rule
# (any same-basename declaration anywhere refuses, documented at sl5/
# inc2): relaxing it without replicating Rocq's own Require/Import-order-
# sensitive name resolution exactly cannot be done soundly with a
# per-library digest table.
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, Import M.N resolves to X.M.N): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER state (W adds an unrelated
# top-level Module N) still succeeds -- the qualified "M.N" never matches
# W's bare top-level N. This is what makes the refusal below an
# OVER-refusal, not evidence of a real shadow -- recorded here so the
# accepted imprecision is visible, not just asserted.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild W.v (AFTER) for the sanity check: $(cat "$WORK/sanity-rebuild.log")"
build A.v >>"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild A.v (same source) against W1.v: $(cat "$WORK/sanity-rebuild.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -ne 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the unrelated-top-level-N W failed -- expected to succeed (the qualified M.N can never match a top-level N); the over-refusal premise of this fixture no longer holds."
fi
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
  uc_fail "coqc C.v succeeded reusing B.vo after W added an unrelated top-level Module N -- expected a sound, basename-level over-refusal (round 12 reverted the full-path key as unsound, per nd5)."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "unrelated top-level Module N correctly (if conservatively) refused, sharing X's nested M.N's basename-level shadow key: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
