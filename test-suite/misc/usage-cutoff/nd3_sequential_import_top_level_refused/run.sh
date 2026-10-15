#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 10 (Lean round 10 review,
# issuecomment-6198625773, fixture "nd3", P3). Same as nd2, but B does
# `Import M.` then a SEPARATE `Import N.` instead of the single qualified
# `Import M.N.`. X and A are required TOGETHER, upfront (`Require Import
# X A.`), before either `Import` statement, so at the point `Import N.`
# runs, X's nested N is the only "N" that resolution has ever seen -- a
# fresh compile still succeeds regardless of W's new top-level N.
#
# Round 11 tried fixing this (and nd2) by encoding each label's FULL
# nesting path -- then Main found (nd5, which separates the `Require
# Import A` from the earlier `Import M.`) that order, not just depth,
# determines whether a bare `Import <name>` picks up a later top-level
# definer, so the full-path key is unsound. Round 12 reverted to the
# reviewer's original basename-only, namespaced shape, which refuses this
# case too -- an accepted over-refusal (see nd2's header for the full
# argument), not a soundness gap.
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, Import M. Import N. resolves to X.M.N): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER state (W adds an unrelated
# top-level Module N) still succeeds -- X and A were required together,
# upfront, so Import N. only ever sees X's nested N. This is what makes
# the refusal below an OVER-refusal, recorded here so the imprecision is
# visible, not just asserted.
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
  uc_fail "SANITY: a fresh compile of B against the unrelated-top-level-N W failed -- expected to succeed (Import M. Import N. with X/A required together upfront only ever sees X's nested N); the over-refusal premise of this fixture no longer holds."
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

uc_ok "unrelated top-level Module N correctly (if conservatively) refused, sequential-Import variant: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
