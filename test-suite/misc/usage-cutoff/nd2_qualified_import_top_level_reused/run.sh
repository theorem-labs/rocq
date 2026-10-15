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
# "M.N", so a fresh compile of B is unaffected and still succeeds. Before
# round 11's fix, the G7 shadow table reduced every label to its bare
# innermost name ("N"), so W's unrelated top-level N wrongly collided with
# X's nested M.N's OWN "N" label; round 11 encodes each label's FULL
# nesting path, so they no longer collide.
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
# W's bare top-level N.
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
  uc_fail "SANITY: a fresh compile of B against the unrelated-top-level-N W failed -- this fixture does not actually isolate an over-refusal (fresh B should succeed, since the qualified M.N can never match a top-level N)."
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
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was REFUSED reusing B.vo after W added an UNRELATED top-level Module N -- B's qualified Import M.N can never be confused with W's bare top-level N, and a fresh compile succeeds, so this is an over-refusal: a label's full nesting path, not just its innermost name, must be what the G7 shadow table compares."
fi
uc_ok "unrelated top-level Module N correctly reused despite sharing X's nested M.N's innermost name: $(echo "$c_out" | tail -1)"
