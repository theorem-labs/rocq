#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 10 (Lean round 10 review,
# issuecomment-6198625773, fixture "lc1", P3). X declares `Module foo.
# Definition f := 1. End foo.`. B does `Import foo.` and uses `f`,
# resolving unambiguously to X's module foo. W is then rebuilt to add an
# UNRELATED top-level `Definition foo := 99.` -- a CONSTANT, not a module,
# reachable only transitively through A's `Require Export`. Rocq resolves
# module names and term names through entirely SEPARATE Nametab tables, so
# `Import foo.` (which only ever looks up a MODULE) can never be confused
# with a same-named constant: a fresh compile of B is unaffected and still
# succeeds. Before round 11's fix, the module label entry X's `Module foo`
# produced shared the SAME bare-basename shadow space ordinary constants
# use, so W's unrelated `Definition foo` wrongly collided with it; round
# 11 puts module/module-type labels in their own, constant-disjoint
# namespace.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE, no foo): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, Import foo resolves to X.foo): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER state (W adds an unrelated
# CONSTANT foo) still succeeds -- Import foo only ever looks up a module.
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
  uc_fail "SANITY: a fresh compile of B against the unrelated-constant-foo W failed -- this fixture does not actually isolate an over-refusal (fresh B should succeed: Import foo resolves through the module Nametab, never the term one)."
fi
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly so the main test starts from the same
# baseline B.vo/C.vo built above.
cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W0.v: $(cat "$WORK/restore.log")"

# AFTER: W grows an unrelated CONSTANT foo, re-exported unchanged through
# A. Rebuild W and A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds an unrelated constant foo) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was REFUSED reusing B.vo after W added an UNRELATED constant foo -- modules and terms are separate Nametab namespaces, B's Import foo can never be confused with a term, and a fresh compile succeeds, so this is an over-refusal: a module's label must not share a shadow namespace with constants."
fi
uc_same_interface "$WORK" "lc1_module_label_vs_constant_reused"
uc_ok "unrelated constant foo correctly reused despite sharing X's Module foo's name: $(echo "$c_out" | tail -1)"
