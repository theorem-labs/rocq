#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mkc1", P3). A new precision defect
# INTRODUCED by round 9's own P1-adjacent marking scheme: a Module Type's
# FIELDS are basename-marked uncollidable with a REAL identifier
# (`modtype_entry_marker`), but two DIFFERENT, unrelated module types that
# happen to name a field the same (here "x") reduce to the SAME marked
# basename ("0usage_cutoff_modtype_x") -- which the G7 shadow table then
# treats as one shadowing the other, even though neither dependent ever
# resolves a bare "x" to either module type's abstract field.
#
# X declares `Module Type T. Parameter x : nat.` and an UNRELATED
# `Definition g`. W (before) has nothing module-type-shaped. A does
# `Require Export W.` B uses ONLY `g`, never touching T, U, or any module
# type at all. W is then rebuilt to add `Module Type U. Parameter x : nat.`
# -- an UNRELATED module type, reached only transitively through A's
# `Require Export`, whose field happens to share the name "x" with T's.
# Since neither T nor U nor their field "x" is ever referenced by B, a
# fresh compile of B still succeeds unchanged. The marked-basename
# collision must not cause a reuse refusal here.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE, no module types): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses only g): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER state (W adds the
# colliding Module Type U) really does succeed -- B never touches T/U.
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
  uc_fail "SANITY: a fresh compile of B against the field-marker-colliding W failed -- this fixture does not actually isolate an over-refusal (fresh B should succeed, since B never touches T or U)."
fi
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly so the main test starts from the same
# baseline B.vo/C.vo built above.
cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W0.v: $(cat "$WORK/restore.log")"

# AFTER: W grows the unrelated, field-colliding Module Type U, re-exported
# unchanged through A. Rebuild W and A ONLY -- B.vo (and C.vo) are left
# stale.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds unrelated Module Type U) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was REFUSED reusing B.vo after W added an UNRELATED Module Type U whose field happens to share T's field name 'x' -- B never touches T, U, or 'x' at all, and a fresh compile succeeds, so this is an over-refusal: marked basenames from DIFFERENT module types must not collide with each other in the G7 shadow table."
fi
uc_ok "unrelated field-name-colliding Module Type U correctly reused: $(echo "$c_out" | tail -1)"
