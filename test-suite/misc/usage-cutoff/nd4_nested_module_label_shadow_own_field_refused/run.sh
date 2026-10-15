#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 10 (Lean round 10 review,
# issuecomment-6198625773, fixture "nd4"). Same shape as nd1 (a TRUE shadow
# at nesting depth 2, kept refused), but W's colliding nested M.N ALSO
# redefines B's actually-used field `f` (not just an unrelated `zzq`) --
# confirms the refusal holds even when the colliding field itself is the
# one the dependent uses, reinforced by (not merely coincident with) the
# label-level collision.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE, no module M): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, Import M.N resolves to X.M.N): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing W really does
# fail -- W's nested M.N redefines f itself, so B's eq_refl no longer
# type-checks.
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
  uc_fail "SANITY: a fresh compile of B against the field-redefining nested-module-shadowing W succeeded -- this fixture does not actually exercise a real shadowing hazard."
fi
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state exactly so the main test starts from the same
# baseline B.vo/C.vo built above.
cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild W.v (BEFORE): $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v against W0.v: $(cat "$WORK/restore.log")"

# AFTER: W grows a second, identically-nested M.N that ALSO redefines f,
# re-exported unchanged through A. Rebuild W and A ONLY -- B.vo (and C.vo)
# are left stale.
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds a same-depth-nested Module M.N redefining f) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after W added an identically-nested Module M.N redefining f -- this is a TRUE shadow and must stay refused."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "same-depth nested Module M.N shadow (redefining the used field) correctly stays refused: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
