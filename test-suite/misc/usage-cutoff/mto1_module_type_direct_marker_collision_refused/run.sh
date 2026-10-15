#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mto1"). CONTROL for mkc1: the SAME
# field-name-colliding Module Type U (`Parameter x : nat`, matching X's
# Module Type T) added DIRECTLY to A's own source, instead of reached
# transitively through a dependency's `Require Export`. A fresh compile of
# B still succeeds (B never touches T, U, or "x"), but the reuse is -- and
# must remain -- REFUSED: this goes through A's own exact objects digest
# (a new ModuleObject in A's own library_objects), unrelated to the P3
# marker-collision bug mkc1 exercises and unaffected by its fix. A correct,
# by-design, conservative over-refusal (D4's whole-table exact-equality
# vernac-objects digest is not usage-based, per the repo's own "m3" note),
# not a bug: it demonstrates P3 is specifically about the G7 shadow table
# conflating two DIFFERENT libraries' marked entries, not a general defect
# in how directly-added module types are handled.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses only g): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER state (A directly adds the
# colliding Module Type U) really does succeed -- B never touches T/U.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/sanity-rebuild.log" 2>&1 \
  || uc_fail "SETUP: could not rebuild A.v (AFTER) for the sanity check: $(cat "$WORK/sanity-rebuild.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -ne 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against A's direct Module Type U addition failed -- expected to succeed (B never touches T or U)."
fi
rm -f "$WORK"/B_fresh_check.*

# Restore the BEFORE state, rebuild B/C against it (same baseline as the
# sanity check started from), then redo the direct addition for the main
# reuse check against the stale B.vo/C.vo.
cp "$D/A_before.v" "$WORK/A.v"
build A.v >"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild A.v (BEFORE): $(cat "$WORK/restore.log")"
build B.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild B.v (BEFORE): $(cat "$WORK/restore.log")"
build C.v >>"$WORK/restore.log" 2>&1 || uc_fail "RESTORE: could not rebuild C.v (BEFORE): $(cat "$WORK/restore.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, direct Module Type U addition) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A directly added the field-colliding Module Type U -- expected a (correct, by-design) refusal via A's own exact objects digest, independent of the P3 fix."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "direct Module Type U addition in A correctly refused reuse via A's own digest, though a fresh B still succeeds (correct, by-design over-refusal; control, unaffected by the P3 fix): $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
