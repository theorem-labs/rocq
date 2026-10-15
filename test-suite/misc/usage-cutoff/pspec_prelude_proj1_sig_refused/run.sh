#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 6 review (issuecomment-6191273575),
# "pspec". Same shape as `plog_prelude_eq_sym_refused`, against
# `Corelib.Init.Specif`'s `Module SigTNotations` instead of
# `Corelib.Init.Logic`'s `Module EqNotations` -- confirms round 7's
# recursive `iface_entries_of_sfb` fix is not specific to one prelude
# file. B references the prelude's `proj1_sig` unqualified; A is
# rebuilt to ADD its own `Definition proj1_sig := 0.`.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, proj1_sig resolves to the prelude's): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/B.v" "$WORK/B_fresh_check.v"
sed -i 's/Require Import A\./Require Import A_after./' "$WORK/B_fresh_check.v"
cp "$D/A_after.v" "$WORK/A_after.v"
( cd "$WORK" && uc_coqc -Q . "" A_after.v ) >"$WORK/shadow-check.log" 2>&1 \
  || uc_fail "SETUP: could not build A_after.v as A_after for the fresh-shadow sanity check: $(cat "$WORK/shadow-check.log")"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the shadowing A succeeded -- this fixture does not actually exercise a name-shadowing hazard, nothing to test."
fi
rm -f "$WORK"/B_fresh_check.* "$WORK"/A_after.*

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding proj1_sig) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added proj1_sig, colliding with the prelude's own proj1_sig -- a fresh compile of B against the same new A fails (confirmed above), so this reuse is wrong."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "colliding addition (proj1_sig) correctly refused ($(echo "$c_out" | grep -m1 'Inconsistent assumptions'))"
