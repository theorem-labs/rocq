#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 6 review (issuecomment-6191273575),
# "plog". g7mod is reachable with NO nested Module anywhere in the
# dependent's own tree: the always-loaded prelude itself does the work.
# `Corelib.Init.Logic` declares `Module EqNotations` alongside its own
# flat `eq_sym`/`eq_trans`/etc.; before round 7's recursive
# `iface_entries_of_sfb` fix, that one nested module forced Logic's
# WHOLE `iface_table` to `None`, hiding `eq_sym` from the G7 closure
# table. B references the prelude's `eq_sym` unqualified (implicitly
# open); A is rebuilt to ADD its OWN `Definition eq_sym := 0.`, which
# shadows the prelude's in a fresh compile (last `Require Import` wins
# for an unqualified name).
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, eq_sym resolves to the prelude's): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the shadowing A really does fail.
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

# AFTER: A grows eq_sym, colliding with the prelude's own eq_sym that B's
# closure resolved. Rebuild A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding eq_sym) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added eq_sym, colliding with the prelude's own eq_sym -- a fresh compile of B against the same new A fails (confirmed above), so this reuse is wrong."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "colliding addition (eq_sym) correctly refused ($(echo "$c_out" | grep -m1 'Inconsistent assumptions'))"
