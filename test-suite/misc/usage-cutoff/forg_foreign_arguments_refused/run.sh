#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 5, test "forg" (new,
# issuecomment-6189455137). A `#[global] Arguments` override issued in A
# but targeting a FOREIGN declaration A does not itself own
# (`Nat.pred`, from the prelude/stdlib) -- round 3's `vernac_iface`
# mechanism only re-covers names that ALSO have a keyed CONSTANT/
# INDUCTIVE classifier object actually present IN A's own object tree
# (`G1Partition.vernac_iface_entries`'s walk only ever visits
# declaration objects A itself declares), so a foreign-target
# IMPLICITS/ARGUMENTS-SCOPE object, EXCLUDED from the exact digest by
# `classify`'s bare `object_name` match, was dropped from EVERY digest
# with nothing picking up the slack.
#
# A declares only an unrelated definition, then (AFTER) adds
# `#[global] Arguments Nat.pred {n}.`, overriding a declaration it does
# not own at all. B does `Require Import A.` and uses `Nat.pred 3` (the
# argument explicit, matching Nat.pred's ORIGINAL signature before any
# override). Once G1 makes A's unrelated-looking addition reusable, a
# FRESH compile of B would now try to apply the (now nullary-explicit)
# `Nat.pred` to an extra explicit argument -- Illegal application. A
# REUSED B.vo stays green regardless -- the `G1Partition.classify`/
# `modpath_of_gr`/`is_local` fix (round 5: inspect the raw object's own
# target `GlobRef.t` directly via `Impargs.cutoff_implicits_targets`, and
# keep it in the EXACT digest whenever any target is foreign to the
# declaring library) must refuse reuse instead.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, Nat.pred 3 with explicit arg): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the Arguments-overridden A fails.
cp "$D/A_after.v" "$WORK/A_fresh.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh.v ) >"$WORK/fresh-a.log" 2>&1 \
  || uc_fail "SETUP: A_after.v failed to compile standalone: $(cat "$WORK/fresh-a.log")"
cp "$D/B.v" "$WORK/B_fresh.v"
sed -i 's/Require Import A\./Require Import A_fresh./' "$WORK/B_fresh.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh.v 2>&1)
fresh_rc=$?
rm -f "$WORK"/A_fresh.* "$WORK"/B_fresh.*
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the foreign Arguments override succeeded -- this fixture doesn't exercise a real override hazard."
fi

# AFTER: A gains a foreign #[global] Arguments override. Rebuild A ONLY.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, foreign Arguments Nat.pred {n}) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added a foreign Arguments override on Nat.pred -- a fresh compile of B fails, so the reuse must be refused."
fi
echo "$c_out" | grep -qE 'Inconsistent assumptions over module|makes inconsistent assumptions over library' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected message -- got: $c_out"

uc_ok "foreign Arguments override (Nat.pred {n}, issued in A but not owned by A) correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
