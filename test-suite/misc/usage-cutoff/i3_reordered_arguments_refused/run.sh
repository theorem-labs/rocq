#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 4, test "i3" (new,
# issuecomment-6189398514/round-5 issuecomment-6189455137: "ready to
# lift" from the reviewer's own experiment, not yet in the suite). Two
# REORDERED `Arguments` leaves for the SAME name: an unkeyed, raw-leaf
# SET check (the mechanism round 3's i1 finding replaced) cannot tell
# these two orderings apart at all -- both produce the exact same SET of
# two leaves, just reordered, so a flat-digest-of-the-set view sees no
# change. Only a digest of the EFFECTIVE, resolved value
# (`Impargs.implicits_of_global`, order-independent of which raw leaf
# came first) catches it -- same mechanism as i1, independently verified
# here since i1 only exercised an ADDED leaf, never a REORDERED pair.
#
# A declares `baz`, then `Arguments baz {x}.` followed by
# `Arguments baz x : clear implicits.` -- the net EFFECTIVE state is
# baz's argument explicit (the second command wins). B uses `baz 3`
# (explicit). A is rebuilt with the SAME TWO commands in SWAPPED order --
# the net EFFECTIVE state is now baz's argument IMPLICIT. Once G1 makes
# this kind of change reusable, a FRESH compile of B would now try to
# apply the (now nullary-explicit) `baz` to an extra explicit argument --
# Illegal application. A REUSED B.vo stays green regardless -- the
# per-name EFFECTIVE-value digest (round 3, `G1Partition.vernac_iface_entries`)
# must refuse reuse instead.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, net effective: baz explicit): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, baz 3 explicit): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the reordered-Arguments A fails.
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
  uc_fail "SANITY: a fresh compile of B against the reordered-Arguments A succeeded -- this fixture doesn't exercise a real reorder hazard."
fi

# AFTER: A's two Arguments commands for baz are reordered (net effective
# state flips from explicit to implicit). Rebuild A ONLY.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, reordered Arguments) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A's two Arguments commands for baz were reordered -- a fresh compile of B fails, so the reuse must be refused."
fi
echo "$c_out" | grep -qE 'Inconsistent assumptions over module|makes inconsistent assumptions over library' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected message -- got: $c_out"

uc_ok "reordered Arguments leaves (baz {x} then clear implicits, vs the reverse) correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
