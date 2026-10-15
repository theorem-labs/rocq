#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 5, test "ind1" (new,
# issuecomment-6189455137). The round-5 reviewer's own repro: an
# `Arguments` override on a CONSTRUCTOR. Round 3's `vernac_iface`
# mechanism only covered CONSTANT's own classifier; INDUCTIVE (types and
# constructors) stayed wholesale EXCLUDED from the exact digest with no
# keyed coverage either, so an override on a constructor's own implicit
# status was invisible to every reuse check.
#
# A declares `Inductive t := C (x : nat).`. B does `Require Import A.`
# and uses `C 3` (both args explicit, matching A's original signature).
# A is rebuilt to ADD `Arguments C {x}.` (x becomes implicit) -- a
# genuine, allowed-by-G1 addition in the sense that nothing B directly
# referenced about A's declaration CHANGED VALUE. Once G1 makes this kind
# of override reusable, a FRESH compile of B would now have `C 3` try to
# apply the (now nullary-explicit) constructor to an extra explicit
# argument -- Illegal application. A REUSED B.vo stays green regardless
# (its own absolute kernel reference to C is unaffected), silently
# diverging from what a fresh compile would now do -- the Declaremods
# `G1Partition`/`DeclareInd` INDUCTIVE classifier fix (keying one entry
# per `IndRef`/`ConstructRef` target, round 5) must refuse reuse instead.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, C 3 both explicit): $(cat "$WORK/setup.log")"
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
  uc_fail "SANITY: a fresh compile of B against the Arguments-overridden A succeeded -- this fixture doesn't exercise a real override hazard."
fi

# AFTER: A's constructor C gains the Arguments override. Rebuild A ONLY.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, Arguments C {x}) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A overrode constructor C's Arguments -- a fresh compile of B fails, so the reuse must be refused."
fi
echo "$c_out" | grep -qE 'Inconsistent assumptions over module|makes inconsistent assumptions over library' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected message -- got: $c_out"

uc_ok "constructor Arguments override (C {x}) correctly refused reuse: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
