#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 6 review (issuecomment-6191273575),
# "or1"/"or2" (new precision defect P2). `check_required`'s live closure
# table used to be built from the WHOLE `current_libs` of the CONSUMING
# process, not from B's own recorded closure: an entirely UNRELATED
# library (Z) sharing a bare id with something in B's closure (X's `f`)
# wrongly poisoned every reuse of B, and ONLY if Z happened to be loaded
# before B in the SAME process -- the exact same B.vo was refused or
# reused purely depending on an unrelated `Require` order the consuming
# file chose. Round 7 scopes the live comparison to exactly the
# `DirPath.t`s B's own recorded closure named (see
# `Safe_typing.check_required`'s doc comment). A's rebuild adds `h`, an
# UNRELATED, non-colliding addition -- reuse must succeed, and must
# succeed the SAME way regardless of whether the consumer requires Z
# before or after B.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/Z.v "$D"/B.v "$D"/C1.v "$D"/C2.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build Z.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Z.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (AFTER, non-colliding h) standalone: $(cat "$WORK/setup.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -ne 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the non-colliding A (adds h) failed -- this fixture does not actually exercise an ordinary allowed addition: $fresh_out"
fi
rm -f "$WORK"/B_fresh_check.*

# A is back to BEFORE on disk; rebuild A (AFTER) only, leave B.vo stale,
# then check both consumer orders.
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"
before_hash=$(uc_sha256 "$WORK/B.vo")

c1_out=$(build C1.v 2>&1)
c1_rc=$?
if [ "$c1_rc" -ne 0 ]; then
  echo "$c1_out" >&2
  uc_fail "or1: coqc C1.v (Require Import Z. Require Import B.) was refused, even though A's addition (h) does not collide with anything B's closure resolved -- Z is unrelated to B and must not affect this reuse decision: $c1_out"
fi
after1_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after1_hash" "$before_hash" \
  "or1: B.vo's bytes changed after compiling C1 -- B was silently recompiled rather than genuinely reused."

c2_out=$(build C2.v 2>&1)
c2_rc=$?
if [ "$c2_rc" -ne 0 ]; then
  echo "$c2_out" >&2
  uc_fail "or2: coqc C2.v (Require Import B. Require Import Z.) was refused -- same scenario as or1 with Z and B swapped; the reuse decision must not depend on require order: $c2_out"
fi
after2_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after2_hash" "$before_hash" \
  "or2: B.vo's bytes changed after compiling C2 -- B was silently recompiled rather than genuinely reused."

uc_ok "non-colliding addition (h) reused identically (sha256 $after1_hash) regardless of Z/B require order (or1 and or2 both pass)"
