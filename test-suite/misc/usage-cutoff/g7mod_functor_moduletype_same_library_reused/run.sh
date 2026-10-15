#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 8 (Lean round 7 review, "the functor
# pattern"). Y declares BOTH `Module Type T. Parameter x : nat. End T.`
# and `Module X. Definition x := 1. End X.` in the SAME file -- before
# round 8, these shared the bare key "x" in Y's OWN [comp_iface], and
# [iface_subset_ok]'s first-match lookup made ANY reuse of a dependent on
# Y refuse unconditionally (the masking bug firing on Y's OWN two "x"
# entries every single time, regardless of what else changed). Round 8's
# qualified-path keys ("T.x" vs "X.x") remove the within-library
# collision outright, and excluding Module Type fields entirely (mt1)
# removes it a second, independent way. A's non-colliding addition must
# reuse B.vo byte-for-byte.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/Y.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build Y.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Y.v (Module Type T + Module X, both with x): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (uses Y.X.x): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"
before_hash=$(uc_sha256 "$WORK/B.vo")

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, non-colliding g) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was refused after a non-colliding addition to A, with Y's own Module Type T and Module X both declaring 'x' in the same library -- this must not force every reuse of a Y-dependent to refuse: $c_out"
fi
after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C with a non-colliding addition to A -- B was silently recompiled rather than genuinely reused."

uc_ok "non-colliding addition (g) correctly reused unchanged (sha256 $after_hash) with Y's own same-library Module Type/Module x collision"
