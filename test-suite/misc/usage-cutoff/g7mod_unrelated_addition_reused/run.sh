#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 7. Positive control for
# `g7mod_nested_module_refused`: G7's recursive module walk must not
# OVER-trigger. X has the SAME nested `Module Internal` as the sibling
# fixture, but A's rebuild adds a NON-colliding name (`g`, never seen
# anywhere in B's closure) instead of a colliding one (`f`). B.vo must
# still be reused byte-for-byte.
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
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"
before_hash=$(uc_sha256 "$WORK/B.vo")

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds non-colliding g) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was refused after A added a NON-colliding declaration (g) in the closure of a library (X) with an unrelated nested Module -- G7's module walk is over-triggering: $c_out"
fi
after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C with a non-colliding addition to A -- B was silently recompiled rather than genuinely reused."

uc_same_interface "$WORK" "g7mod_unrelated_addition_reused"
uc_ok "non-colliding addition (g) correctly reused unchanged (sha256 $after_hash) despite X's unrelated nested Module"
