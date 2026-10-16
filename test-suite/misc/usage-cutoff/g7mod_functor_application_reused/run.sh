#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 7. X applies a functor (`Module M :=
# F Arg.`) -- the APPLICATION's own expanded signature is a concrete,
# non-functor structure (the kernel resolves `F Arg` fully at
# type-checking time), so it must still be fully enumerable by
# [Safe_typing.iface_entries_of_sfb]'s recursive walk, NOT fall back to
# a whole-library [None]. Control: a non-colliding addition to A must
# still reuse B.vo byte-for-byte even though X's own structure contains
# a functor declaration (`Module F (Y : S). ... End F.`, never itself
# dereferenced) alongside the application.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v (functor + application): $(cat "$WORK/setup.log")"
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
  uc_fail "coqc C.v was refused after a non-colliding addition to A, with a functor application in X's closure -- functor-bearing libraries must not force the whole-library exact-match fallback: $c_out"
fi
after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C with a non-colliding addition to A -- B was silently recompiled rather than genuinely reused."

uc_same_interface "$WORK" "g7mod_functor_application_reused"
uc_ok "non-colliding addition (g) correctly reused unchanged (sha256 $after_hash) with a functor application in X's closure"
