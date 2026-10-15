#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 8 (Lean round 8 review,
# issuecomment-6192580006, fixture "mtc5"). Same cause as mtc1
# (kernel/safe_typing.ml:2153 at head 1e4242077b excluded `SFBmodtype` from
# `comp_iface` entirely), exercised through `Include T` instead of a seal.
# When T's field x changes from nat to bool, a fresh compile of B fails
# (X.x : bool used where nat is expected), but the stale B.vo was wrongly
# REUSED.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, Module Type T with x : nat): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (Module X. Include T. End X.): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, x : nat -> x : bool) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C compiled against the stale B.vo after T's field x changed from nat to bool -- B's 'Module X. Include T. End X. Definition b : nat := X.x.' no longer typechecks against a fresh T."
fi
uc_ok "C was refused against the stale B.vo: $(echo "$out" | tail -1)"

build B.v >"$WORK/freshB.log" 2>&1
if [ $? -eq 0 ]; then
  uc_fail "B.v compiled fresh against the new T (x : bool) -- expected a type mismatch on X.x: $(cat "$WORK/freshB.log")"
fi
uc_assert_contains "$WORK/freshB.log" "X.x" \
  "fresh B.v compile against the new T did not fail with the expected X.x type-mismatch error"
uc_ok "fresh B.v compile against the new T correctly fails"
