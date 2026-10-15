#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 8 (Lean round 8 review,
# issuecomment-6192580006, fixture "mtn1"). Same cause as mtc1
# (kernel/safe_typing.ml:2153 at head 1e4242077b excluded `SFBmodtype` from
# `comp_iface` entirely), exercised with T NESTED inside a Module M, not
# top-level -- confirms the fix's recursion into `SFBmodtype` reaches a
# nested Module Type too, qualified as `M.T`. When T's field x changes
# from nat to bool, a fresh compile of B (`Module X : M.T. Definition x
# := 1. End X.`) fails, but the stale B.vo was wrongly REUSED.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, Module M containing Module Type T with x : nat): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (seals X : M.T): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, M.T's x : nat -> x : bool) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C compiled against the stale B.vo after the NESTED M.T's field x changed from nat to bool -- B seals X against M.T with 'Definition x := 1', which no longer matches a fresh M.T."
fi
uc_ok "C was refused against the stale B.vo: $(echo "$out" | tail -1)"

build B.v >"$WORK/freshB.log" 2>&1
if [ $? -eq 0 ]; then
  uc_fail "B.v compiled fresh against the new M.T (x : bool) -- expected a signature mismatch: $(cat "$WORK/freshB.log")"
fi
uc_assert_contains "$WORK/freshB.log" "Signature components" \
  "fresh B.v compile against the new M.T did not fail with the expected signature-mismatch error"
uc_ok "fresh B.v compile against the new M.T correctly fails"
