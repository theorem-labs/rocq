#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 8 (Lean round 8 review,
# issuecomment-6192580006, fixture "mtc6"). Same cause as mtc1
# (kernel/safe_typing.ml:2153 at head 1e4242077b excluded `SFBmodtype` from
# `comp_iface` entirely), exercised through an `Axiom` change (not a
# `Parameter`'s type): T's `Axiom ax : x = 1` becomes `ax : x = 2`, with
# `x : nat` held fixed. B's functor proves `pf : P.x = 1 := P.ax`; once
# P.ax's type becomes `P.x = 2`, a fresh compile fails, but the stale
# B.vo was wrongly REUSED.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, Module Type T with ax : x = 1): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (functor G (P : T) proving pf : P.x = 1): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, ax : x = 1 -> ax : x = 2) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C compiled against the stale B.vo after T's axiom ax changed from 'x = 1' to 'x = 2' -- B's 'Definition pf : P.x = 1 := P.ax.' no longer typechecks against a fresh T."
fi
uc_ok "C was refused against the stale B.vo: $(echo "$out" | tail -1)"

build B.v >"$WORK/freshB.log" 2>&1
if [ $? -eq 0 ]; then
  uc_fail "B.v compiled fresh against the new T (ax : x = 2) -- expected a type mismatch on P.ax: $(cat "$WORK/freshB.log")"
fi
uc_assert_contains "$WORK/freshB.log" "P.ax" \
  "fresh B.v compile against the new T did not fail with the expected P.ax type-mismatch error"
uc_ok "fresh B.v compile against the new T correctly fails"
