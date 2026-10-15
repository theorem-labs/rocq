#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 8 (Lean round 8 review,
# issuecomment-6192580006, fixture "mtc1"). `iface_entries_of_sfb` returned
# `[]` for `SFBmodtype` (kernel/safe_typing.ml:2153 at head 1e4242077b), so
# a Module Type's own fields never entered `comp_iface` at all -- a changed
# signature was invisible to `iface_subset_ok`, and a stale B that sealed a
# module against the old T was wrongly REUSED even though a fresh compile
# of B against the new T fails ("Signature components for field x do not
# match"). Fixed by recursing into `SFBmodtype` exactly like `SFBmodule`
# (so its fields enter `comp_iface`), with every such entry's own basename
# marked via `modtype_entry_marker`/`mark_basename` so it still never
# enters the G7 shadow table (`flatten_closure`).
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, Module Type T with x : nat): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (seals M : T): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# AFTER: T's field x changes from nat to bool. Rebuild A ONLY -- B.vo is
# left stale on disk.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, x : nat -> x : bool) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# The exploit: compile C fresh against the stale B.vo (B.v/B.vo untouched
# since the BEFORE build).
if out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C compiled against the stale B.vo after T's field x changed from nat to bool -- B seals a module against T with 'Definition x := 1', which no longer matches a fresh T."
fi
uc_ok "C was refused against the stale B.vo: $(echo "$out" | tail -1)"

# Confirm the counterfactual: a FRESH compile of the unchanged B.v against
# the new A must actually fail (not merely "the loader is conservative").
build B.v >"$WORK/freshB.log" 2>&1
if [ $? -eq 0 ]; then
  uc_fail "B.v compiled fresh against the new T (x : bool) -- expected a signature mismatch, since M seals 'Definition x := 1' against bool: $(cat "$WORK/freshB.log")"
fi
uc_assert_contains "$WORK/freshB.log" "Signature components" \
  "fresh B.v compile against the new T did not fail with the expected signature-mismatch error"
uc_ok "fresh B.v compile against the new T correctly fails"
