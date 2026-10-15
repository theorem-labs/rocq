#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "unused_addition_still_reused"
# (issue list item 12 of 15, the POSITIVE control). Depends on: D3 (the
# shared dep_ok predicate) / D4 (the exported-object digest). Should PASS
# once those land -- and, crucially, this is the test that stops a design
# which closes every soundness hole by refusing ALL reuse from passing the
# whole suite vacuously: adding a declaration nothing depends on MUST still
# skip recompiling existing dependents, or the entire feature has no point.
#
# A gains an unused helper lemma (A rebuilt); B (which only ever used `a`,
# never anything from `helper`) and C must still go through using the OLD
# B.vo, completely untouched -- not merely "C still compiles" (which a
# silent full rebuild would also satisfy), but B.vo's bytes on disk must
# be bit-for-bit unchanged after C is compiled.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_ref.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"

before_hash=$(uc_sha256 "$WORK/B.vo")

# AFTER: an unused helper lemma is added to A. Rebuild A ONLY.
cp "$D/A_helper.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, unused helper added) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if ! out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C was refused after an UNUSED declaration was added to A -- over-conservative, defeats the entire point of the cutoff (false negative on reuse)."
fi

after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C -- B was silently recompiled rather than genuinely reused."

uc_ok "C compiled using B.vo unchanged (sha256 $after_hash) after an unused addition to A: $(echo "$out" | tail -1)"
