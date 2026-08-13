#!/bin/sh
set -eu

test_dir=misc/proof-assumptions
actual="$test_dir/actual.json"
missing="$test_dir/missing.json"

rm -f "$actual" "$missing"

$coqc -Q "$test_dir" ProofAssumptions "$test_dir/input.v"

"$BIN/rocqchk" -silent \
  -Q "$test_dir" ProofAssumptions \
  -norec ProofAssumptions.input \
  --proof-assumptions ProofAssumptions.input.through_sealed \
  --proof-assumptions ProofAssumptions.input.through_transparent \
  --proof-assumptions ProofAssumptions.input.closed \
  --proof-assumptions ProofAssumptions.input.transparent_witness \
  --proof-assumptions ProofAssumptions.input.witness \
  --proof-assumptions ProofAssumptions.input.uses_wrapper \
  --proof-assumptions-output "$actual"

diff -u "$test_dir/expected.json" "$actual"
rm "$actual"

if "$BIN/rocqchk" -silent \
  -Q "$test_dir" ProofAssumptions \
  -norec ProofAssumptions.input \
  --proof-assumptions ProofAssumptions.input.does_not_exist \
  --proof-assumptions-output "$missing" \
  >/dev/null 2>&1
then
  echo "rocqchk accepted a missing proof-assumptions target" >&2
  exit 1
fi

test ! -e "$missing"
