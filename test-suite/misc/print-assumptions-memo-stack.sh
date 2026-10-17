#!/usr/bin/env bash
# Print Assumptions reuses traversals across queries in one environment. The
# reuse must not use more stack than the walk it replaces: on long chains of
# definitions and on a second query over a wide tree of long chains, it answers
# wherever the walk without reuse answers. The files are generated here; the
# stack is fixed at 8 MiB so the limits below do not depend on the machine.
#
# chain N: Definition x(k) := S x(k-1), N times, over Axiom A, and one query.
# fan N:   the same chain with N = 100000, then a balanced tree of
#          [f a b := a] over x10, x20, ..., x100000, queried twice.

set -e

export PATH=$BIN:$PATH

cd misc
rm -rf print-assumptions-memo-stack/_test
mkdir -p print-assumptions-memo-stack/_test
cd print-assumptions-memo-stack/_test

chain() {
  echo "Axiom A : nat."
  echo "Definition x0 := A."
  echo "Definition f (a b : nat) := a."
  for ((k = 1; k <= $1; k++)); do echo "Definition x$k := S x$((k - 1))."; done
}

tree() {
  # balanced tree of f over the given leaves
  if [ "$#" -eq 1 ]; then printf '%s' "$1"; return; fi
  local half=$(($# / 2))
  printf '(f '
  tree "${@:1:half}"
  printf ' '
  tree "${@:half+1}"
  printf ')'
}

{ chain 50000; echo "Print Assumptions x50000."; } > Chain50000.v
{ chain 72500; echo "Print Assumptions x72500."; } > Chain72500.v
leaves=()
for ((k = 10; k <= 100000; k += 10)); do leaves+=("x$k"); done
{ chain 100000; printf 'Definition R := '; tree "${leaves[@]}"; echo "."
  echo "Print Assumptions R."; echo "Print Assumptions R."; } > Fan100000.v

expected_one='Axioms:
A : nat'

for f in Chain50000 Chain72500 Fan100000; do
  out=$(ulimit -s 8192; rocq c -q "$f.v" 2>&1)
  case $f in
    Fan100000) want="$expected_one
$expected_one" ;;
    *) want=$expected_one ;;
  esac
  if [ "$out" != "$want" ]; then
    echo "$f: unexpected output:"
    echo "$out"
    exit 1
  fi
done
