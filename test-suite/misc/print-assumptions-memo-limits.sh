#!/usr/bin/env bash
# Print Assumptions reuses traversals across queries in one environment. The
# reuse must not use more stack or memory than the walk it replaces: on long
# chains, on a second query over a wide tree of long chains, and on a second
# query of a very wide inductive, it answers wherever the walk without reuse
# answers. The files are generated here, compiled with -R . P as real
# libraries are, and run with an 8 MiB stack.
#
# Chain50000, Chain72500: Definition x(k) := S x(k-1) over Axiom A, one query.
# Fan100000: that chain to 100,000, then a balanced tree of [f a b := a] over
#   x10, x20, ..., x100000, queried twice; the second query is a replay.
# IndChain31500: Inductive I(k) := c(k) : I(k-1) -> I(k) over Axiom B, one
#   query. MixChain25500: Definition e(k) := J(k-1) alternating with
#   Inductive J(k) := k(k) : e(k) -> J(k).
# Wide40000: one inductive with 40,000 constructors, queried twice, under
#   ulimit -v 2000000 (2 GB). Stock and this branch need about 0.8 GB; a
#   replay that pushes a block's shared edges once per member runs out even
#   at 4 GB.
#
# The limits depend on the build. Measured with the dev profile (what
# `make world` and CI build) and ulimit -s 8192, the walk without reuse
# answers definition chains up to about 74,650, inductive chains up to about
# 32,650 and mixed chains up to about 26,130. Each size above is below that,
# and above where a walk that holds more stack per level runs out: a non-tail
# call into the definition walk overflows from about 47,500 definitions, a
# recursive replay overflows on Fan100000's second query, and an inductive
# walk with one more frame slot overflows from about 30,750 inductives and
# 24,900 mixed links. The release profile (-O3) lowers the inductive limits
# of the walk without reuse to about 29,030 and 23,760, so this script is
# meant for dev builds.
#
# OCaml 5 ignores ulimit -s (it runs OCaml code on its own stack), so these
# limits do not apply there, and the memory cap was measured on OCaml 4 only:
# the script skips, rather than pass on files that cannot overflow.

set -e

export PATH=$BIN:$PATH

case $(rocq --version) in
  *"compiled with OCaml 4."*) ;;
  *) echo "Skipping: not built with OCaml 4, whose stack and memory limits this script is measured against."; exit 0 ;;
esac

cd misc
rm -rf print-assumptions-memo-limits/_test
mkdir -p print-assumptions-memo-limits/_test
cd print-assumptions-memo-limits/_test

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

indchain() {
  echo "Unset Elimination Schemes."
  echo "Axiom B : Type."
  echo "Inductive I0 : Type := c0 : B -> I0."
  for ((k = 1; k <= $1; k++)); do echo "Inductive I$k : Type := c$k : I$((k - 1)) -> I$k."; done
  echo "Print Assumptions I$1."
}

mixchain() {
  echo "Unset Elimination Schemes."
  echo "Axiom B : Type."
  echo "Inductive J0 : Type := k0 : B -> J0."
  for ((k = 1; k <= $1; k++)); do
    echo "Definition e$k := J$((k - 1))."
    echo "Inductive J$k : Type := k$k : e$k -> J$k."
  done
  echo "Print Assumptions J$1."
}

wide() {
  echo "Unset Elimination Schemes."
  echo "Inductive wide : Set :="
  for ((k = 0; k < $1; k++)); do echo "| C$k : wide"; done
  echo "."
  echo "Print Assumptions wide."
  echo "Print Assumptions wide."
}

{ chain 50000; echo "Print Assumptions x50000."; } > Chain50000.v
{ chain 72500; echo "Print Assumptions x72500."; } > Chain72500.v
leaves=()
for ((k = 10; k <= 100000; k += 10)); do leaves+=("x$k"); done
{ chain 100000; printf 'Definition R := '; tree "${leaves[@]}"; echo "."
  echo "Print Assumptions R."; echo "Print Assumptions R."; } > Fan100000.v
indchain 31500 > IndChain31500.v
mixchain 25500 > MixChain25500.v
wide 40000 > Wide40000.v

axiom_a='Axioms:
A : nat'
axiom_b='Axioms:
B : Type'
closed='Closed under the global context'

status=0
for f in Chain50000 Chain72500 Fan100000 IndChain31500 MixChain25500 Wide40000; do
  out=$(ulimit -s 8192; ulimit -v 2000000; rocq c -q -R . P "$f.v" 2>&1) || true
  case $f in
    Fan100000) want="$axiom_a
$axiom_a" ;;
    IndChain*|MixChain*) want=$axiom_b ;;
    Wide*) want="$closed
$closed" ;;
    *) want=$axiom_a ;;
  esac
  if [ "$out" != "$want" ]; then
    echo "$f: unexpected output:"
    echo "$out"
    status=1
  fi
done
exit $status
