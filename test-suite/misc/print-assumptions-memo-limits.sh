#!/usr/bin/env bash
# Print Assumptions reuses traversals across queries in one environment. The
# reuse must not cost more time, stack or memory than the walk it replaces.
# The files are generated here and compiled with -R . P, as real libraries
# are.
#
# Time: one user name reached under two canonical names. A chain of 8,000
# definitions over an object of a module alias is queried alternately with a
# constant whose implementation, read through a sealed functor application,
# reaches the same user name under the other canonical name.
# - Flip8000: c(k) := S c(k-1) over M2.bar with M2 := M, queried with P2.bar
#   for P2 := N M2.
# - AliasChain8000: y(k) := S y(k-1) over MA.c with MA := M, queried with
#   z := Q.c for Q := F MA.
# - BlockChain8000: the same with an inductive in place of the constant:
#   z(k) := S z(k-1) over a match on MA.c0, queried with Q.d, whose
#   implementation matches on X.c0.
# Compiling each file must take at most three times the CPU time of compiling
# it without its queries, plus one second; the walk without reuse takes about
# as long either way. A cache that replaces the entry recorded under one
# canonical name by one under the other, for a constant or for the members of
# an inductive block, makes every later replay of the chain go down to that
# name and miss, at each level: about ten times as long here. Measuring both
# compilations in the same run makes the check independent of the machine's
# speed.
#
# Stack and memory, with an 8 MiB stack (ulimit -s 8192) and 2 GB of address
# space (ulimit -v 2000000):
# - Chain50000, Chain72500: Definition x(k) := S x(k-1) over Axiom A.
# - Fan100000: that chain to 100,000, then a balanced tree of [f a b := a]
#   over x10, x20, ..., x100000, queried twice; the second query is a replay.
# - IndChain28000: Inductive I(k) := c(k) : I(k-1) -> I(k) over Axiom B.
# - MixChain23000: Definition e(k) := J(k-1) alternating with
#   Inductive J(k) := k(k) : e(k) -> J(k).
# - Wide40000: one inductive with 40,000 constructors, queried twice. The
#   walk without reuse needs about 0.8 GB of address space; a replay that
#   pushes a block's shared edges once per member runs out even at 4 GB.
# Every size answers without reuse on the dev profile (what `make world` and
# CI build) and on the release profile (-O3, as `dune build -p` builds),
# whose larger frames lower the inductive limits to about 29,000 inductives
# and 23,750 mixed links. The definition chains catch a non-tail call into
# the walk, which overflows from about 47,500 definitions on the dev profile,
# and Fan100000's second query a recursive replay. A walk frame one slot
# larger than without reuse shortens the inductive limits on the dev profile
# to about 30,750 and 24,900 only, which a size that answers on the release
# profile cannot catch: frame sizes are checked on the object code (objdump),
# not by this script.
#
# Memory kept between queries, with an 8 MiB stack and 1,000,000 KiB of
# address space (ulimit -v 1000000):
# - Retain64: 64 groups of 100 definitions with one 1,000-argument body
#   F b0 ... b999, each group under a root G(g); G0 ... G63 are queried in
#   turn, so the queries share only F and the b's.
# - BlockRetain64: the same with groups of 100 inductives whose constructors
#   take that body.
# The walk without reuse drops each query's data before the next; the reuse
# keeps entries, and clears them when they weigh more than twice the
# heaviest query. Measured on the dev and the release profile, both files
# need 720 to 790 MiB of address space without reuse, 790 to 880 MiB with the
# bounded reuse, and 1,240 to 1,280 MiB with a cache that keeps every entry
# until the environment changes, which runs out here.
#
# OCaml 5 ignores ulimit -s (it runs OCaml code on its own stack), and the
# memory caps were measured on OCaml 4 only: the stack and memory cases are
# skipped there, rather than pass on files that cannot overflow.

set -e

export PATH=$BIN:$PATH
export LC_ALL=C

case $(rocq --version) in
  *"compiled with OCaml 4."*) ocaml4=true ;;
  *) ocaml4=false ;;
esac

cd misc
rm -rf print-assumptions-memo-limits/_test
mkdir -p print-assumptions-memo-limits/_test
cd print-assumptions-memo-limits/_test

status=0

# Prints the output of $2 when it differs from $3, and fails.
expect() {
  if [ "$2" != "$3" ]; then
    echo "$1: unexpected output:"
    echo "$2"
    status=1
  fi
}

flip() {
  echo "Axiom foo : nat."
  echo "Module Type T. Parameter bar : nat. End T."
  echo "Module M : T. Module Hide. Definition x := foo. End Hide. Definition bar := Hide.x. End M."
  echo "Module M2 := M."
  echo "Module N (X : T) : T. Definition y := X.bar. Definition bar := y. End N."
  echo "Module P2 := N M2."
  echo "Definition c0 := M2.bar."
  for ((k = 1; k <= $1; k++)); do echo "Definition c$k := S c$((k - 1))."; done
  for _ in 1 2; do echo "Print Assumptions c$1."; echo "Print Assumptions P2.bar."; done
}

aliaschain() {
  echo "Axiom ax : nat."
  echo "Module Type T. Parameter c : nat. End T."
  echo "Module M : T. Definition c := ax. End M."
  echo "Module MA := M."
  echo "Module F (X : T) : T. Definition c := X.c. End F."
  echo "Module Q := F MA."
  echo "Definition y0 := MA.c."
  for ((k = 1; k <= $1; k++)); do echo "Definition y$k := S y$((k - 1))."; done
  echo "Definition z := Q.c."
  for _ in 1 2; do echo "Print Assumptions y$1."; echo "Print Assumptions z."; done
}

blockchain() {
  echo "Axiom ax : nat."
  echo "Module Type T. Inductive I := c0 : nat -> I. End T."
  echo "Module M : T. Inductive I := c0 : nat -> I. End M."
  echo "Module MA := M."
  echo "Module Type T2. Parameter d : nat. End T2."
  echo "Module F (X : T) : T2. Definition d := match X.c0 ax with X.c0 k => k end. End F."
  echo "Module Q := F MA."
  echo "Definition z0 := match MA.c0 ax with MA.c0 k => k end."
  for ((k = 1; k <= $1; k++)); do echo "Definition z$k := S z$((k - 1))."; done
  for _ in 1 2; do echo "Print Assumptions z$1."; echo "Print Assumptions Q.d."; done
}

# Compiles $1 under a CPU cap, leaving its output in $1.log, and prints its
# CPU seconds (user + system).
cpu() {
  local TIMEFORMAT='%U %S' t
  t=$( { time (ulimit -t 300; rocq c -q -R . P "$1" > "$1.log" 2>&1); } 2>&1 ) || true
  awk -v t="$t" 'BEGIN { split(t, a, " "); printf "%.2f", a[1] + a[2] }'
}

flip 8000 > Flip8000.v
aliaschain 8000 > AliasChain8000.v
blockchain 8000 > BlockChain8000.v

for f in Flip8000 AliasChain8000 BlockChain8000; do
  grep -v '^Print Assumptions' "$f.v" > "${f}NoQuery.v"
  full=$(cpu "$f.v")
  base=$(cpu "${f}NoQuery.v")
  case $f in
    Flip*) axiom='foo : nat' ;;
    *) axiom='ax : nat' ;;
  esac
  want="Axioms:
$axiom
Axioms:
$axiom
Axioms:
$axiom
Axioms:
$axiom"
  expect "$f" "$(cat "$f.v.log")" "$want"
  expect "${f}NoQuery" "$(cat "${f}NoQuery.v.log")" ""
  if ! awk -v f="$full" -v b="$base" 'BEGIN { exit !(f <= 3 * b + 1) }'; then
    echo "$f: ${full}s of CPU, against ${base}s without its queries"
    status=1
  fi
done

if ! $ocaml4; then
  echo "Skipping the stack and memory cases: not built with OCaml 4, whose limits they are measured against."
  exit $status
fi

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

# Q groups of M definitions with one shared body, F b0 ... b(K-1), and a root
# G(g) over its group's definitions; G0 ... G(Q-1) are queried in turn, so the
# queries share only F and the b's.
retain() {
  local k=$1 m=$2 q=$3 g j args xs bs zeros
  xs=$(seq -f 'x%g' 0 $((k - 1)) | tr '\n' ' ')
  bs=$(seq -f 'b%g' 0 $((k - 1)) | tr '\n' ' ')
  zeros=$(yes 0 | head -n $((k - m)) | tr '\n' ' ')
  echo "Axiom ax : nat."
  echo "Definition F (${xs}: nat) : nat := 0."
  seq -f 'Definition b%g := ax.' 0 $((k - 1))
  echo "Abbreviation BIG := (F ${bs% })."
  for ((g = 0; g < q; g++)); do
    args=""
    for ((j = 0; j < m; j++)); do echo "Definition d${g}_$j := BIG."; args+="d${g}_$j "; done
    echo "Definition G$g := F $args${zeros% }."
  done
  for ((g = 0; g < q; g++)); do echo "Print Assumptions G$g."; done
}

# The same with inductive blocks: group g holds M inductives whose
# constructors take a BIG, and G(g) is their product.
blockretain() {
  local k=$1 m=$2 q=$3 g j xs bs prod
  xs=$(seq -f 'x%g' 0 $((k - 1)) | tr '\n' ' ')
  bs=$(seq -f 'b%g' 0 $((k - 1)) | tr '\n' ' ')
  echo "Unset Elimination Schemes."
  echo "Axiom ax : nat."
  echo "Definition F (${xs}: nat) : Set := nat."
  seq -f 'Definition b%g := ax.' 0 $((k - 1))
  echo "Abbreviation BIG := (F ${bs% })."
  for ((g = 0; g < q; g++)); do
    prod=""
    for ((j = 0; j < m; j++)); do
      echo "Inductive I${g}_$j : Set := c${g}_$j : BIG -> I${g}_$j."
      prod+="I${g}_$j * "
    done
    echo "Definition G$g := (${prod% \* })%type."
  done
  for ((g = 0; g < q; g++)); do echo "Print Assumptions G$g."; done
}

{ chain 50000; echo "Print Assumptions x50000."; } > Chain50000.v
{ chain 72500; echo "Print Assumptions x72500."; } > Chain72500.v
leaves=()
for ((k = 10; k <= 100000; k += 10)); do leaves+=("x$k"); done
{ chain 100000; printf 'Definition R := '; tree "${leaves[@]}"; echo "."
  echo "Print Assumptions R."; echo "Print Assumptions R."; } > Fan100000.v
indchain 28000 > IndChain28000.v
mixchain 23000 > MixChain23000.v
wide 40000 > Wide40000.v

axiom_a='Axioms:
A : nat'
axiom_b='Axioms:
B : Type'
closed='Closed under the global context'

for f in Chain50000 Chain72500 Fan100000 IndChain28000 MixChain23000 Wide40000; do
  out=$(ulimit -s 8192; ulimit -v 2000000; rocq c -q -R . P "$f.v" 2>&1) || true
  case $f in
    Fan100000) want="$axiom_a
$axiom_a" ;;
    IndChain*|MixChain*) want=$axiom_b ;;
    Wide*) want="$closed
$closed" ;;
    *) want=$axiom_a ;;
  esac
  expect "$f" "$out" "$want"
done

retain 1000 100 64 > Retain64.v
blockretain 1000 100 64 > BlockRetain64.v
want=$(for ((g = 0; g < 64; g++)); do echo "Axioms:"; echo "ax : nat"; done)
for f in Retain64 BlockRetain64; do
  out=$(ulimit -s 8192; ulimit -v 1000000; rocq c -q -R . P "$f.v" 2>&1) || true
  expect "$f" "$out" "$want"
done
exit $status
