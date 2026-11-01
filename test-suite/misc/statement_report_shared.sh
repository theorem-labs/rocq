#!/usr/bin/env bash

# The requests of one report share one walk (check_closure.ml, "One walk for
# every request"). What each request reports must stay exactly what a report
# of that request alone reports: this runs every request together, then each
# request on its own, and compares the lines of each.
#
# The tree carries what makes the shared walk differ from the per-request
# walk if it is wrong: an inductive block whose constructors name the block
# itself, two axioms, a relaxed typing flag, a module field with no body in
# the signature, and models that share most of their closure.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Shared.v" <<'EOF'
Inductive tree : Set := leaf : tree | node : tree -> tree -> tree.

Axiom base : tree.
Axiom other : nat.

Fixpoint size (t : tree) : nat :=
  match t with leaf => 1 | node l r => size l + size r end.

#[bypass_check(positivity)]
Inductive bad : Set := mk : (bad -> bad) -> bad.

Definition shared : tree := node base leaf.
Definition m_plain : nat := size shared.
Definition m_axiom : nat := size shared + other.
Definition m_flagged : Set := bad.

Module Type S. Parameter out : nat. End S.
Module M : S.
  Definition hidden : nat := size base.
  Definition out : nat := hidden.
End M.
Definition m_sealed : nat := M.out.
EOF

$coqc -Q "$d" StmtShared "$d/Shared.v"

models="m_plain m_axiom m_flagged m_sealed shared"

# Every request in one report: one walk serves them all.
: > "$d/requests"
for m in $models; do
  printf 'r_%s StmtShared.Shared.%s -\n' "$m" "$m" >> "$d/requests"
done
# The same model twice, so a repeated root is covered too.
printf 'r_again StmtShared.Shared.m_axiom -\n' >> "$d/requests"

"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtShared StmtShared.Shared \
  > "$d/together" 2>&1

# One report for each request: the walk cannot share anything.
: > "$d/apart"
for m in $models; do
  printf 'r_%s StmtShared.Shared.%s -\n' "$m" "$m" > "$d/one"
  "$BIN"rocqchk -silent -statement-report "$d/one" -Q "$d" StmtShared StmtShared.Shared \
    > "$d/one.out" 2>&1
  grep -E "^(statement|axiom|flag) r_${m} " "$d/one.out" >> "$d/apart"
done
grep -E '^(statement|axiom|flag) r_again ' "$d/together" | sed 's/ r_again / r_m_axiom /' \
  > "$d/again"

for m in $models; do
  grep -E "^(statement|axiom|flag) r_${m} " "$d/together" >> "$d/shared"
done

diff -u "$d/apart" "$d/shared"

# The repeated root reports what its first request reported.
grep -E '^(statement|axiom|flag) r_m_axiom ' "$d/together" > "$d/first"
diff -u "$d/first" "$d/again"

# The tree must really exercise axioms and a flag, or the test proves nothing.
awk '$1 == "statement" && $2 == "r_m_axiom" { exit !($6 >= 2) }
     END { }' "$d/together"
grep -q '^axiom r_m_axiom StmtShared.Shared.other$' "$d/together"
grep -q '^axiom r_m_axiom StmtShared.Shared.base$' "$d/together"
grep -q '^flag r_m_flagged assumed-positive StmtShared.Shared.bad$' "$d/together"
grep -q '^axiom r_m_sealed StmtShared.Shared.base$' "$d/together"

# What the sharing is for: the walk of a report of six requests must stay near
# the walk of one, not grow with the number of requests. One walk for each
# request is the sum of the six, which is what this asserts against.
printf 'r_one StmtShared.Shared.m_axiom -\n' > "$d/one"
COQ_TEST_SUITE_STATEMENT_REPORT_WALK=1 \
  "$BIN"rocqchk -silent -statement-report "$d/one" -Q "$d" StmtShared StmtShared.Shared \
  > "$d/walk.one" 2>&1
COQ_TEST_SUITE_STATEMENT_REPORT_WALK=1 \
  "$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtShared StmtShared.Shared \
  > "$d/walk.all" 2>&1
one=$(awk '$1 == "walk" { print $2 }' "$d/walk.one")
all=$(awk '$1 == "walk" { print $2 }' "$d/walk.all")
test -n "$one"
test -n "$all"
# Six requests over five models that share most of their closure. One walk for
# each request enters well over twice what one request enters.
if [ "$all" -gt $((2 * one)) ]; then
  echo "the report entered $all objects for six requests against $one for one: not shared" >&2
  exit 1
fi

echo OK
