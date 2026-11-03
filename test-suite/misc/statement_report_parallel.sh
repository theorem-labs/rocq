#!/usr/bin/env bash

# With -j N, forked processes read and walk the opaque bodies of the
# environment ahead of the report's walk (check_closure.ml, "Opaque bodies
# read ahead"). The report must be the one -j 1 prints, byte for byte, on
# standard output and on standard error. This runs one report at -j 1 and at
# -j 4 and compares both streams, then does the same with an opaque body that
# cannot be read: its warning must be printed where -j 1 prints it.
#
# The tree has opaque proofs that reach two axioms, a relaxed typing flag
# reached through an opaque proof, a sealed module field whose implementation
# is an opaque proof, and enough opaque proofs to keep several processes busy.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

{
  cat <<'EOF'
Inductive tree : Set := leaf : tree | node : tree -> tree -> tree.

Axiom base : tree.
Axiom other : nat.

Fixpoint size (t : tree) : nat :=
  match t with leaf => 1 | node l r => size l + size r end.

#[bypass_check(positivity)]
Inductive bad : Set := mk : (bad -> bad) -> bad.

Lemma shared : tree.
Proof. exact (node base leaf). Qed.

Lemma uses_bad : Set.
Proof. exact bad. Qed.

Definition keep (A : Set) (n : nat) : nat := n.

Module Type S. Parameter out : nat. End S.
Module M : S.
  Lemma hidden : nat.
  Proof. exact (size base). Qed.
  Definition out : nat := hidden.
End M.

Lemma p0 : nat.
Proof. exact (size shared). Qed.
EOF
  # A chain of opaque proofs, each reaching the one before it and, in turn,
  # an axiom, the sealed field, or the flagged inductive.
  for i in $(seq 1 200); do
    case $((i % 3)) in
      0) step="p$((i - 1)) + other" ;;
      1) step="p$((i - 1)) + M.out" ;;
      *) step="keep uses_bad p$((i - 1))" ;;
    esac
    printf 'Lemma p%d : nat.\nProof. exact (%s). Qed.\n' "$i" "$step"
  done
} > "$d/Par.v"

$coqc -Q "$d" StmtParallel "$d/Par.v"

P=StmtParallel.Par
cat > "$d/requests" <<EOF
r_top $P.p200 -
r_mid $P.p100 -
r_shared $P.shared -
r_flagged $P.uses_bad -
r_sealed $P.M.out -
r_plain $P.size -
r_typed $P.p1 $P.p2
EOF

# run JOBS NAME [VAR=VALUE...]: the report at -j JOBS, its standard output in
# NAME.out and its standard error in NAME.err.
run() {
  local jobs=$1 name=$2
  shift 2
  env "$@" "$BIN"rocqchk -silent -j "$jobs" -statement-report "$d/requests" \
    -Q "$d" StmtParallel StmtParallel.Par > "$d/$name.out" 2> "$d/$name.err"
}

same() {
  diff -u "$d/$1.out" "$d/$2.out"
  diff -u "$d/$1.err" "$d/$2.err"
}

run 1 serial
run 4 parallel
same serial parallel

# The tree must really exercise axioms, a flag and the sealed field through
# opaque proofs, or the comparison proves nothing.
grep -q '^END STATEMENT REPORT$' "$d/parallel.err"
grep -q "^axiom r_top $P.base\$" "$d/parallel.err"
grep -q "^axiom r_top $P.other\$" "$d/parallel.err"
grep -q "^flag r_top assumed-positive $P.bad\$" "$d/parallel.err"
grep -q "^flag r_flagged assumed-positive $P.bad\$" "$d/parallel.err"
grep -q "^axiom r_sealed $P.base\$" "$d/parallel.err"
grep -q "^axiom r_shared $P.base\$" "$d/parallel.err"
grep -q "^statement r_typed $P.p1 $P.p2 match " "$d/parallel.err"

# The processes did the work: the walk took nodes from them at -j 4, and none
# at -j 1. The seam is a test variable the checker reads only when it is set
# (check_closure.ml's test_read_ahead_count, beside test_fault).
used() {
  awk '$1 == "read" && $2 == "ahead" { print $3 }' "$d/$1.err"
}
run 4 seam COQ_TEST_SUITE_STATEMENT_REPORT_READ_AHEAD=1
run 1 seam1 COQ_TEST_SUITE_STATEMENT_REPORT_READ_AHEAD=1
test -n "$(used seam)"
if [ "$(used seam)" -le 100 ]; then
  echo "the walk took $(used seam) nodes from the processes" >&2; exit 1
fi
test "$(used seam1)" = 0

# An opaque body that cannot be read, one the processes would read ahead and
# one that only the walk reaches (the implementation of the sealed field): the
# processes send nothing for either, and the walk warns where it warns at -j 1.
for c in $P.p150 $P.M.hidden; do
  run 1 unreadable1 COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$c"
  run 4 unreadable4 COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$c"
  same unreadable1 unreadable4
  grep -q "Statement report: the opaque body of $c could not be read" "$d/unreadable4.err"
  grep -q "^axiom r_top $c\$" "$d/unreadable4.err"
done

echo OK
