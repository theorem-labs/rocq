#!/usr/bin/env bash

# rocqchk -statement-report prints each axiom's canonical kernel name beside
# the path the closure reached it by. Two distinct constants with the same
# short name keep two canonical names; one constant reached through a sealed
# module's Include is printed by the path the term names and the canonical
# name of the constant it is.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cat > "$d/Canon.v" <<'EOF'
Module A. Axiom ax : nat. End A.
Module B. Axiom ax : nat. End B.
Definition two_distinct : nat := A.ax + B.ax.

Module Type T. Parameter n : nat. End T.
Module N. Axiom ax : nat. Definition n : nat := ax. End N.
Module M : T. Include N. End M.
Definition through_include : nat := M.n.
EOF
$coqc -Q "$d" StmtCanon "$d/Canon.v"
printf 'two StmtCanon.Canon.two_distinct -\ninc StmtCanon.Canon.through_include -\n' > "$d/requests"
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtCanon StmtCanon.Canon > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/out"
grep -q '^STATEMENT REPORT 2$' "$d/out"
grep -q '^END STATEMENT REPORT$' "$d/out"
grep -q '^axiom two StmtCanon.Canon.A.ax StmtCanon.Canon:A.ax$' "$d/out"
grep -q '^axiom two StmtCanon.Canon.B.ax StmtCanon.Canon:B.ax$' "$d/out"
# Exactly one axiom for the Include, whose canonical name is N.ax.
[ "$(grep -c '^axiom inc ' "$d/out")" = 1 ]
grep -q '^axiom inc [^ ]* StmtCanon.Canon:N.ax$' "$d/out"
# Every axiom line has four tokens.
awk '$1 == "axiom" && NF != 4 { bad = 1 } END { exit bad }' "$d/out"

# Library P.A with module B, and library P.A.B: two constants whose dotted
# paths print alike keep two canonical names.
mkdir -p "$d/P/A"
cat > "$d/P/A.v" <<'V'
Module B. Axiom ax : nat. End B.
Definition left : nat := B.ax.
V
cat > "$d/P/A/B.v" <<'V'
Axiom ax : nat.
Definition right : nat := ax.
V
$coqc -Q "$d/P" P "$d/P/A.v"
$coqc -Q "$d/P" P "$d/P/A/B.v"
printf 'left P.A.left -\nright P.A.B.right -\n' > "$d/preq"
"$BIN"rocqchk -silent -statement-report "$d/preq" -Q "$d/P" P P.A P.A.B > "$d/pout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/pout"
grep -q '^axiom left P.A.B.ax P.A:B.ax$' "$d/pout"
grep -q '^axiom right P.A.B.ax P.A.B:ax$' "$d/pout"

# A functor's own axiom is printed under the functor argument's unique form.
cat > "$d/Fun.v" <<'V'
Module Type E. End E.
Module F (X : E). Axiom ax : nat. Definition n : nat := ax. End F.
V
$coqc -Q "$d" StmtCanon "$d/Fun.v"
printf 'fn StmtCanon.Fun.F.n -\n' > "$d/freq"
"$BIN"rocqchk -silent -statement-report "$d/freq" -Q "$d" StmtCanon StmtCanon.Fun > "$d/fout" 2>&1 || true
awk '$1 == "axiom" && $4 !~ /:/ { bad = 1 } END { exit bad }' "$d/fout" "$d/out" "$d/pout"
