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

# The two print alike as P.A.B.ax: as a model or a trusted constant the
# name is ambiguous, never one of them picked.
printf 'm P.A.B.ax -\nt P.A.left P.A.B.ax\n' > "$d/areq"
"$BIN"rocqchk -silent -statement-report "$d/areq" -Q "$d/P" P P.A P.A.B > "$d/aout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/aout"
grep -q '^statement m P.A.B.ax - ambiguous 0 0$' "$d/aout"
grep -q '^statement t P.A.left P.A.B.ax trusted-ambiguous 1 0$' "$d/aout"
grep -q '^END STATEMENT REPORT$' "$d/aout"

# Every canonical on an axiom line has the root separator.
awk '$1 == "axiom" && $4 !~ /:/ { bad = 1 } END { exit bad }' "$d/out" "$d/pout" "$d/aout"

# Functor arguments: the closure walks an applied functor's body under the
# argument substitution, so an axiom reached through a functor argument
# prints the argument's library root, not a bound-module root.
cat > "$d/Fn.v" <<'V'
Module Type T. Parameter ax : nat. End T.
Module A. Axiom ax : nat. End A.
Module F (X : T). Definition n : nat := X.ax. End F.
Module B := F A.
Module G (X : T) : T. Definition ax : nat := X.ax. End G.
Module C := G A.
Module Type S. Declare Module X : T. Definition m : nat := X.ax. End S.
Declare Module D : S.
Definition u1 : nat := B.n.
Definition u2 : nat := C.ax.
Definition u3 : nat := D.m.
V
$coqc -Q "$d" StmtCanon "$d/Fn.v"
printf 'u1 StmtCanon.Fn.u1 -\nu2 StmtCanon.Fn.u2 -\nu3 StmtCanon.Fn.u3 -\nf StmtCanon.Fn.F.n -\n' > "$d/fnreq"
"$BIN"rocqchk -silent -statement-report "$d/fnreq" -Q "$d" StmtCanon StmtCanon.Fn > "$d/fnout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/fnout"
grep -q '^axiom u1 StmtCanon.Fn.A.ax StmtCanon.Fn:A.ax$' "$d/fnout"
grep -q '^axiom u2 StmtCanon.Fn.A.ax StmtCanon.Fn:A.ax$' "$d/fnout"
grep -q '^axiom u3 StmtCanon.Fn.D.X.ax StmtCanon.Fn:D.X.ax$' "$d/fnout"
# An unapplied functor's field is not a request target.
grep -q '^statement f StmtCanon.Fn.F.n - model-missing 0 0$' "$d/fnout"
grep -q '^END STATEMENT REPORT$' "$d/fnout"

# Two implementation-only axioms that print the same path (P.A's module B.C
# and P.A.B's module C each hide an ax) get two distinct tokens after ?, the
# term's own canonical, so no set keyed on the printed line can merge them.
# One library cannot require both (coqc: "Q.A.B already exists"), so each
# is reached from its own library, in one report.
mkdir -p "$d/Q/A"
cat > "$d/Q/A.v" <<'V'
Module Type T. Parameter n : nat. End T.
Module B. Module C : T. Axiom ax : nat. Definition n : nat := ax. End C. End B.
Definition left : nat := B.C.n.
V
cat > "$d/Q/A/B.v" <<'V'
Module Type T. Parameter n : nat. End T.
Module C : T. Axiom ax : nat. Definition n : nat := ax. End C.
Definition right : nat := C.n.
V
$coqc -Q "$d/Q" Q "$d/Q/A.v"
$coqc -Q "$d/Q" Q "$d/Q/A/B.v"
printf 'left Q.A.left -\nright Q.A.B.right -\n' > "$d/qreq"
"$BIN"rocqchk -silent -statement-report "$d/qreq" -Q "$d/Q" Q Q.A Q.A.B > "$d/qout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/qout"
grep -q '^axiom left Q.A.B.C.ax ?Q.A:B.C.ax$' "$d/qout"
grep -q '^axiom right Q.A.B.C.ax ?Q.A.B:C.ax$' "$d/qout"
[ "$(grep -c '^axiom [a-z]* Q.A.B.C.ax ?' "$d/qout")" = 2 ]
grep -q '^END STATEMENT REPORT$' "$d/qout"

# Two unsafe fixpoints named f that print one path (P.A's module B, and
# library P.A.B) give two flag lines, told apart by the canonical column.
# One library cannot require both, so each is reached from its own request.
mkdir -p "$d/G/A"
cat > "$d/G/A.v" <<'V'
Module B. #[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n. End B.
Definition left : nat := B.f 0.
V
cat > "$d/G/A/B.v" <<'V'
#[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n.
Definition right : nat := f 0.
V
$coqc -Q "$d/G" G "$d/G/A.v"
$coqc -Q "$d/G" G "$d/G/A/B.v"
printf 'left G.A.left -\nright G.A.B.right -\n' > "$d/greq"
"$BIN"rocqchk -silent -statement-report "$d/greq" -Q "$d/G" G G.A G.A.B > "$d/gout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/gout"
grep -q '^flag left unsafe-fixpoint G.A.B.f G.A:B.f$' "$d/gout"
grep -q '^flag right unsafe-fixpoint G.A.B.f G.A.B:f$' "$d/gout"
[ "$(grep -c '^flag [a-z]* unsafe-fixpoint G.A.B.f ' "$d/gout")" = 2 ]
awk '$1 == "flag" && NF != 5 { bad = 1 } END { exit bad }' "$d/gout"
grep -q '^END STATEMENT REPORT$' "$d/gout"
