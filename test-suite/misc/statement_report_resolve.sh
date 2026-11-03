#!/usr/bin/env bash

# A request's subject the final environment does not hold is looked up in the
# implementations, as Print Assumptions finds a constant a seal hides. A name
# the final environment holds answers from there, and the implementation is
# not searched for it. A name nothing holds is model-missing.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cat > "$d/Res.v" <<'EOF'
Module Type T. Parameter n : nat. End T.
Module N. Axiom ax : nat. Definition n : nat := ax. End N.
(* M.ax exists only in M's implementation (the Include), canonically N.ax. *)
Module M : T. Include N. End M.

Module Type TA. Parameter ax : nat. End TA.
(* P.ax is in the final environment (the seal's parameter, canonically P.ax)
   and, with canonical N.ax, in P's implementation. *)
Module P : TA. Include N. End P.
EOF
$coqc -Q "$d" StmtRes "$d/Res.v"
printf 'hidden StmtRes.Res.M.ax -\nfinal StmtRes.Res.P.ax -\nnone StmtRes.Res.M.nothing -\n' > "$d/requests"
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtRes StmtRes.Res > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/out"
grep -q '^statement hidden StmtRes.Res.M.ax - not-requested 1 0$' "$d/out"
grep -q '^axiom hidden [^ ]* StmtRes.Res:N.ax$' "$d/out"
grep -q '^statement final StmtRes.Res.P.ax - not-requested 1 0$' "$d/out"
# P.ax is a key of the final environment, so it answers from there (by the
# order of the lookup in check_closure.ml's print), never as ambiguous.
grep -q '^statement none StmtRes.Res.M.nothing - model-missing 0 0$' "$d/out"

# A typed request on a model only an implementation holds answers
# model-missing, and the report goes on: its type may name the
# implementation's own definitions, which the final environment lacks.
cat > "$d/Hid.v" <<'V'
Module Type Empty. End Empty.
Module M : Empty. Definition T := nat. Axiom ax : T. End M.
Definition trusted : nat := 0.
V
$coqc -Q "$d" StmtRes "$d/Hid.v"
printf 'closure StmtRes.Hid.M.ax -\ntyped StmtRes.Hid.M.ax StmtRes.Hid.trusted\nafter StmtRes.Hid.trusted -\n' > "$d/treq"
"$BIN"rocqchk -silent -statement-report "$d/treq" -Q "$d" StmtRes StmtRes.Hid > "$d/tout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/tout"
grep -q '^statement closure StmtRes.Hid.M.ax - not-requested 1 0$' "$d/tout"
grep -q '^statement typed StmtRes.Hid.M.ax StmtRes.Hid.trusted model-missing 0 0$' "$d/tout"
grep -q '^statement after StmtRes.Hid.trusted - not-requested 0 0$' "$d/tout"
grep -q '^END STATEMENT REPORT$' "$d/tout"

# A name the final environment holds answers from there, and the
# implementations are not searched for it: library P.A hides ax in a sealed
# B, library P.A.B has a public ax, and both print as P.A.B.ax.
mkdir -p "$d/P/A"
cat > "$d/P/A.v" <<'V'
Module Type Empty. End Empty.
Module B : Empty. Axiom ax : nat. End B.
V
cat > "$d/P/A/B.v" <<'V'
Axiom ax : nat.
V
$coqc -Q "$d/P" P "$d/P/A.v"
$coqc -Q "$d/P" P "$d/P/A/B.v"
printf 'pub P.A.B.ax -\n' > "$d/preq"
"$BIN"rocqchk -silent -statement-report "$d/preq" -Q "$d/P" P P.A P.A.B > "$d/pout" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/pout"
grep -q '^statement pub P.A.B.ax - not-requested 1 0$' "$d/pout"
grep -q '^axiom pub P.A.B.ax P.A.B:ax$' "$d/pout"
if grep -q 'P.A:B.ax' "$d/pout"; then exit 1; fi
grep -q '^END STATEMENT REPORT$' "$d/pout"
