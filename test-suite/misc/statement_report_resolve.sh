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
grep -q '^axiom hidden [^ ]* StmtRes.Res.N.ax$' "$d/out"
grep -q '^statement final StmtRes.Res.P.ax - not-requested 1 0$' "$d/out"
# P.ax is a key of the final environment, so it answers from there (by the
# order of the lookup in check_closure.ml's print), never as ambiguous.
grep -q '^statement none StmtRes.Res.M.nothing - model-missing 0 0$' "$d/out"
