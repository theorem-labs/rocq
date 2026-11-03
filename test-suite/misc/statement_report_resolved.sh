#!/usr/bin/env bash

# A bodyless interface field the closure reads through its implementation is
# named by a `resolved <stmt> <field> <implementation-canonical>` line; one
# whose implementation is not walked is not. The implementation's own axioms
# are listed as axiom lines. Closures are unchanged.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cat > "$d/Rsv.v" <<'V'
Module Type T. Parameter n : nat. End T.
Module N. Axiom ax : nat. Definition n : nat := ax. End N.
Module M : T. Include N. End M.
Definition through : nat := M.n.

Module P : T. Definition n : nat := 0. End P.
(* P.n is in the summary but nothing this statement walks reaches it. *)
Definition untouched : nat := 1.
V
$coqc -Q "$d" StmtRsv "$d/Rsv.v"
printf 'through StmtRsv.Rsv.through -\nuntouched StmtRsv.Rsv.untouched -\n' > "$d/requests"
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtRsv StmtRsv.Rsv > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/out"
grep -q '^resolved through StmtRsv.Rsv.M.n StmtRsv.Rsv.M.n$' "$d/out" \
  || grep -q '^resolved through StmtRsv.Rsv.M.n StmtRsv.Rsv.N.n$' "$d/out"
# The implementation's axiom is its own axiom line.
grep -q '^axiom through [^ ]* StmtRsv.Rsv.N.ax$' "$d/out"
# No resolved line where no implementation was walked.
if grep -q '^resolved untouched ' "$d/out"; then exit 1; fi
grep -q '^END STATEMENT REPORT$' "$d/out"
