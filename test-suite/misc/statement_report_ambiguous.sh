#!/usr/bin/env bash

# One dotted name that two implementations hide: library P.A's module B.C and
# library P.A.B's module C. The request answers ambiguous with no closure.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir -p "$d/A"
cat > "$d/A.v" <<'V'
Module Type Empty. End Empty.
Module B. Module C : Empty. Axiom ax : nat. End C. End B.
V
cat > "$d/A/B.v" <<'V'
Module Type Empty. End Empty.
Module C : Empty. Axiom ax : nat. End C.
V
$coqc -Q "$d" P "$d/A.v"
$coqc -Q "$d" P "$d/A/B.v"
printf 'amb P.A.B.C.ax -\n' > "$d/requests"
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" P P.A P.A.B > "$d/out" 2>&1
sed -n '/^STATEMENT REPORT 2$/,/^END STATEMENT REPORT$/p' "$d/out"
grep -q '^statement amb P.A.B.C.ax - ambiguous 0 0$' "$d/out"
if grep -qE '^(axiom|resolved|flag) amb ' "$d/out"; then exit 1; fi
grep -q '^END STATEMENT REPORT$' "$d/out"
