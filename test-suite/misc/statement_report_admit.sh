#!/usr/bin/env bash

# rocqchk -statement-report with a model library that is admitted and reached
# from no checked library. Before the recheck_library admit-intern fix,
# recheck_library interned the check and norec lists but not the admit list,
# then looked the admit closure up in depgraph, so such a library -- absent
# from depgraph -- raised Anomaly "missing dep when computing closure
# (StmtAdmit.Model)" and aborted the whole run, costing every statement its
# verdict. This is the shape a -statement-report run produces: the model
# library is referenced by constant name, not Require'd by the checked
# statement library. Found by S4 (BET-257), 2026-10-28.
#
# The report must complete with a verdict, with the vm_compute machine off
# (default) and on.

set -eu

D=misc/statement_report_admit
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D"/Model.v "$D"/Stmt.v "$D"/requests "$d/"

$coqc -noinit -Q "$d" StmtAdmit "$d/Model.v"
$coqc -noinit -Q "$d" StmtAdmit "$d/Stmt.v"

run () {  # $1 = label; rest = extra rocqchk flags (vm toggle)
  label=$1; shift
  "$BIN"rocqchk -silent "$@" -statement-report "$d/requests" -Q "$d" StmtAdmit \
    -admit StmtAdmit.Model -norec StmtAdmit.Stmt > "$d/out.log" 2>&1 \
    || { echo "FAIL: rocqchk exited non-zero ($label)"; cat "$d/out.log"; exit 1; }
  if grep -q 'Anomaly' "$d/out.log"; then
    echo "FAIL: anomaly ($label)"; cat "$d/out.log"; exit 1
  fi
  grep -q '^statement unreached ' "$d/out.log" \
    || { echo "FAIL: no verdict for the statement ($label)"; cat "$d/out.log"; exit 1; }
}

run "vm-off"
run "vm-on" -bytecode-compiler yes

echo "statement_report_admit: ok"
