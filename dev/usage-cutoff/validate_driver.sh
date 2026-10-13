#!/bin/bash
# Validates cutoff_rocq.py end to end through a real coq_makefile Makefile:
# for each (BEFORE -> AFTER) transition on A.v (or on B.v itself), compares the
# tree the driver produces (reusing whatever it can) against a fully fresh
# rebuild of the identical final sources, via Print Assumptions + coqchk.
set -euo pipefail
BIN=/rocq/rocq-usage-cutoff/_build/install/default/bin
FIX=/rocq/rocq-usage-cutoff/dev/usage-cutoff/fixtures
DRIVER=/rocq/rocq-usage-cutoff/dev/usage-cutoff/cutoff_rocq.py
export PATH=$BIN:$PATH
export CUTOFF_REAL_ROCQ=$BIN/rocq
ROOT=/tmp/cutoff-validate
rm -rf "$ROOT" && mkdir -p "$ROOT/driver" "$ROOT/fresh"

setup_project() {
  local dir=$1
  cd "$dir"
  cp "$FIX"/X.v "$FIX"/B.v "$FIX"/C.v .
  cat > _CoqProject <<EOF
-Q . ""
X.v
A.v
B.v
C.v
EOF
  rocq makefile -f _CoqProject -o Makefile
}

assumptions() {
  # prints Print Assumptions output for B.b and C.b via a scratch driver file
  local dir=$1
  cd "$dir"
  cat > _scratch.v <<EOF
Require Import C.
Print Assumptions B.b.
Print Assumptions C.b.
EOF
  coqc -Q . "" _scratch.v >/dev/null 2>&1
  coqtop -batch -Q . "" -require-import _scratch 2>&1 | grep -A2 -E "Axioms|Closed"
  rm -f _scratch.v _scratch.vo _scratch.glob
}

run_case() {
  local name=$1 before=$2 after=$3 expect=$4
  echo "== $name =="
  rm -rf "$ROOT/driver" "$ROOT/fresh"
  mkdir -p "$ROOT/driver" "$ROOT/fresh"
  setup_project "$ROOT/driver" >/dev/null
  cp "$ROOT"/driver/*.v "$ROOT"/driver/_CoqProject "$ROOT"/driver/Makefile "$ROOT/fresh/" 2>/dev/null || true
  setup_project "$ROOT/fresh" >/dev/null

  cp "$FIX/$before" "$ROOT/driver/A.v"
  cp "$FIX/$before" "$ROOT/fresh/A.v"
  cd "$ROOT/driver"
  rm -f cutoff-stats.log
  make -f Makefile real-all ROCQ="python3 $DRIVER" CUTOFF_STATS_LOG="$ROOT/driver/cutoff-stats.log" >/dev/null 2>"$ROOT/driver/build1.log" || { echo "FAIL: driver initial build"; cat "$ROOT/driver/build1.log"; return; }
  cd "$ROOT/fresh"
  make -f Makefile real-all >/dev/null 2>"$ROOT/fresh/build1.log" || { echo "FAIL: fresh initial build"; return; }

  cp "$FIX/$after" "$ROOT/driver/A.v"
  cp "$FIX/$after" "$ROOT/fresh/A.v"
  cd "$ROOT/driver"
  rm -f cutoff-stats.log
  make -f Makefile real-all ROCQ="python3 $DRIVER" CUTOFF_STATS_LOG="$ROOT/driver/cutoff-stats.log" >/dev/null 2>"$ROOT/driver/build2.log"
  driver_decisions=$(cat "$ROOT/driver/cutoff-stats.log" | tr '\n' ';')
  cd "$ROOT/fresh"
  rm -f ./*.vo.cutoff-stamp
  rm -f A.vo B.vo C.vo A.glob B.glob C.glob A.vos A.vok B.vos B.vok C.vos C.vok
  make -f Makefile real-all >/dev/null 2>"$ROOT/fresh/build2.log"

  da=$(assumptions "$ROOT/driver")
  fa=$(assumptions "$ROOT/fresh")
  if [ "$da" = "$fa" ]; then eq="Print Assumptions MATCH"; else eq="Print Assumptions MISMATCH: driver=[$da] fresh=[$fa]"; fi
  cd "$ROOT/driver"
  if coqchk -o -Q . "" A B C >coqchk.out 2>&1; then chk="coqchk ok"; else chk="coqchk FAILED: $(tail -3 coqchk.out)"; fi
  echo "decisions: $driver_decisions"
  echo "expected-pattern: $expect"
  echo "$eq | $chk"
  echo
}

run_case "1. Qed -> Qed (different proof)"            A_ref.v      A_qed2.v     "B REUSED, C never invoked"
run_case "2. Admitted -> Qed"                          A_admitted.v A_ref.v      "B REUSED, C never invoked"
run_case "3. unused helper lemma added"                A_ref.v      A_helper.v   "B REUSED, C never invoked"
run_case "4. statement changed"                        A_ref.v      A_statement.v "B REBUILD-REFUSED, C then rebuilds too"
run_case "5. axiom used inside opaque proof"            A_ref.v      A_axiom.v    "B REUSED (axiom still visible), C never invoked"
echo "All done."
