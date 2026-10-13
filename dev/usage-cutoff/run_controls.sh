#!/bin/bash
# Usage-cutoff controls: B.vo is built once against a BEFORE version of A.
# AFTER is then compiled in A's place (A rebuilt only), and we check whether
# the old B.vo still loads when C (which Requires B) is compiled, what
# coqchk says about the merged object set, and what Print Assumptions b
# reports. Run from this directory with ROCQC/ROCQCHK/ROCQTOP pointing at
# the patched fork's freshly built binaries, e.g.:
#   ROCQC=.../bin/coqc ROCQCHK=.../bin/coqchk ROCQTOP=.../bin/coqtop ./run_controls.sh
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-$HERE/work}"
FIX="$HERE/fixtures"
COQC="${ROCQC:-coqc}"
COQCHK="${ROCQCHK:-coqchk}"
COQTOP="${ROCQTOP:-coqtop}"
export OCAMLRUNPARAM=s=1M

case_() {
  local name=$1 before=$2 after=$3
  rm -rf "$WORK"; mkdir -p "$WORK"
  cp "$FIX"/X.v "$FIX"/B.v "$FIX"/C.v "$WORK"/
  cp "$FIX/$before" "$WORK/A.v"
  (cd "$WORK" && "$COQC" -Q . "" X.v && "$COQC" -Q . "" A.v && "$COQC" -Q . "" B.v) \
    >/dev/null 2>"$WORK/setup.err" || { echo "$name: SETUP FAILED: $(tail -1 "$WORK/setup.err")"; return; }
  cp "$FIX/$after" "$WORK/A.v"
  if ! (cd "$WORK" && "$COQC" -Q . "" A.v) >/dev/null 2>"$WORK/rebuildA.err"; then
    echo "$name: REBUILD A FAILED: $(tail -1 "$WORK/rebuildA.err")"; return
  fi
  local c chk pa
  if out=$(cd "$WORK" && "$COQC" -Q . "" C.v 2>&1); then c="C compiles (B.vo reused)"; else
    c="C REFUSED: $(echo "$out" | tail -1)"
  fi
  if out=$(cd "$WORK" && "$COQCHK" -o -Q . "" -norec A -norec B -norec C 2>&1); then chk=ok; else
    chk="FAIL: $(echo "$out" | grep -m1 -iE 'error|incons|fail')"
  fi
  pa=$(cd "$WORK" && printf 'Require Import C.\nPrint Assumptions B.b.\n' | "$COQTOP" -Q . "" 2>&1 \
    | grep -A2 -E 'Axioms|Closed' | tr '\n' ' ')
  echo "$name: $c | coqchk A,B,C: $chk | Print Assumptions b: $pa"
}

echo "== usage-cutoff controls (BEFORE -> AFTER, B/C built against BEFORE only) =="
case_ "1. Qed -> Qed (different proof, same statement)"      A_ref.v      A_qed2.v
case_ "2. Admitted -> Qed (same statement, filled in)"       A_admitted.v A_ref.v
case_ "3. unused declaration added (helper lemma, a unchanged)" A_ref.v   A_helper.v
case_ "4. statement changed"                                 A_ref.v      A_statement.v
case_ "5. new axiom used inside a's (opaque) proof"           A_ref.v      A_axiom.v
