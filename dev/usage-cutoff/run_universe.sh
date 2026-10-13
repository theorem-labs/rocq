#!/bin/bash
# Usage-cutoff adversarial control: can an agent's opaque proof add a universe
# constraint that contradicts one in a dependent compiled against the
# reference, without the reused dependent being refused at load time? The
# loader's interface digest deliberately does not track comp_univs (library-
# wide monomorphic constraints), so this case is expected to be ACCEPTED by
# the relaxed loader; the claim under test is that coqchk (run over the
# actual merged object set regardless of how it got assembled) still catches
# the inconsistency. See docs/build/ROCQ-USAGE-CUTOFF.md for the argument.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-$HERE/work-universe}"
FIX="$HERE/fixtures"
COQC="${ROCQC:-coqc}"
COQCHK="${ROCQCHK:-coqchk}"
export OCAMLRUNPARAM=s=1M

rm -rf "$WORK"; mkdir -p "$WORK"
cp "$FIX"/U.v "$WORK/U.v"
cp "$FIX"/B_u.v "$WORK/B.v"
cp "$FIX"/C_u.v "$WORK/C.v"
cp "$FIX"/A_uref.v "$WORK/A.v"
(cd "$WORK" && "$COQC" -Q . "" U.v && "$COQC" -Q . "" A.v && "$COQC" -Q . "" B.v) \
  >/dev/null 2>"$WORK/setup.err" || { echo "setup failed: $(tail -1 "$WORK/setup.err")"; exit 1; }

echo "== sanity: agent A and B together from scratch (both rebuilt, no reuse) =="
mkdir -p "$WORK/fresh"
cp "$FIX"/U.v "$FIX"/B_u.v "$WORK"/C.v "$WORK/fresh/"
mv "$WORK/fresh/B_u.v" "$WORK/fresh/B.v" 2>/dev/null
cp "$FIX"/A_uagent.v "$WORK/fresh/A.v"
(cd "$WORK/fresh" && "$COQC" -Q . "" U.v && "$COQC" -Q . "" A.v && "$COQC" -Q . "" B.v) 2>&1 | tail -3

echo "== reuse: agent's A rebuilt (introduces a contradicting universe constraint), B.vo kept from the reference build =="
cp "$FIX"/A_uagent.v "$WORK/A.v"
if (cd "$WORK" && "$COQC" -Q . "" A.v) >"$WORK/agentA.log" 2>&1; then
  echo "agent A compiled standalone (as expected: the constraint is only a problem once merged with B)"
else
  echo "agent A failed to compile: $(tail -1 "$WORK/agentA.log")"; exit 1
fi
echo "-- coqc C (does B.vo get reused, i.e. does the loader accept it despite the new universe constraint in A?):"
(cd "$WORK" && "$COQC" -Q . "" C.v) 2>&1 | tail -3
echo "-- coqchk over the merged set (A rebuilt + B,C reused/compiled against it) -- this is the trust anchor:"
(cd "$WORK" && "$COQCHK" -o -Q . "" -norec U -norec A -norec B -norec C) 2>&1 \
  | grep -iE 'error|incons|universe|fatal|successfully' | head -4
echo "-- coqchk with B admitted (trusted, not rechecked) and only A checked, for contrast:"
(cd "$WORK" && "$COQCHK" -o -Q . "" -admit B -norec A) 2>&1 \
  | grep -iE 'error|incons|universe|fatal|successfully' | head -4
