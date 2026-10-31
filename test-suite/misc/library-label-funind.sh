#!/usr/bin/env bash
# D18 (dispatch://INFRA-361), Astra review 3 N1: `Functional Scheme` reads whether a
# foreign equation lemma is an axiom or an opaque proof, and the keepfacts record it.
#
# plugins/funind/gen_principle.ml (make_scheme) makes the generated principle an opaque
# proof when the function's equation lemma (`<f>_equation`, found by its short name in
# scope) is one, and a transparent definition otherwise. A's `f_equation` is Admitted in
# `adm` and proved in `qed`; the label blinds that, so A's two labels are equal, and a B
# compiled against the Admitted A still loads next to the proved one. Without a record,
# a keep rule would keep B, while a clean rebuild of B against the proved A fails at
# `Transparent local_scheme` (the principle is then an opaque proof). With the record,
# B's keepfacts name A.f_equation with the status it saw, and the keep rule rebuilds B
# when A's status no longer matches.
#
# Checks:
# - A's labels are equal across `f_equation` Admitted -> Qed;
# - B (Functional Scheme local_scheme := Induction for f Sort Prop. Transparent
#   local_scheme.) compiled against the Admitted A records
#   {A.f_equation, A, opaque=false, table=null};
# - B fails against the proved A, at `Transparent local_scheme` ("declared opaque");
# - B compiled against the Admitted A loads next to the proved A (what a kept B is);
# - the control BC (B without the Transparent) records the same query against the
#   Admitted A, records opaque=true against the proved A, and its local_scheme is a
#   transparent definition in the first and an opaque proof in the second.
#
# The test suite has no Stdlib, so B loads the funind plugin the way the test suite's
# own prerequisite does (test-suite/prerequisite/funind.v, which Stdlib's FunInd
# matches): `From Corelib Require Extraction.` and `Declare ML Module`.

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _funind
mkdir -p _funind/{adm,qed,b,bqed,bc,bcqed,client}

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
report() { "$TOOL" --axiom-report-json "$1"; }
field() { report "$1" | sed -n "s/.*\"$2\":\(\[[^]]*\]\|{[^}]*}\|null\).*/\1/p"; }
comp() { rocq c -q -location-free-label "$@"; }

D=_funind
printf 'Definition f (n : nat) : nat := n.\nLemma f_equation : forall n : nat, f n = n.\nAdmitted.\n' > $D/adm/A.v
printf 'Definition f (n : nat) : nat := n.\nLemma f_equation : forall n : nat, f n = n.\nProof. intro n. reflexivity. Qed.\n' \
  > $D/qed/A.v
head='From Corelib Require Extraction.
Declare ML Module "rocq-runtime.plugins.funind".
Require Import A.
Functional Scheme local_scheme := Induction for f Sort Prop.'
printf '%s\nTransparent local_scheme.\n' "$head" > $D/b/B.v
cp $D/b/B.v $D/bqed/B.v
printf '%s\n' "$head" > $D/bc/B.v
cp $D/bc/B.v $D/bcqed/B.v

comp -R $D/adm A $D/adm/A.v
comp -R $D/qed A $D/qed/A.v
alib=$(report $D/adm/A.vo | sed -n 's/.*"library":"\([^"]*\)".*/\1/p')
if [ "$(label $D/adm/A.vo)" = "$(label $D/qed/A.vo)" ]; then
  pass "A's label is equal across f_equation Admitted -> Qed ($(label $D/adm/A.vo))"
else
  bad "A's label differs across f_equation Admitted -> Qed (expected equal)"
fi

aba=$(field $D/adm/A.vo axiom_blind); abq=$(field $D/qed/A.vo axiom_blind)
if [ "$aba" = "[{\"constant\":\"$alib.f_equation\",\"status\":\"axiom\"}]" ] \
   && [ "$abq" = "[{\"constant\":\"$alib.f_equation\",\"status\":\"proof\"}]" ]; then
  pass "A's axiom_blind lists $alib.f_equation as an axiom, then as a proof: the name B's query uses"
else
  bad "A's axiom_blind: '$aba' (Admitted), '$abq' (Qed)"
fi
q_adm="[{\"constant\":\"$alib.f_equation\",\"library\":\"$alib\",\"opaque\":false,\"table\":null}]"
q_qed="[{\"constant\":\"$alib.f_equation\",\"library\":\"$alib\",\"opaque\":true,\"table\":null}]"

# B against the Admitted A: compiles, records the status it saw.
if comp -R $D/adm A -R $D/b Bdep $D/b/B.v > $D/b/out 2>&1; then
  qb=$(field $D/b/B.vo opacity_queries)
  if [ "$qb" = "$q_adm" ]; then
    pass "B (Functional Scheme + Transparent local_scheme) records the Admitted f_equation: $qb"
  else
    bad "B's opacity_queries against the Admitted A: '$qb'"
  fi
else
  bad "B failed against the Admitted A: $(tr '\n' ' ' < $D/b/out | cut -c1-600)"
fi

# B against the proved A: a clean rebuild fails at Transparent local_scheme.
if comp -R $D/qed A -R $D/bqed Bdep $D/bqed/B.v > $D/bqed/out 2>&1; then
  bad "B compiled against the proved A (expected Transparent local_scheme to fail)"
elif tr '\n' ' ' < $D/bqed/out | grep -q 'Cannot make .*local_scheme.* transparent because it was declared  *opaque'; then
  pass "B fails against the proved A at Transparent local_scheme (declared opaque), so a kept B would hide a failing build"
else
  bad "B fails against the proved A for another reason: $(tr '\n' ' ' < $D/bqed/out | cut -c1-600)"
fi

# What a kept B is: B compiled against the Admitted A loads next to the proved A.
printf 'Require Bdep.B.\n' > $D/client/C.v
if [ -f $D/b/B.vo ] && comp -R $D/qed A -R $D/b Bdep -R $D/client Cl $D/client/C.v > $D/client/out 2>&1; then
  pass "B compiled against the Admitted A loads next to the proved A: only its record tells the keep rule to rebuild it"
else
  bad "B compiled against the Admitted A does not load next to the proved A: $(tr '\n' ' ' < $D/client/out 2>/dev/null | cut -c1-600)"
fi

# Control: no Transparent. Both builds finish; the record and the generated
# declaration still follow f_equation's status.
comp -R $D/adm A -R $D/bc Bdep $D/bc/B.v
comp -R $D/qed A -R $D/bcqed Bdep $D/bcqed/B.v
qc=$(field $D/bc/B.vo opacity_queries); qcq=$(field $D/bcqed/B.vo opacity_queries)
if [ "$qc" = "$q_adm" ] && [ "$qcq" = "$q_qed" ]; then
  pass "control BC records the status it saw: $qc against the Admitted A, $qcq against the proved A"
else
  bad "control BC's opacity_queries: '$qc' against the Admitted A, '$qcq' against the proved A"
fi
ab=$(field $D/bc/B.vo axiom_blind); abq=$(field $D/bcqed/B.vo axiom_blind)
if ! printf '%s' "$ab" | grep -q 'local_scheme' \
   && printf '%s' "$abq" | grep -q '"constant":"Bdep.B.local_scheme","status":"proof"'; then
  pass "control BC: local_scheme is a transparent definition against the Admitted A and an opaque proof against the proved A"
else
  bad "control BC's local_scheme: axiom_blind '$ab' against the Admitted A, '$abq' against the proved A"
fi

exit $fail
