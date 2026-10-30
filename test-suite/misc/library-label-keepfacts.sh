#!/usr/bin/env bash
# D18 (dispatch://INFRA-361), Astra review 2 blockers 1 and 3: the [keepfacts]
# segment that -location-free-label writes, read through
# `rocq-library-label --axiom-report-json` (schema version 3).
#
# B3 (assumption closure). A's lemma `l` is a Qed proof in both variants; in `use`
# its proof starts to use A's existing axiom `ax`. The label blinds the opaque body,
# so A's label is equal across the edit, and every declaration status is unchanged,
# so only a real closure tells the edits apart: A's "assumptions" gain `ax`, and so do
# those of D, which proves its lemma with A.l, and of E, which proves its lemma with
# D.d (E reaches ax through two libraries' keepfacts). Dx proves the same lemma as D
# against an A compiled without the flag, which has no keepfacts: its closure still
# sees ax.
#
# B1 (opacity a command saw). A's `c` is Admitted in `adm` and a Qed proof in `qed`;
# the label is equal across. B runs `Transparent A.c.`: it compiles against `adm` and
# records (c, opaque=false), and it fails against `qed`. B2 runs
# `Fail Transparent A.c.` against `qed` and records (c, opaque=true): a rolled-back
# command's outcome still depended on what it saw. BX extracts A.c, which tells an
# axiom from an opaque proof too, and records (c, opaque=false) against `adm`. BN
# runs `Transparent Nat.add.`, a transparent definition, which cannot become an axiom
# or an opaque proof while its library's label stays equal: nothing is recorded.
#
# Control: a file compiled without the flag has no segment ("assumptions" and
# "opacity_queries" are null), and neither has a .vos, even one with no proof left
# out.

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _kfacts
mkdir -p _kfacts/{noax,use,dnoax,duse,euse,offa,dx,adm,qed,badm,bqed,b2qed,bx,bn,off,vos}

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
report() { "$TOOL" --axiom-report-json "$1"; }
field() { report "$1" | sed -n "s/.*\"$2\":\(\[[^]]*\]\|{[^}]*}\|null\).*/\1/p"; }
# The closure the report lists for declaration $2 of file $1 ("" when empty).
closure() { field "$1" assumptions | sed -n "s/.*\"[^\"]*\.$2\":\(\[[^]]*\]\).*/\1/p"; }

# --- B3 ---
printf 'Axiom ax : True.\nLemma l : True.\nProof. exact I. Qed.\n' > _kfacts/noax/A.v
printf 'Axiom ax : True.\nLemma l : True.\nProof. exact ax. Qed.\n' > _kfacts/use/A.v
printf 'Require A.\nLemma d : True.\nProof. exact A.l. Qed.\n' > _kfacts/dnoax/D.v
cp _kfacts/dnoax/D.v _kfacts/duse/D.v
rocq c -q -location-free-label -R _kfacts/noax A _kfacts/noax/A.v
rocq c -q -location-free-label -R _kfacts/use A _kfacts/use/A.v
rocq c -q -location-free-label -R _kfacts/noax A -R _kfacts/dnoax Ddep _kfacts/dnoax/D.v
rocq c -q -location-free-label -R _kfacts/use A -R _kfacts/duse Ddep _kfacts/duse/D.v
printf 'Require Ddep.D.\nLemma e : True.\nProof. exact Ddep.D.d. Qed.\n' > _kfacts/euse/E.v
rocq c -q -location-free-label -R _kfacts/use A -R _kfacts/duse Ddep -R _kfacts/euse Edep _kfacts/euse/E.v
cp _kfacts/use/A.v _kfacts/offa/A.v
cp _kfacts/dnoax/D.v _kfacts/dx/D.v
rocq c -q -R _kfacts/offa A _kfacts/offa/A.v
rocq c -q -location-free-label -R _kfacts/offa A -R _kfacts/dx Ddep _kfacts/dx/D.v

if [ "$(label _kfacts/noax/A.vo)" = "$(label _kfacts/use/A.vo)" ]; then
  pass "B3: A's label is equal when l's opaque proof starts to use ax"
else
  bad "B3: A's label differs across the opaque-proof edit (expected equal under v2b)"
fi
a1=$(field _kfacts/noax/A.vo assumptions)
l1=$(closure _kfacts/noax/A.vo l); l2=$(closure _kfacts/use/A.vo l)
x1=$(closure _kfacts/noax/A.vo ax)
d1=$(closure _kfacts/dnoax/D.vo d); d2=$(closure _kfacts/duse/D.vo d)
case "$a1" in \{*) pass "B3: A has per-declaration closures: $a1";; *) bad "B3: A has no closures: '$a1'";; esac
if printf '%s' "$x1" | grep -q 'axiom:[^"]*\.ax"'; then
  pass "B3: the axiom ax's own closure is itself: $x1"
else
  bad "B3: ax's closure: '$x1'"
fi
if [ -z "$l1" ] && printf '%s' "$l2" | grep -q 'axiom:[^"]*\.ax"'; then
  pass "B3: l's closure grows from empty to ax when its opaque proof uses ax: '$l1' -> $l2"
else
  bad "B3: l's closure does not track its opaque proof: '$l1' -> '$l2'"
fi
if [ -z "$d1" ] && printf '%s' "$d2" | grep -q 'axiom:[^"]*\.ax"'; then
  pass "B3: D.d's closure gains ax through A.l's opaque proof: '$d1' -> $d2"
else
  bad "B3: D.d's closure does not see ax through A.l: '$d1' -> '$d2'"
fi
e2=$(closure _kfacts/euse/E.vo e)
if [ -n "$d2" ] && [ "$e2" = "$d2" ]; then
  pass "B3: E.e's closure is D.d's, through D's and A's keepfacts: $e2"
else
  bad "B3: E.e's closure '$e2' is not D.d's '$d2'"
fi
dx=$(closure _kfacts/dx/D.vo d)
if [ -n "$d2" ] && [ "$dx" = "$d2" ]; then
  pass "B3: against an A without keepfacts, D.d's closure is still $dx"
else
  bad "B3: against an A without keepfacts, D.d's closure is '$dx', not '$d2'"
fi

# --- B1 ---
printf 'Lemma c : True.\nAdmitted.\n' > _kfacts/adm/A.v
printf 'Lemma c : True.\nProof. exact I. Qed.\n' > _kfacts/qed/A.v
printf 'Require A.\nTransparent A.c.\n' > _kfacts/badm/B.v
cp _kfacts/badm/B.v _kfacts/bqed/B.v
printf 'Require A.\nFail Transparent A.c.\n' > _kfacts/b2qed/B.v
rocq c -q -location-free-label -R _kfacts/adm A _kfacts/adm/A.v
rocq c -q -location-free-label -R _kfacts/qed A _kfacts/qed/A.v
rocq c -q -location-free-label -R _kfacts/adm A -R _kfacts/badm Bdep _kfacts/badm/B.v
rocq c -q -location-free-label -R _kfacts/qed A -R _kfacts/b2qed Bdep _kfacts/b2qed/B.v

if [ "$(label _kfacts/adm/A.vo)" = "$(label _kfacts/qed/A.vo)" ]; then
  pass "B1: A's label is equal across c Admitted->Qed"
else
  bad "B1: A's label differs across c Admitted->Qed (expected equal under v2b)"
fi
if rocq c -q -location-free-label -R _kfacts/qed A -R _kfacts/bqed Bdep _kfacts/bqed/B.v 2>/dev/null; then
  bad "B1: Transparent A.c compiled against the Qed A (the case the keep rule must rebuild for)"
else
  pass "B1: Transparent A.c fails against the Qed A, so a kept B would hide a failing build"
fi
alib=$(report _kfacts/adm/A.vo | sed -n 's/.*"library":"\([^"]*\)".*/\1/p')
q1=$(field _kfacts/badm/B.vo opacity_queries); q2=$(field _kfacts/b2qed/B.vo opacity_queries)
if [ "$q1" = "[{\"constant\":\"$alib.c\",\"library\":\"$alib\",\"opaque\":false}]" ]; then
  pass "B1: B records the opacity it saw against the Admitted A: $q1"
else
  bad "B1: B's opacity_queries against the Admitted A: '$q1'"
fi
if [ "$q2" = "[{\"constant\":\"$alib.c\",\"library\":\"$alib\",\"opaque\":true}]" ]; then
  pass "B1: B2 records (Fail-wrapped) the opacity it saw against the Qed A: $q2"
else
  bad "B1: B2's opacity_queries against the Qed A: '$q2'"
fi
# The keep rule looks the recorded name up in the owner's axiom_blind list.
st_adm=$(report _kfacts/adm/A.vo); st_qed=$(report _kfacts/qed/A.vo)
if printf '%s' "$st_adm" | grep -q "{\"constant\":\"$alib.c\",\"status\":\"axiom\"}" \
   && printf '%s' "$st_qed" | grep -q "{\"constant\":\"$alib.c\",\"status\":\"proof\"}"; then
  pass "B1: A's axiom_blind lists $alib.c under the recorded name, axiom then proof"
else
  bad "B1: A's axiom_blind does not list $alib.c as the opacity record names it"
fi

# BX: extraction tells A.c's axiom from an opaque proof (an axiom to realize, an opaque
# proof accessed: either warning can be an error), so it records what it saw too.
printf 'From Corelib Require Extraction.\nRequire A.\nExtraction A.c.\n' > _kfacts/bx/B.v
rocq c -q -location-free-label -R _kfacts/adm A -R _kfacts/bx Bdep _kfacts/bx/B.v > /dev/null
qx=$(field _kfacts/bx/B.vo opacity_queries)
if [ "$qx" = "[{\"constant\":\"$alib.c\",\"library\":\"$alib\",\"opaque\":false}]" ]; then
  pass "B1: an extraction of A.c records the axiom it saw against the Admitted A: $qx"
else
  bad "B1: BX's opacity_queries against the Admitted A: '$qx'"
fi
# BN: a transparent definition is neither form the label blinds into one: no record,
# or every later keep check would find it mismatched and rebuild BN forever.
printf 'Transparent Nat.add.\nDefinition n := 0.\n' > _kfacts/bn/B.v
rocq c -q -location-free-label -R _kfacts/bn Bdep _kfacts/bn/B.v
qn=$(field _kfacts/bn/B.vo opacity_queries)
if [ "$qn" = "[]" ]; then
  pass "B1: Transparent Nat.add (a transparent definition) records nothing"
else
  bad "B1: Transparent Nat.add recorded: '$qn'"
fi

# --- control ---
cp _kfacts/noax/A.v _kfacts/off/A.v
rocq c -q -R _kfacts/off A _kfacts/off/A.v
o1=$(field _kfacts/off/A.vo assumptions); o2=$(field _kfacts/off/A.vo opacity_queries)
if [ "$o1" = null ] && [ "$o2" = null ]; then
  pass "control: a file compiled without -location-free-label has no keepfacts"
else
  bad "control: off file has keepfacts: assumptions=$o1 opacity_queries=$o2"
fi
# A .vos gets no segment, even one that leaves no proof out (it has no opaque proof).
printf 'Axiom ax : True.\nDefinition d := I.\n' > _kfacts/vos/A.v
rocq c -q -vos -location-free-label -R _kfacts/vos A _kfacts/vos/A.v
v1=$(field _kfacts/vos/A.vos assumptions); v2=$(field _kfacts/vos/A.vos opacity_queries)
if [ -f _kfacts/vos/A.vos ] && [ "$v1" = null ] && [ "$v2" = null ]; then
  pass "control: a .vos with no proof left out has no keepfacts"
else
  bad "control: the .vos has keepfacts: assumptions=$v1 opacity_queries=$v2"
fi
r=$(report _kfacts/noax/A.vo)
if printf '%s' "$r" | grep -q '"version":3,' && ! printf '%s' "$r" | grep -q copied_from_libraries; then
  pass "schema version 3, with no copied_from_libraries"
else
  bad "the axiom report is not schema version 3: $r"
fi

exit $fail
