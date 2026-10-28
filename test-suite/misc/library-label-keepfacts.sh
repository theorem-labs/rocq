#!/usr/bin/env bash
# D18 (dispatch://INFRA-361), Astra review 2 blockers 1 and 3: the [keepfacts]
# segment that -location-free-label writes, read through
# `rocq-library-label --axiom-report-json` (schema version 2).
#
# B3 (assumption closure). A's lemma `l` is a Qed proof in both variants; in `use`
# its proof starts to use A's existing axiom `ax`. Label v2b blinds the opaque body,
# so A's label is equal across the edit, and every declaration status is unchanged,
# so only a real closure tells the edits apart: A's "assumptions" gain `ax`, and so do
# those of D, which proves its lemma with A.l.
#
# B1 (opacity a strategy command saw). A's `c` is Admitted in `adm` and a Qed proof
# in `qed`; the label is equal across. B runs `Transparent A.c.`: it compiles against
# `adm` and records (c, opaque=false), and it fails against `qed`. B2 runs
# `Fail Transparent A.c.` against `qed` and records (c, opaque=true): a rolled-back
# command's outcome still depended on what it saw.
#
# Control: a file compiled without the flag has no segment ("assumptions" and
# "opacity_queries" are null).

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _kfacts
mkdir -p _kfacts/{noax,use,dnoax,duse,adm,qed,badm,bqed,b2qed,off}

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

# --- S1 field: an Include in a submodule copies A's axiom c; its canonical name stays in A ---
mkdir -p _kfacts/inc
printf 'Require A.\nModule M.\nInclude A.\nEnd M.\n' > _kfacts/inc/E.v
rocq c -q -location-free-label -R _kfacts/adm A -R _kfacts/inc Edep _kfacts/inc/E.v
cf=$(field _kfacts/inc/E.vo copied_from_libraries)
if [ "$cf" = "[\"$alib\"]" ]; then
  pass "S1: E's copied_from_libraries names A for the Include in submodule M: $cf"
else
  bad "S1: E's copied_from_libraries: '$cf'"
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
if report _kfacts/noax/A.vo | grep -q '"version":2,'; then
  pass "schema version 2"
else
  bad "the axiom report is not schema version 2"
fi

exit $fail
