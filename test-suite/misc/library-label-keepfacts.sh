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
# sees ax. E's closures come from one walk over the stored closures and equal the full
# walk's (ROCQ_KEEPFACTS_FULL_WALK=1). Three more cases of the stored-closure walk: a
# keep round (D compiled against an Admitted A, E against the proved A and the old D:
# E's closure strictly contains the full walk's); the fallback (a match on an empty
# type over an axiom: each closure by its own walk, equal to the full walk's); and a
# closure reached only through a foreign inductive's constructor.
#
# B1 (opacity a command saw). A's `c` is Admitted in `adm` and a Qed proof in `qed`;
# the label is equal across. B runs `Transparent A.c.`: it compiles against `adm` and
# records (c, opaque=false), and it fails against `qed`. B2 runs
# `Fail Transparent A.c.` against `qed` and records (c, opaque=true): a rolled-back
# command's outcome still depended on what it saw. BX extracts A.c, which tells an
# axiom from an opaque proof too, and records (c, opaque=false) against `adm`. BXB
# extracts opaque proofs whose bodies extraction reads: a lemma in a functor body
# (`Extraction A.F`, which the global environment does not hold) and one in a sealed
# module's implementation (`Extraction A.M`): each records opaque=true. BXH seals a
# functor application to a module type that omits its lemma (`Module X : A.S :=
# A.F A.A0.` in H): H's foreign_opaque_libraries names A, and a JSON extraction of
# H.X, which rebuilds X from that expression, records X.fc opaque=true under H. BN runs
# `Transparent Nat.add.`, a transparent definition, which cannot become an axiom or an
# opaque proof while its library's label stays equal: nothing is recorded.
#
# Control: a file compiled without the flag has no segment ("assumptions" and
# "opacity_queries" are null), and neither has a .vos, even one with no proof left
# out; a byte flipped inside a real segment reads as absent, with the reason on
# standard error.

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
# E's closures come from one walk that takes D.d's closure from D's keepfacts
# (ROCQ_KEEPFACTS_DEBUG=1 says so on standard error), and they are the closures each
# root's own walk through every body gives (ROCQ_KEEPFACTS_FULL_WALK=1).
mkdir -p _kfacts/edbg _kfacts/efull
cp _kfacts/euse/E.v _kfacts/edbg/E.v; cp _kfacts/euse/E.v _kfacts/efull/E.v
ROCQ_KEEPFACTS_DEBUG=1 rocq c -q -location-free-label -R _kfacts/use A -R _kfacts/duse Ddep -R _kfacts/edbg Edep \
  _kfacts/edbg/E.v 2> _kfacts/edbg/debug
ROCQ_KEEPFACTS_FULL_WALK=1 rocq c -q -location-free-label -R _kfacts/use A -R _kfacts/duse Ddep -R _kfacts/efull Edep \
  _kfacts/efull/E.v
if grep -q '^\[keepfacts\] Edep\.E: [0-9]* roots, one walk of [0-9]* objects, [1-9][0-9]* foreign stored closures$' \
     _kfacts/edbg/debug; then
  pass "B3: E's closures come from one walk over D's stored closures: $(cat _kfacts/edbg/debug)"
else
  bad "B3: E's closures did not come from stored closures: '$(cat _kfacts/edbg/debug)'"
fi
ef=$(field _kfacts/efull/E.vo assumptions); eu=$(field _kfacts/euse/E.vo assumptions)
if [ -n "$eu" ] && [ "$ef" = "$eu" ]; then
  pass "B3: every root's own walk gives E the same closures: $ef"
else
  bad "B3: E's closures by every root's own walk '$ef' differ from the stored-closure walk's '$eu'"
fi
# includes KEYS1 KEYS2: every key of the JSON list KEYS2 is in the JSON list KEYS1.
includes() {
  local k
  for k in $(printf '%s' "$2" | tr -d '[]' | tr ',' ' '); do
    printf '%s' "$1" | grep -qF -- "$k" || return 1
  done
}

# A keep round: D is compiled against A with c Admitted, so D.d's closure lists A.c; A is
# rebuilt with c proved (an equal label, so the old D still loads), and E is compiled
# against that A and the old D. E's closure takes D.d's stored closure, which still lists
# A.c: a strict superset of the closure a walk of the current bodies gives
# (ROCQ_KEEPFACTS_FULL_WALK=1), which is empty. The keep rule keeps such a D only when no
# closure of its in-tree dependencies grew, so a stored closure is never smaller than the
# current one (vernac/keepFacts.ml, fast_closures).
K=_kfacts/kr
mkdir -p $K/{aadm,aqed,d,e,efull}
printf 'Lemma c : True.\nAdmitted.\n' > $K/aadm/A.v
printf 'Lemma c : True.\nProof. exact I. Qed.\n' > $K/aqed/A.v
printf 'Require A.\nLemma d : True.\nProof. exact A.c. Qed.\n' > $K/d/D.v
printf 'Require Ddep.D.\nLemma e : True.\nProof. exact Ddep.D.d. Qed.\n' > $K/e/E.v
cp $K/e/E.v $K/efull/E.v
rocq c -q -location-free-label -R $K/aadm A $K/aadm/A.v
rocq c -q -location-free-label -R $K/aqed A $K/aqed/A.v
rocq c -q -location-free-label -R $K/aadm A -R $K/d Ddep $K/d/D.v
rocq c -q -location-free-label -R $K/aqed A -R $K/d Ddep -R $K/e Edep $K/e/E.v
ROCQ_KEEPFACTS_FULL_WALK=1 rocq c -q -location-free-label -R $K/aqed A -R $K/d Ddep -R $K/efull Edep $K/efull/E.v
kd=$(closure $K/d/D.vo d); ke=$(closure $K/e/E.vo e); kf=$(closure $K/efull/E.vo e)
if [ "$(label $K/aadm/A.vo)" = "$(label $K/aqed/A.vo)" ] && printf '%s' "$kd" | grep -q 'axiom:[^"]*\.c"' \
   && [ "$ke" = "$kd" ] && includes "$ke" "$kf" && [ "$ke" != "$kf" ]; then
  pass "B3, keep round: E's closure over the old D's stored closure ($ke) strictly contains the current bodies' ('$kf')"
else
  bad "B3, keep round: A's labels $(label $K/aadm/A.vo) $(label $K/aqed/A.vo), D.d '$kd', E.e stored-closure '$ke', full walk '$kf'"
fi

# The fallback: a match on an empty type over an axiom makes what one shared walk reaches
# depend on the order it visits objects in, so the library's closures are each computed
# by their own walk; ROCQ_KEEPFACTS_DEBUG=1 says so, and they are the full walk's.
FB=_kfacts/fb
mkdir -p $FB/dbg $FB/full
printf 'Lemma imp : False.\nAdmitted.\nLemma u : 0 = 1.\nProof. exact (match imp return 0 = 1 with end). Qed.\n' > $FB/dbg/F.v
cp $FB/dbg/F.v $FB/full/F.v
ROCQ_KEEPFACTS_DEBUG=1 rocq c -q -location-free-label -R $FB/dbg Fb $FB/dbg/F.v 2> $FB/dbg/debug
ROCQ_KEEPFACTS_FULL_WALK=1 rocq c -q -location-free-label -R $FB/full Fb $FB/full/F.v
fd=$(field $FB/dbg/F.vo assumptions); ff=$(field $FB/full/F.vo assumptions); fu=$(closure $FB/dbg/F.vo u)
if grep -q '^\[keepfacts\] Fb\.F: [0-9]* roots, each by its own walk (a match on an empty type over an axiom)$' $FB/dbg/debug \
   && printf '%s' "$fu" | grep -q 'axiom:[^"]*\.imp"' && [ "$fd" = "$ff" ]; then
  pass "B3, fallback: $(cat $FB/dbg/debug); closures equal the full walk's: $fd"
else
  bad "B3, fallback: debug '$(cat $FB/dbg/debug)', closures '$fd', full walk '$ff', u '$fu'"
fi

# A stored closure reached through a foreign inductive and its constructor: D's t has a
# constructor mk2 whose type mentions A.ax, and E proves D.t with the other constructor,
# mk, so the block's stored closure is E's only path to A.ax. E's closure is D.t's stored
# closure (one walk, stored closures used) and equals the full walk's.
IN=_kfacts/ind
mkdir -p $IN/{d,e,efull}
printf 'Require A.\nInductive t : Prop := mk : t | mk2 : A.ax = A.ax -> t.\n' > $IN/d/D.v
printf 'Require Ddep.D.\nLemma e : Ddep.D.t.\nProof. exact Ddep.D.mk. Qed.\n' > $IN/e/E.v
cp $IN/e/E.v $IN/efull/E.v
rocq c -q -location-free-label -R _kfacts/use A -R $IN/d Ddep $IN/d/D.v
ROCQ_KEEPFACTS_DEBUG=1 rocq c -q -location-free-label -R _kfacts/use A -R $IN/d Ddep -R $IN/e Edep $IN/e/E.v \
  2> $IN/e/debug
ROCQ_KEEPFACTS_FULL_WALK=1 rocq c -q -location-free-label -R _kfacts/use A -R $IN/d Ddep -R $IN/efull Edep $IN/efull/E.v
it=$(closure $IN/d/D.vo t); ie=$(closure $IN/e/E.vo e); if_=$(closure $IN/efull/E.vo e)
if printf '%s' "$it" | grep -q 'axiom:[^"]*\.ax"' && [ "$ie" = "$it" ] && [ "$ie" = "$if_" ] \
   && grep -q '^\[keepfacts\] Edep\.E: [0-9]* roots, one walk of [0-9]* objects, [1-9][0-9]* foreign stored closures$' $IN/e/debug; then
  pass "B3, inductive: E.e's closure through D.mk is D.t's stored closure and the full walk's: $ie ($(cat $IN/e/debug))"
else
  bad "B3, inductive: D.t '$it', E.e '$ie', full walk '$if_', debug '$(cat $IN/e/debug)'"
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
# BXB: with AccessOpaque (the default) an extraction reads an opaque proof's body: the
# query is opaque=true, with the library holding the constant read. Two cases only the
# body-read hook can record as opaque: a lemma of a functor's body (F.fc), which the
# global environment does not hold, so the extraction's first record (of the body the
# environment gives) records nothing; and a lemma of a sealed module's implementation
# (M.sn), whose signature constant is an axiom, so that record says opaque=false.
mkdir -p _kfacts/xb/{a,b,bs}
printf 'Module Type S. End S.\nModule F (X : S). Lemma fc : nat. Proof. exact 0. Qed. End F.\nModule Type T2. Parameter sn : nat. End T2.\nModule M : T2. Lemma sn : nat. Proof. exact 0. Qed. End M.\n' \
  > _kfacts/xb/a/A.v
printf 'From Corelib Require Extraction.\nRequire A.\nExtraction A.F.\n' > _kfacts/xb/b/B.v
printf 'From Corelib Require Extraction.\nRequire A.\nExtraction A.M.\n' > _kfacts/xb/bs/B.v
rocq c -q -location-free-label -R _kfacts/xb/a A _kfacts/xb/a/A.v
rocq c -q -location-free-label -R _kfacts/xb/a A -R _kfacts/xb/b Bdep _kfacts/xb/b/B.v > /dev/null
rocq c -q -location-free-label -R _kfacts/xb/a A -R _kfacts/xb/bs Bdep _kfacts/xb/bs/B.v > /dev/null
xlib=$(report _kfacts/xb/a/A.vo | sed -n 's/.*"library":"\([^"]*\)".*/\1/p')
qb=$(field _kfacts/xb/b/B.vo opacity_queries); qs=$(field _kfacts/xb/bs/B.vo opacity_queries)
if [ "$qb" = "[{\"constant\":\"$xlib.F.fc\",\"library\":\"$xlib\",\"opaque\":true}]" ]; then
  pass "B1: an extraction that reads the functor-body lemma A.F.fc's opaque body records it opaque: $qb"
else
  bad "B1: BXB's opacity_queries for the functor-body A.F.fc: '$qb'"
fi
if [ "$qs" = "[{\"constant\":\"$xlib.M.sn\",\"library\":\"$xlib\",\"opaque\":true}]" ]; then
  pass "B1: an extraction that reads sealed A.M.sn's opaque body records it opaque: $qs"
else
  bad "B1: BXB's opacity_queries for the sealed A.M.sn: '$qs'"
fi
# BXH: H seals a functor application to a module type that omits its opaque lemma,
# `Module X : A.S := A.F A.A0.`. X keeps the expression as its implementation and S as
# its signature, so no constant of H holds a reference into A's opaque table; H's
# report still names A, from the module paths of that implementation. An extraction
# to a language other than OCaml (JSON here) rebuilds X from the expression and reads
# A.F.fc's body as X.fc: the query is opaque=true, under H, whose
# foreign_opaque_libraries then makes the keep rule check A.
XH=_kfacts/xh
mkdir -p $XH/a $XH/h $XH/b
printf 'Module Type S. End S.\nModule F (X : S). Lemma fc : nat. Proof. exact 0. Qed. End F.\nModule A0. End A0.\n' \
  > $XH/a/A.v
printf 'Require A.\nModule X : A.S := A.F A.A0.\n' > $XH/h/H.v
printf 'From Corelib Require Extraction.\nRequire Hdep.H.\nExtraction Language JSON.\nExtraction Hdep.H.X.\n' > $XH/b/B.v
rocq c -q -location-free-label -R $XH/a A $XH/a/A.v
rocq c -q -location-free-label -R $XH/a A -R $XH/h Hdep $XH/h/H.v
xhlib=$(report $XH/a/A.vo | sed -n 's/.*"library":"\([^"]*\)".*/\1/p')
hfor=$(field $XH/h/H.vo foreign_opaque_libraries)
if [ "$hfor" = "[\"$xhlib\"]" ]; then
  pass "BXH: H (Module X : A.S := A.F A.A0) names A in foreign_opaque_libraries: $hfor"
else
  bad "BXH: H's foreign_opaque_libraries (Module X : A.S := A.F A.A0): '$hfor', expected [\"$xhlib\"]"
fi
if rocq c -q -location-free-label -R $XH/a A -R $XH/h Hdep -R $XH/b Bdep $XH/b/B.v > $XH/b/out 2>&1; then
  qh=$(field $XH/b/B.vo opacity_queries)
  if [ "$qh" = '[{"constant":"Hdep.H.X.fc","library":"Hdep.H","opaque":true}]' ]; then
    pass "BXH: the JSON extraction of H.X reads A.F.fc's body and records it opaque under H: $qh"
  else
    bad "BXH: BXH's opacity_queries for the JSON extraction of H.X: '$qh'"
  fi
else
  bad "BXH: the JSON extraction of Hdep.H.X failed: $(tr '\n' ' ' < $XH/b/out | cut -c1-600)"
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
# A changed byte inside the keepfacts segment of a real .vo: the tool reads the segment
# as absent (both fields null) and says why on standard error, rather than reading
# another value (layout per lib/objFile.ml).
mkdir -p _kfacts/flip
python3 - _kfacts/noax/A.vo _kfacts/flip/A.vo <<'PY'
import struct, sys
b = bytearray(open(sys.argv[1], 'rb').read())
(sp,) = struct.unpack_from(">Q", b, 8)
(n,) = struct.unpack_from(">I", b, sp); off = sp + 4
for _ in range(n):
    (ln,) = struct.unpack_from(">I", b, off); off += 4
    name = bytes(b[off:off+ln]); off += ln
    pos, sz = struct.unpack_from(">QQ", b, off); off += 32
    if name == b"keepfacts":
        b[pos + sz // 2] ^= 0x01
        open(sys.argv[2], 'wb').write(b)
        sys.exit(0)
sys.exit("no keepfacts segment in " + sys.argv[1])
PY
fr=$("$TOOL" --axiom-report-json _kfacts/flip/A.vo 2> _kfacts/flip/err)
if printf '%s' "$fr" | grep -q '"assumptions":null,"opacity_queries":null}$' \
   && grep -q 'keepfacts segment read as absent: its bytes do not match its digest' _kfacts/flip/err; then
  pass "control: a byte flipped in the keepfacts segment reads as absent, with the reason: $(cat _kfacts/flip/err)"
else
  bad "control: the flipped keepfacts segment: report '$fr', stderr '$(cat _kfacts/flip/err)'"
fi

exit $fail
