#!/usr/bin/env bash
# D18 (dispatch://INFRA-361), review gate 1 F1: an Admitted -> Qed edit inside a
# functor body or a module type moves its library's label (label version 5).
#
# A functor application copies its body's axiom-or-opaque form into the library that
# applies it (kernel/mod_typing.ml), and so do [Declare Module M : T] and
# [Module X : T := ...] for a module type's. There it decides whether the dependent
# compiles ([Transparent R.c] fails on an opaque proof) and what [Print Assumptions]
# says of it, while no axiom report lists the functor's or the module type's
# constants. So the label must not blind the two forms there: up to label version 4 it
# did, a dependent was kept across the edit, and a clean rebuild of that dependent
# failed. The label still blinds them for the library's own signature, where the keep
# rule reads the status off the report (misc/library-label-keepfacts.sh).
#
# Case 1, functor. L declares a functor F whose body holds lemma c, Admitted in `adm`
# and a Qed proof in `qed`. Checks: L's label differs between the two; D, which
# applies F (Module R := L.F L.A0) and runs Transparent R.c (DT) or Opaque R.c (DO),
# compiles against the Admitted L, DT fails against the Qed L (so a kept DT would hide
# a failing build), and each D compiled against the Admitted L is refused by coqc next
# to the Qed L ("inconsistent assumptions": the digest D recorded for L is no longer
# L's); DO compiled against each L has a different label. DI includes F's application
# (Module R. Include L.F L.A0. End R.) and runs Transparent R.c: it fails against the
# Qed L, and DI compiled against the Admitted L is refused next to the Qed L.
# Transitive: L2 only applies F, D2 runs Transparent L2.R.c; L2's label differs between
# the two Ls, and D2 compiled against the Admitted chain is refused next to the Qed
# chain.
#
# Case 2, module type. L declares a module type T holding lemma c, Admitted or Qed.
# Checks: L's label differs; DM (Declare Module M : L.T. Transparent M.c.) compiles
# against the Admitted L, fails against the Qed L, and its object compiled against the
# Admitted L is refused next to the Qed L.
#
# Each refusal check has a control: the same client next to the L the dependent was
# compiled against loads. Every L is checked to carry a label ("label2"), so a label
# that differs is a label, not a fallback to the MD5 of the segment's bytes.

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _flip
mkdir -p _flip

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
# labels2 NAME FILE...: every FILE stores its label ("label2" from --check).
labels2() {
  local name=$1 f k ok=1; shift
  for f in "$@"; do
    k=$("$TOOL" --check "$f" | awk '{print $1}')
    [ "$k" = label2 ] || { ok=0; bad "$name: $f is '$k', not label2"; }
  done
  [ $ok = 0 ] || pass "$name: every L carries its label (label2)"
}
comp() { rocq c -q -location-free-label "$@"; }
# refused CLIENT_DIR ARGS...: compile CLIENT_DIR/C.v with ARGS; "refused" when coqc
# reports inconsistent assumptions, "loads" when it compiles, "error" otherwise.
refused() {
  local d=$1; shift
  if comp "$@" -R "$d" Cl "$d/C.v" > "$d/out" 2>&1; then echo loads
  elif grep -q 'inconsistent assumptions' "$d/out"; then echo refused
  else echo error; fi
}
expect_refused() { # NAME CLIENT_DIR ARGS...
  local name=$1; shift
  local r; r=$(refused "$@")
  if [ "$r" = refused ]; then pass "$name: refused next to the Qed library"
  else bad "$name: expected refused next to the Qed library, got $r: $(tr '\n' ' ' < "$1/out")"; fi
}
expect_loads() { # NAME CLIENT_DIR ARGS...
  local name=$1; shift
  local r; r=$(refused "$@")
  if [ "$r" = loads ]; then pass "$name: control, loads next to the library it was compiled against"
  else bad "$name: control expected to load, got $r: $(tr '\n' ' ' < "$1/out")"; fi
}
client() { mkdir -p "$1"; printf 'Require %s.\n' "$2" > "$1/C.v"; }

# --- Case 1: functor ---
F=_flip/functor
mkdir -p $F/{adm,qed,dt_adm,dt_qed,do_adm,do_qed,di_adm,di_qed,l2_adm,l2_qed,d2_adm}
head='Module Type S. End S.
Module F (X : S).'
tail='End F.
Module A0. End A0.'
printf '%s\nLemma c : True.\nAdmitted.\n%s\n' "$head" "$tail" > $F/adm/L.v
printf '%s\nLemma c : True.\nProof. exact I. Qed.\n%s\n' "$head" "$tail" > $F/qed/L.v
comp -R $F/adm Lib $F/adm/L.v
comp -R $F/qed Lib $F/qed/L.v
la=$(label $F/adm/L.vo); lq=$(label $F/qed/L.vo)
labels2 "functor" $F/adm/L.vo $F/qed/L.vo
if [ "$la" != "$lq" ]; then pass "functor: L's label differs across c Admitted->Qed in F's body"
else bad "functor: L's label is equal across c Admitted->Qed in F's body ($la)"; fi

printf 'Require Lib.L.\nModule R := Lib.L.F Lib.L.A0.\nTransparent R.c.\n' > $F/dt_adm/D.v
cp $F/dt_adm/D.v $F/dt_qed/D.v
printf 'Require Lib.L.\nModule R := Lib.L.F Lib.L.A0.\nOpaque R.c.\n' > $F/do_adm/D.v
cp $F/do_adm/D.v $F/do_qed/D.v
comp -R $F/adm Lib -R $F/dt_adm Dep $F/dt_adm/D.v
comp -R $F/adm Lib -R $F/do_adm Dep $F/do_adm/D.v
comp -R $F/qed Lib -R $F/do_qed Dep $F/do_qed/D.v
if comp -R $F/qed Lib -R $F/dt_qed Dep $F/dt_qed/D.v 2> $F/dt_qed/err; then
  bad "functor: Transparent R.c compiled against the Qed L"
elif tr '\n' ' ' < $F/dt_qed/err | grep -q 'Cannot make .* transparent because it was declared  *opaque'; then
  pass "functor: Transparent R.c fails against the Qed L (Cannot make R.c transparent: declared opaque), so a kept DT would hide a failing build"
else
  bad "functor: Transparent R.c fails against the Qed L for another reason: $(tr '\n' ' ' < $F/dt_qed/err)"
fi
if [ "$(label $F/do_adm/D.vo)" != "$(label $F/do_qed/D.vo)" ]; then
  pass "functor: DO (Opaque R.c) compiled against each L has a different label"
else bad "functor: DO's label is equal against both Ls"; fi
client $F/c_dt_ok Dep.D; expect_loads "functor DT" $F/c_dt_ok -R $F/adm Lib -R $F/dt_adm Dep
client $F/c_dt Dep.D; expect_refused "functor DT (Transparent R.c)" $F/c_dt -R $F/qed Lib -R $F/dt_adm Dep
client $F/c_do_ok Dep.D; expect_loads "functor DO" $F/c_do_ok -R $F/adm Lib -R $F/do_adm Dep
client $F/c_do Dep.D; expect_refused "functor DO (Opaque R.c)" $F/c_do -R $F/qed Lib -R $F/do_adm Dep

# DI: an Include of F's application copies c's form into R like the application does.
printf 'Require Lib.L.\nModule R.\nInclude Lib.L.F Lib.L.A0.\nEnd R.\nTransparent R.c.\n' > $F/di_adm/D.v
cp $F/di_adm/D.v $F/di_qed/D.v
comp -R $F/adm Lib -R $F/di_adm Dep $F/di_adm/D.v
if comp -R $F/qed Lib -R $F/di_qed Dep $F/di_qed/D.v 2> $F/di_qed/err; then
  bad "functor DI: Include L.F L.A0; Transparent R.c compiled against the Qed L"
elif tr '\n' ' ' < $F/di_qed/err | grep -q 'Cannot make .* transparent because it was declared  *opaque'; then
  pass "functor DI: Include L.F L.A0; Transparent R.c fails against the Qed L (declared opaque), so a kept DI would hide a failing build"
else
  bad "functor DI: Transparent R.c fails against the Qed L for another reason: $(tr '\n' ' ' < $F/di_qed/err)"
fi
client $F/c_di_ok Dep.D; expect_loads "functor DI" $F/c_di_ok -R $F/adm Lib -R $F/di_adm Dep
client $F/c_di Dep.D; expect_refused "functor DI (Include L.F L.A0; Transparent R.c)" $F/c_di -R $F/qed Lib -R $F/di_adm Dep

# Transitive: L2 only applies F; D2 depends on L2 alone.
printf 'Require Lib.L.\nModule R := Lib.L.F Lib.L.A0.\n' > $F/l2_adm/L2.v
cp $F/l2_adm/L2.v $F/l2_qed/L2.v
printf 'Require Mid.L2.\nTransparent Mid.L2.R.c.\n' > $F/d2_adm/D2.v
comp -R $F/adm Lib -R $F/l2_adm Mid $F/l2_adm/L2.v
comp -R $F/qed Lib -R $F/l2_qed Mid $F/l2_qed/L2.v
comp -R $F/adm Lib -R $F/l2_adm Mid -R $F/d2_adm Top $F/d2_adm/D2.v
if [ "$(label $F/l2_adm/L2.vo)" != "$(label $F/l2_qed/L2.vo)" ]; then
  pass "functor, transitive: L2 (which only applies F) has a different label against each L"
else bad "functor, transitive: L2's label is equal against both Ls"; fi
client $F/c_d2_ok Top.D2; expect_loads "functor, transitive D2" $F/c_d2_ok -R $F/adm Lib -R $F/l2_adm Mid -R $F/d2_adm Top
client $F/c_d2 Top.D2; expect_refused "functor, transitive D2 (Transparent L2.R.c)" $F/c_d2 -R $F/qed Lib -R $F/l2_qed Mid -R $F/d2_adm Top

# --- Case 2: module type ---
M=_flip/modtype
mkdir -p $M/{adm,qed,dm_adm,dm_qed}
printf 'Module Type T.\nLemma c : True.\nAdmitted.\nEnd T.\n' > $M/adm/L.v
printf 'Module Type T.\nLemma c : True.\nProof. exact I. Qed.\nEnd T.\n' > $M/qed/L.v
comp -R $M/adm Lib $M/adm/L.v
comp -R $M/qed Lib $M/qed/L.v
la=$(label $M/adm/L.vo); lq=$(label $M/qed/L.vo)
labels2 "module type" $M/adm/L.vo $M/qed/L.vo
if [ "$la" != "$lq" ]; then pass "module type: L's label differs across c Admitted->Qed in T"
else bad "module type: L's label is equal across c Admitted->Qed in T ($la)"; fi
printf 'Require Lib.L.\nDeclare Module M : Lib.L.T.\nTransparent M.c.\n' > $M/dm_adm/D.v
cp $M/dm_adm/D.v $M/dm_qed/D.v
comp -R $M/adm Lib -R $M/dm_adm Dep $M/dm_adm/D.v
if comp -R $M/qed Lib -R $M/dm_qed Dep $M/dm_qed/D.v 2> $M/dm_qed/err; then
  bad "module type: Transparent M.c compiled against the Qed L"
elif tr '\n' ' ' < $M/dm_qed/err | grep -q 'Cannot make .* transparent because it was declared  *opaque'; then
  pass "module type: Transparent M.c fails against the Qed L (Cannot make M.c transparent: declared opaque), so a kept DM would hide a failing build"
else
  bad "module type: Transparent M.c fails against the Qed L for another reason: $(tr '\n' ' ' < $M/dm_qed/err)"
fi
client $M/c_dm_ok Dep.D; expect_loads "module type DM" $M/c_dm_ok -R $M/adm Lib -R $M/dm_adm Dep
client $M/c_dm Dep.D; expect_refused "module type DM (Declare Module M : L.T)" $M/c_dm -R $M/qed Lib -R $M/dm_adm Dep

exit $fail
