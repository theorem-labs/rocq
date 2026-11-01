#!/usr/bin/env bash
# An error text must not tell a foreign opaque proof from an axiom.
#
# Environ.constant_value_in (and EConstr's, and CClosure's) raised
# NotEvaluableConst Opaque for an opaque proof and NotEvaluableConst NoBody for an
# axiom. No catch tells them apart, but some callers let the exception escape a tactic
# (Tacred.value_of_evaluable_ref behind `unfold c at n`, Eauto.unfold_head behind
# `autounfold_one`, Rewrite.unfold_match, Recdef's proj1_sig), and with no printer
# registered its text shows the payload ("Uncaught exception
# Environ.NotEvaluableConst(1)" against "(0)"). Ltac2 can turn that text into a string
# (Control.print_err, Message.to_string) and succeed or fail on it, so a dependent B
# kept across an `Admitted -> Qed` of a foreign constant (which keeps the foreign
# library's label) could compile where its clean rebuild fails. An opaque proof now
# raises NoBody as an axiom does.
#
# A's `c` is Admitted in `adm` and proved in `qed` (equal labels). Each B compares the
# error text of a tactic on A.c with the text of the same tactic on a local axiom, and
# fails when they differ, or when either tactic succeeds, since a tactic that stops
# failing has no error text to compare: B_unfold with `unfold _ at 1`, B_auto with
# `autounfold_one`. A control, B_succeed, runs the same comparison on two tactics that
# succeed, and must fail with that message.
#
# The three evaluators are also called one by one, by a findlib plugin built here,
# kferr, whose Ltac2 externals return what each one does with a constant:
# env_value calls Environ.constant_value_in (kernel/environ.ml), econstr_value
# EConstr.constant_value_in (engine/eConstr.ml), and closure_value asks CClosure to
# unfold the constant (kernel/cClosure.ml). CClosure's own constant_value_in is local
# to its lookup table, which reads every NotEvaluableConst other than a primitive's or
# a rewrite symbol's as "no body", so its payload never leaves the module: what can be
# checked there is what the lookup decides. B_eval prints each result for A.c, for the
# local axiom, and for a local transparent definition, which each of them must
# evaluate (so the externals really reach the evaluators).
#
# Checks: A's two files carry a label ("label2", non-empty) and the labels are equal;
# each B compiles against both A; the text it prints for A.c is the same against both
# A and the same as for the local axiom; B_succeed fails with the comparison's message;
# B_eval compiles against both A; env_value and econstr_value each raise
# NotEvaluableConst on A.c with one text against both A, the same as on the axiom;
# closure_value unfolds none of them; and all three evaluate the definition.

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _errtext
mkdir -p _errtext/{adm,qed,pkg/kferr}

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
# label FILE: the label `rocq-library-label --check` prints for FILE; fails, saying
# why, when the tool fails or FILE carries no label.
label() {
  local out
  out=$("$TOOL" --check "$1") || { echo "rocq-library-label --check $1 failed" >&2; return 1; }
  case "$out" in
    "label2 "?*) printf '%s\n' "${out#label2 }" ;;
    *) echo "$1 carries no label: '$out'" >&2; return 1 ;;
  esac
}
comp() { rocq c -q -location-free-label "$@"; }

D=_errtext
# The plugin.
cat > $D/pkg/kferr/META <<'EOF'
requires = "rocq-runtime.plugins.ltac2"
plugin(native) = "p.cmxs"
EOF
cat > $D/pkg/kferr/p.ml <<'EOF'
open Ltac2_plugin

(* What [f ()] did: "returned a value", or the text of the exception it
   raised as [Printexc] gives it with no printer registered (the text an
   escaping exception shows). *)
let outcome f = match f () with
  | _ -> "returned a value"
  | exception e -> Printexc.to_string e

let ext name f =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kferr"; mltac_tactic = name }
    Tac2externals.(Tac2ffi.constr @-> eret Tac2ffi.string)
    (fun c env sigma ->
       match EConstr.kind sigma c with
       | Constr.Const (cst, u) -> f env sigma cst u
       | _ -> "not a constant")

let () = ext "env_value" (fun env sigma cst u ->
    outcome (fun () -> Environ.constant_value_in env (cst, EConstr.EInstance.kind sigma u)))

let () = ext "econstr_value" (fun env sigma cst u ->
    outcome (fun () -> EConstr.constant_value_in env sigma (cst, u)))

let () = ext "closure_value" (fun env sigma cst u ->
    let infos = CClosure.create_clos_infos RedFlags.all env in
    let key = Names.ConstKey (cst, EConstr.EInstance.kind sigma u) in
    match CClosure.unfold_ref_with_args infos (CClosure.create_tab ()) key CClosure.empty_stack with
    | Some _ -> "unfolds"
    | None -> "does not unfold"
    | exception e -> Printexc.to_string e)
EOF
( cd $D/pkg/kferr && ocamlfind ocamlopt -thread -shared -package rocq-runtime.plugins.ltac2 -o p.cmxs p.ml > build.log 2>&1 ) ||
  { echo "FAIL cannot build the test plugin kferr"; cat $D/pkg/kferr/build.log; exit 1; }
export OCAMLPATH="$PWD/$D/pkg${OCAMLPATH:+:$OCAMLPATH}"

printf 'Lemma c : nat.\nAdmitted.\n' > $D/adm/A.v
printf 'Lemma c : nat.\nProof. exact 0. Qed.\n' > $D/qed/A.v
comp -R $D/adm A $D/adm/A.v
comp -R $D/qed A $D/qed/A.v
ladm=$(label $D/adm/A.vo) || { bad "A (Admitted) has no label"; exit 1; }
lqed=$(label $D/qed/A.vo) || { bad "A (Qed) has no label"; exit 1; }
if [ "$ladm" = "$lqed" ]; then
  pass "A's label is equal across c Admitted -> Qed: $ladm"
else
  bad "A's label differs across c Admitted -> Qed (expected equal): $ladm $lqed"
fi

head='Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Require A.
Axiom loc : nat.
Create HintDb kfa.
Create HintDb kfl.
#[export] Hint Unfold A.c : kfa.
#[export] Hint Unfold loc : kfl.
Ltac2 err_text (t : unit -> unit) : string option :=
  match Control.case t with
  | Val _ => None
  | Err e =>
    match e with
    | Internal err => Some (Message.to_string (Control.print_err err))
    | _ => Some (Message.to_string (Message.of_exn e))
    end
  end.
Ltac2 shown (t : string option) : string :=
  match t with Some s => s | None => "(the tactic succeeded)" end.
Ltac2 same (ta : string option) (tl : string option) :=
  Message.print (Message.concat (Message.of_string "TEXT foreign: ") (Message.of_string (shown ta)));
  Message.print (Message.concat (Message.of_string "TEXT local axiom: ") (Message.of_string (shown tl)));
  match (ta, tl) with
  | (Some a, Some l) =>
    if String.equal a l then ()
    else Control.throw (Tactic_failure (Some (Message.of_string "the error text tells A.c from an axiom")))
  | (_, _) => Control.throw (Tactic_failure (Some (Message.of_string "a tactic that must fail succeeded")))
  end.'

# check NAME TACTIC_ON_A TACTIC_ON_LOC: B, on the goal `A.c = A.c /\ loc = loc`, takes
# the error text of each tactic (each fails, leaving the goal as it was), prints both,
# and fails unless both tactics failed and their texts are equal.
build_check() {
  local name=$1 ta=$2 tl=$3
  local d
  for v in adm qed; do
    d=$D/$name-$v; mkdir -p $d
    { printf '%s\n' "$head"
      printf 'Goal A.c = A.c /\\ loc = loc.\n'
      printf '  let ta := err_text (fun () => %s) in\n' "$ta"
      printf '  let tl := err_text (fun () => %s) in\n' "$tl"
      printf '  same ta tl.\n  split; reflexivity.\nQed.\n'
    } > $d/B.v
    if comp -R $D/$v A -R $d Bdep $d/B.v > $d/out 2>&1; then echo ok > $d/rc; else echo failed > $d/rc; fi
  done
}
check() {
  local name=$1
  build_check "$@"
  local fa fq la lq
  fa=$(sed -n 's/^TEXT foreign: //p' $D/$name-adm/out | tr '\n' ' ')
  fq=$(sed -n 's/^TEXT foreign: //p' $D/$name-qed/out | tr '\n' ' ')
  la=$(sed -n 's/^TEXT local axiom: //p' $D/$name-adm/out | tr '\n' ' ')
  lq=$(sed -n 's/^TEXT local axiom: //p' $D/$name-qed/out | tr '\n' ' ')
  if [ "$(cat $D/$name-adm/rc)" = ok ] && [ "$(cat $D/$name-qed/rc)" = ok ] && [ -n "$fa" ] \
     && [ "$fa" = "$fq" ] && [ "$fa" = "$la" ] && [ "$fa" = "$lq" ] \
     && ! grep -q 'the tactic succeeded' $D/$name-adm/out $D/$name-qed/out; then
    pass "$name: B compiles against both A, both tactics fail, and the error text for A.c is the same against both and the same as for a local axiom: $fa"
  else
    bad "$name: B against the Admitted A: $(cat $D/$name-adm/rc), against the proved A: $(cat $D/$name-qed/rc); A.c's text '$fa' against the Admitted A, '$fq' against the proved A, the local axiom's '$la' / '$lq'; $(tr '\n' ' ' < $D/$name-qed/out | cut -c1-400)"
  fi
}

# `unfold _ at 1` (Tacred.value_of_evaluable_ref).
check B_unfold 'unfold A.c at 1' 'unfold loc at 1'
# `autounfold_one` with a database that names only that constant (Eauto.unfold_head).
check B_auto 'ltac1:(autounfold_one with kfa)' 'ltac1:(autounfold_one with kfl)'

# Control: the comparison refuses two tactics that succeed.
build_check B_succeed '()' '()'
if [ "$(cat $D/B_succeed-adm/rc)" = failed ] && [ "$(cat $D/B_succeed-qed/rc)" = failed ] \
   && grep -q 'a tactic that must fail succeeded' $D/B_succeed-adm/out \
   && grep -q 'a tactic that must fail succeeded' $D/B_succeed-qed/out; then
  pass "B_succeed: the comparison fails when the tactics succeed"
else
  bad "B_succeed: against the Admitted A $(cat $D/B_succeed-adm/rc), against the proved A $(cat $D/B_succeed-qed/rc): $(tr '\n' ' ' < $D/B_succeed-adm/out | cut -c1-400)"
fi

# B_eval: each evaluator on its own.
evalhead='Require Import Ltac2.Ltac2.
Declare ML Module "kferr".
Require A.
Axiom loc : nat.
Definition def : nat := 0.
Ltac2 @ external env_value : constr -> string := "kferr" "env_value".
Ltac2 @ external econstr_value : constr -> string := "kferr" "econstr_value".
Ltac2 @ external closure_value : constr -> string := "kferr" "closure_value".
Ltac2 show (tag : string) (v : string) :=
  Message.print (Message.concat (Message.of_string tag) (Message.of_string v)).'
for v in adm qed; do
  d=$D/B_eval-$v; mkdir -p $d
  { printf '%s\n' "$evalhead" 'Goal True.'
    for f in env econstr closure; do
      printf '  show "%s A.c: " (%s_value constr:(A.c)).\n' $f $f
      printf '  show "%s loc: " (%s_value constr:(loc)).\n' $f $f
      printf '  show "%s def: " (%s_value constr:(def)).\n' $f $f
    done
    printf '  exact I.\nQed.\n'
  } > $d/B.v
  if comp -R $D/$v A -R $d Bdep $d/B.v > $d/out 2>&1; then echo ok > $d/rc; else echo failed > $d/rc; fi
done
# value F WHAT VARIANT: the result B_eval printed for evaluator F on WHAT.
value() { sed -n "s/^$1 $2: //p" $D/B_eval-$3/out; }
if [ "$(cat $D/B_eval-adm/rc)" = ok ] && [ "$(cat $D/B_eval-qed/rc)" = ok ]; then
  pass "B_eval compiles against both A"
else
  bad "B_eval: against the Admitted A $(cat $D/B_eval-adm/rc), against the proved A $(cat $D/B_eval-qed/rc): $(tr '\n' ' ' < $D/B_eval-qed/out | cut -c1-400)"
fi
for f in env econstr; do
  a=$(value $f A.c adm); q=$(value $f A.c qed); l=$(value $f loc adm); df=$(value $f def qed)
  case "$a" in
    *NotEvaluableConst*)
      if [ "$a" = "$q" ] && [ "$a" = "$l" ] && [ "$df" = "returned a value" ]; then
        pass "B_eval: ${f}_value raises the same '$a' on A.c against both A and on a local axiom, and evaluates a definition"
      else
        bad "B_eval: ${f}_value on A.c '$a' (Admitted A), '$q' (proved A), on the axiom '$l', on the definition '$df'"
      fi ;;
    *) bad "B_eval: ${f}_value on A.c against the Admitted A did not raise NotEvaluableConst: '$a'" ;;
  esac
done
a=$(value closure A.c adm); q=$(value closure A.c qed); l=$(value closure loc qed); df=$(value closure def adm)
if [ "$a" = "does not unfold" ] && [ "$q" = "$a" ] && [ "$l" = "$a" ] && [ "$df" = unfolds ]; then
  pass "B_eval: closure_value unfolds neither A.c (against both A) nor a local axiom, and unfolds a definition"
else
  bad "B_eval: closure_value on A.c '$a' (Admitted A), '$q' (proved A), on the axiom '$l', on the definition '$df'"
fi

exit $fail
