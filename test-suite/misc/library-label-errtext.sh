#!/usr/bin/env bash
# D18 (dispatch://INFRA-361), round 13 observer sweep: an error text must not tell a
# foreign opaque proof from an axiom.
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
# fails when they differ: B_unfold with `unfold _ at 1`, B_auto with `autounfold_one`.
# Checks: A's labels are equal; each B compiles against both A; the text it prints for
# A.c is the same against both A and the same as for the local axiom.

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _errtext
mkdir -p _errtext/{adm,qed}

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
comp() { rocq c -q -location-free-label "$@"; }

D=_errtext
printf 'Lemma c : nat.\nAdmitted.\n' > $D/adm/A.v
printf 'Lemma c : nat.\nProof. exact 0. Qed.\n' > $D/qed/A.v
comp -R $D/adm A $D/adm/A.v
comp -R $D/qed A $D/qed/A.v
if [ "$(label $D/adm/A.vo)" = "$(label $D/qed/A.vo)" ]; then
  pass "A's label is equal across c Admitted -> Qed"
else
  bad "A's label differs across c Admitted -> Qed (expected equal)"
fi

head='Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Require A.
Axiom loc : nat.
Create HintDb kfa.
Create HintDb kfl.
#[export] Hint Unfold A.c : kfa.
#[export] Hint Unfold loc : kfl.
Ltac2 err_text (t : unit -> unit) : string :=
  match Control.case t with
  | Val _ => "succeeded"
  | Err e =>
    match e with
    | Internal err => Message.to_string (Control.print_err err)
    | _ => Message.to_string (Message.of_exn e)
    end
  end.
Ltac2 same (ta : string) (tl : string) :=
  Message.print (Message.concat (Message.of_string "TEXT foreign: ") (Message.of_string ta));
  Message.print (Message.concat (Message.of_string "TEXT local axiom: ") (Message.of_string tl));
  if String.equal ta tl then ()
  else Control.throw (Tactic_failure (Some (Message.of_string "the error text tells A.c from an axiom"))).'

# check NAME TACTIC_ON_A TACTIC_ON_LOC: B, on the goal `A.c = A.c /\ loc = loc`, takes
# the error text of each tactic (each fails, leaving the goal as it was), prints both,
# and fails unless they are equal.
check() {
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
  local fa fq la
  fa=$(sed -n 's/^TEXT foreign: //p' $D/$name-adm/out | tr '\n' ' ')
  fq=$(sed -n 's/^TEXT foreign: //p' $D/$name-qed/out | tr '\n' ' ')
  la=$(sed -n 's/^TEXT local axiom: //p' $D/$name-adm/out | tr '\n' ' ')
  if [ "$(cat $D/$name-adm/rc)" = ok ] && [ "$(cat $D/$name-qed/rc)" = ok ] && [ -n "$fa" ] && [ "$fa" = "$fq" ] && [ "$fa" = "$la" ]; then
    pass "$name: B compiles against both A, and the error text for A.c is the same against both and the same as for a local axiom: $fa"
  else
    bad "$name: B against the Admitted A: $(cat $D/$name-adm/rc), against the proved A: $(cat $D/$name-qed/rc); A.c's text '$fa' against the Admitted A, '$fq' against the proved A, the local axiom's '$la'; $(tr '\n' ' ' < $D/$name-qed/out | cut -c1-400)"
  fi
}

# `unfold _ at 1` (Tacred.value_of_evaluable_ref).
check B_unfold 'unfold A.c at 1' 'unfold loc at 1'
# `autounfold_one` with a database that names only that constant (Eauto.unfold_head).
check B_auto 'ltac1:(autounfold_one with kfa)' 'ltac1:(autounfold_one with kfl)'

exit $fail
