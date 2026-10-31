#!/usr/bin/env bash
# D18 (dispatch://INFRA-361), review gate 14: a plugin's Global.body_of_constant on a
# foreign constant is recorded.
#
# Global.body_of_constant answers None for an axiom and the forced body for an opaque
# proof, so a plugin tactic that calls it (coq-hammer-tactics' sauto does, through
# is_simple_unfold / case_unfold_cost) tells an Admitted foreign lemma from a proved
# one, and reads the proof's body, which no label covers. It now logs the status it saw
# and, for an opaque proof, the table it read the body from.
#
# The test suite cannot load hammer, so a small findlib plugin built here, kfpeek,
# defines an Ltac2 external body_shape : constr -> int that calls
# Global.body_of_constant Library.indirect_accessor on a constant: 0 for no body, 1 for a
# body that is a constructor, 2 for any other body. A's `c : True` is Admitted (adm),
# proved by `exact I` (qed1) or by `exact (match tt with tt => I end)` (qed2); all three
# have one label (the axiom-or-opaque blinding, and no label covers an opaque body).
# Checks:
# - A's three labels are equal;
# - B_print (prints body_shape A.c) prints 0, 1, 2 against adm, qed1, qed2; its
#   opacity_queries record {A.c, A, opaque=false, table=null} against adm and
#   {A.c, A, opaque=true, table=A} against qed1 and qed2;
# - B_axiom (fails unless body_shape A.c = 0) compiles against adm, fails against qed1,
#   and its adm object loads next to qed1: only its record tells the keep rule to
#   rebuild it;
# - B_shape1 (fails unless body_shape A.c = 1) compiles against qed1 and fails against
#   qed2: a body-only edit of a foreign proof, which the record's table (A) makes the
#   keep rule check;
# - outside the compiling process (review gate 15): B_par runs B_axiom's check under
#   `par:` over two goals, which coqc runs in rocqworker processes, and B_parany reads
#   A.c there; B_fork reads A.c in a child the plugin forks (kfpeek's
#   fork_body_shape, as coq-hammer's best forks its candidates). Their records reach
#   B's keepfacts through the opacity log file (library/opacityLog.ml): the same
#   records as in-process. No log these compiles made is left in TMPDIR.

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _bodyread
mkdir -p _bodyread/{pkg/kfpeek,adm,qed1,qed2,client,tmp}
D=_bodyread
# This fixture's compiles make their opacity logs here, so that the check at the end
# that none is left cannot see another test's (make -j).
export TMPDIR="$PWD/$D/tmp"

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
report() { "$TOOL" --axiom-report-json "$1"; }
field() { report "$1" | sed -n "s/.*\"$2\":\(\[[^]]*\]\|{[^}]*}\|null\).*/\1/p"; }
comp() { rocq c -q -location-free-label "$@"; }

# The plugin.
cat > $D/pkg/kfpeek/META <<'EOF'
requires = "rocq-runtime.plugins.ltac2"
plugin(native) = "p.cmxs"
EOF
cat > $D/pkg/kfpeek/p.ml <<'EOF'
open Ltac2_plugin

let shape c =
  match Global.body_of_constant Library.indirect_accessor c with
  | None -> 0
  | Some (b, _, _) -> if Constr.isConstruct b then 1 else 2

let () =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kfpeek"; mltac_tactic = "body_shape" }
    Tac2externals.(Tac2ffi.constr @-> eret Tac2ffi.int)
    (fun c _env sigma ->
       match EConstr.kind sigma c with
       | Constr.Const (cst, _) -> shape cst
       | _ -> -1)

(* The same read, in a forked child that then exits through [exit], which
   runs the at_exit handlers the child inherited (the opacity log's owner
   check keeps the child from removing the parent's log): the parent learns
   nothing from it (as with a losing candidate of coq-hammer's best). *)
let fork_shape c =
  match Unix.fork () with
  | 0 -> (try ignore (shape c) with _ -> ()); exit 0
  | pid -> ignore (Unix.waitpid [] pid); 0

let () =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kfpeek"; mltac_tactic = "fork_body_shape" }
    Tac2externals.(Tac2ffi.constr @-> eret Tac2ffi.int)
    (fun c _env sigma ->
       match EConstr.kind sigma c with
       | Constr.Const (cst, _) -> fork_shape cst
       | _ -> -1)

(* Tamper with the live opacity log, to test what a broken log does. *)
let log_path () = Option.default "" (Sys.getenv_opt "ROCQ_OPACITYLOG_FILE")

let str_ext name f =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kfpeek"; mltac_tactic = name }
    Tac2externals.(Tac2ffi.string @-> ret Tac2ffi.int) f

(* Append raw text to the log, with '|' written as a tab and '~' as a
   newline (Ltac2 string literals have no escapes). *)
let () = str_ext "log_append_raw" (fun s ->
    let s = String.map (function '|' -> '\t' | '~' -> '\n' | c -> c) s in
    let oc = open_out_gen [Open_wronly; Open_append] 0o600 (log_path ()) in
    output_string oc s; close_out oc; 0)

(* Move the log to [s] (its workers then cannot open it). *)
let () = str_ext "log_move_to" (fun s -> Sys.rename (log_path ()) s; 0)

(* Point the variable workers inherit at [s]. *)
let () = str_ext "log_env_set" (fun s -> Unix.putenv "ROCQ_OPACITYLOG_FILE" s; 0)
EOF
( cd $D/pkg/kfpeek && ocamlfind ocamlopt -thread -shared -package rocq-runtime.plugins.ltac2 -o p.cmxs p.ml > build.log 2>&1 ) ||
  { echo "FAIL cannot build the test plugin kfpeek"; cat $D/pkg/kfpeek/build.log; exit 1; }
export OCAMLPATH="$PWD/$D/pkg${OCAMLPATH:+:$OCAMLPATH}"

printf 'Lemma c : True.\nAdmitted.\n' > $D/adm/A.v
printf 'Lemma c : True.\nProof. exact I. Qed.\n' > $D/qed1/A.v
printf 'Lemma c : True.\nProof. exact (match tt with tt => I end). Qed.\n' > $D/qed2/A.v
for v in adm qed1 qed2; do comp -R $D/$v A $D/$v/A.v; done
alib=$(report $D/adm/A.vo | sed -n 's/.*"library":"\([^"]*\)".*/\1/p')
if [ "$(label $D/adm/A.vo)" = "$(label $D/qed1/A.vo)" ] && [ "$(label $D/qed1/A.vo)" = "$(label $D/qed2/A.vo)" ]; then
  pass "A's label is equal across Admitted, exact I and exact (match tt with tt => I end)"
else
  bad "A's labels differ: $(label $D/adm/A.vo) $(label $D/qed1/A.vo) $(label $D/qed2/A.vo)"
fi

head='Require Import Ltac2.Ltac2.
Declare ML Module "kfpeek".
Require A.
Ltac2 @ external body_shape : constr -> int := "kfpeek" "body_shape".
Ltac2 @ external fork_body_shape : constr -> int := "kfpeek" "fork_body_shape".
Ltac2 @ external log_append_raw : string -> int := "kfpeek" "log_append_raw".
Ltac2 @ external log_move_to : string -> int := "kfpeek" "log_move_to".
Ltac2 @ external log_env_set : string -> int := "kfpeek" "log_env_set".'
# b NAME BODY: the B file NAME, whose goal True is closed after BODY.
b() {
  mkdir -p $D/$1
  printf '%s\nGoal True.\n  %s\n  exact I.\nQed.\n' "$head" "$2" > $D/$1/B.v
}
# build NAME A: compile B NAME (copied to NAME-A) against A's variant; rc in NAME-A/rc.
build() {
  local d=$D/$1-$2
  mkdir -p $d; cp $D/$1/B.v $d/B.v
  if comp -R $D/$2 A -R $d Bdep $d/B.v > $d/out 2>&1; then echo ok > $d/rc; else echo failed > $d/rc; fi
}

b print 'Message.print (Message.concat (Message.of_string "SHAPE ") (Message.of_int (body_shape constr:(A.c)))).'
b axiom 'if Int.equal (body_shape constr:(A.c)) 0 then () else Control.throw (Tactic_failure (Some (Message.of_string "A.c has a body"))).'
b shape1 'if Int.equal (body_shape constr:(A.c)) 1 then () else Control.throw (Tactic_failure (Some (Message.of_string "A.c is not a constructor"))).'
for v in adm qed1 qed2; do build print $v; done
build axiom adm; build axiom qed1; build shape1 qed1; build shape1 qed2

# The same reads outside the compiling process. B_par runs B_axiom's check in `par:`
# over two goals: coqc runs each in a rocqworker process (Stm: 2 tactic workers by
# default, Partac), which returns only the proof term. B_parany reads A.c there
# without failing. B_fork reads A.c in a child the plugin forks.
parb() {
  mkdir -p $D/$1
  printf '%s\nLtac2 check () := %s\nSet Default Proof Mode "Classic".\nGoal True /\\ True.\n  split.\n  par: (ltac2:(check ()); exact I).\nQed.\n' \
    "$head" "$2" > $D/$1/B.v
}
parb par 'if Int.equal (body_shape constr:(A.c)) 0 then () else Control.throw (Tactic_failure (Some (Message.of_string "A.c has a body"))).'
parb parany 'let _ := body_shape constr:(A.c) in ().'
b fork 'let _ := fork_body_shape constr:(A.c) in ().'
build par adm; build par qed1; build parany qed1; build fork adm; build fork qed1

# Round 16. B_modpar: A is required inside a module (the summary is rolled back at
# End M and the REQUIRE-SYNTAX object replayed), then a par: worker reads A.c's body.
mkdir -p $D/modpar
printf '%s\n' 'Require Import Ltac2.Ltac2.' 'Declare ML Module "kfpeek".' 'Module M. Require A. End M.' \
  'Ltac2 @ external body_shape : constr -> int := "kfpeek" "body_shape".' \
  'Ltac2 check () := let _ := body_shape constr:(A.c) in ().' 'Set Default Proof Mode "Classic".' \
  'Goal True /\ True.' '  split.' '  par: (ltac2:(check ()); exact I).' 'Qed.' > $D/modpar/B.v
build modpar qed1
# B_torn: a valid record with no newline appended last; B_bad: a line that is not a record.
b torn 'let _ := body_shape constr:(A.c) in let _ := log_append_raw "R|A.A.c|A.A|1|A.A" in ().'
b bad 'let _ := body_shape constr:(A.c) in let _ := log_append_raw "garbage~" in ().'
build torn qed1; build bad qed1
# B_wmissing: the workers' variable names a file in a missing directory; B_wmoved: the
# log is moved away before the par:, so the workers cannot open it.
parx() { # NAME PRE: B_parany with the toplevel command PRE before the goal
  mkdir -p $D/$1
  printf '%s\n%s\nLtac2 check () := let _ := body_shape constr:(A.c) in ().\nSet Default Proof Mode "Classic".\nGoal True /\\ True.\n  split.\n  par: (ltac2:(check ()); exact I).\nQed.\n' \
    "$head" "$2" > $D/$1/B.v
}
parx wmissing "Ltac2 Eval (log_env_set \"$PWD/$D/missing/x.log\")."
parx wmoved "Ltac2 Eval (log_move_to \"$PWD/$D/moved.log\")."
build wmissing qed1; build wmoved qed1
# B_notmp: TMPDIR is a missing directory, so the log cannot be made.
mkdir -p $D/notmp-qed1; cp $D/print/B.v $D/notmp-qed1/B.v
if TMPDIR="$PWD/$D/nodir" comp -R $D/qed1 A -R $D/notmp-qed1 Bdep $D/notmp-qed1/B.v > $D/notmp-qed1/out 2>&1
then echo ok > $D/notmp-qed1/rc; else echo failed > $D/notmp-qed1/rc; fi

s0=$(sed -n 's/^SHAPE //p' $D/print-adm/out); s1=$(sed -n 's/^SHAPE //p' $D/print-qed1/out); s2=$(sed -n 's/^SHAPE //p' $D/print-qed2/out)
if [ "$s0/$s1/$s2" = "0/1/2" ]; then
  pass "the plugin observes A.c: body_shape is 0, 1, 2 against the Admitted, exact I and match proofs"
else
  bad "body_shape against adm/qed1/qed2: '$s0/$s1/$s2' ($(cat $D/print-adm/rc) $(cat $D/print-qed1/rc) $(cat $D/print-qed2/rc)): $(tr '\n' ' ' < $D/print-adm/out | cut -c1-400)"
fi

q_adm="[{\"constant\":\"$alib.c\",\"library\":\"$alib\",\"opaque\":false,\"table\":null}]"
q_qed="[{\"constant\":\"$alib.c\",\"library\":\"$alib\",\"opaque\":true,\"table\":\"$alib\"}]"
qa=$(field $D/print-adm/B.vo opacity_queries)
if [ "$qa" = "$q_adm" ]; then
  pass "B_print records the axiom Global.body_of_constant saw: $qa"
else
  bad "B_print's opacity_queries against the Admitted A: '$qa'"
fi
q1=$(field $D/print-qed1/B.vo opacity_queries); q2=$(field $D/print-qed2/B.vo opacity_queries)
if [ "$q1" = "$q_qed" ] && [ "$q2" = "$q_qed" ]; then
  pass "B_print records the opaque proof and the table its body was read from, against both proofs: $q1"
else
  bad "B_print's opacity_queries against the proved A: '$q1' (exact I), '$q2' (match)"
fi

if [ "$(cat $D/axiom-adm/rc)" = ok ] && [ "$(cat $D/axiom-qed1/rc)" = failed ] \
   && grep -q 'A.c has a body' $D/axiom-qed1/out; then
  pass "B_axiom compiles against the Admitted A and fails against the proved A"
else
  bad "B_axiom: against the Admitted A $(cat $D/axiom-adm/rc), against the proved A $(cat $D/axiom-qed1/rc): $(tr '\n' ' ' < $D/axiom-qed1/out | cut -c1-400)"
fi
printf 'Require Bdep.B.\n' > $D/client/C.v
if comp -R $D/qed1 A -R $D/axiom-adm Bdep -R $D/client Cl $D/client/C.v > $D/client/out 2>&1; then
  pass "B_axiom compiled against the Admitted A loads next to the proved A: only its record tells the keep rule to rebuild it"
else
  bad "B_axiom compiled against the Admitted A does not load next to the proved A: $(tr '\n' ' ' < $D/client/out | cut -c1-400)"
fi
if [ "$(cat $D/shape1-qed1/rc)" = ok ] && [ "$(cat $D/shape1-qed2/rc)" = failed ] \
   && grep -q 'A.c is not a constructor' $D/shape1-qed2/out; then
  pass "B_shape1 compiles against the exact I proof and fails against the match proof: a body-only edit, which the record's table makes the keep rule check"
else
  bad "B_shape1: against exact I $(cat $D/shape1-qed1/rc), against match $(cat $D/shape1-qed2/rc): $(tr '\n' ' ' < $D/shape1-qed2/out | cut -c1-400)"
fi

# Outside the compiling process: the same records as in it.
if [ "$(cat $D/par-adm/rc)" = ok ] && [ "$(cat $D/par-qed1/rc)" = failed ] \
   && grep -q 'A.c has a body' $D/par-qed1/out; then
  pass "B_par (the B_axiom check under par:) compiles against the Admitted A and fails against the proved A"
else
  bad "B_par: against the Admitted A $(cat $D/par-adm/rc), against the proved A $(cat $D/par-qed1/rc): $(tr '\n' ' ' < $D/par-qed1/out | cut -c1-400)"
fi
qp=$(field $D/par-adm/B.vo opacity_queries); qpa=$(field $D/parany-qed1/B.vo opacity_queries)
if [ "$qp" = "$q_adm" ] && [ "$qpa" = "$q_qed" ]; then
  pass "par: workers' records reach the library: $qp against the Admitted A, $qpa against the proved A"
else
  bad "B_par's opacity_queries under par: '$qp' (Admitted A), B_parany's '$qpa' (proved A)"
fi
qf=$(field $D/fork-adm/B.vo opacity_queries); qfq=$(field $D/fork-qed1/B.vo opacity_queries)
if [ "$(cat $D/fork-adm/rc)" = ok ] && [ "$qf" = "$q_adm" ] && [ "$qfq" = "$q_qed" ]; then
  pass "a forked child's records reach the library: $qf against the Admitted A, $qfq against the proved A"
else
  bad "B_fork ($(cat $D/fork-adm/rc)) opacity_queries from a forked child: '$qf' (Admitted A), '$qfq' (proved A): $(tr '\n' ' ' < $D/fork-adm/out | cut -c1-300)"
fi

# Round 16: a broken log never gives an incomplete record.
qm=$(field $D/modpar-qed1/B.vo opacity_queries)
if [ "$(cat $D/modpar-qed1/rc)" = ok ] && [ "$qm" = "$q_qed" ]; then
  pass "B_modpar: after Module M. Require A. End M., a par: worker reads A.c's body and records it: $qm"
else
  bad "B_modpar ($(cat $D/modpar-qed1/rc)): opacity_queries '$qm': $(tr '\n' ' ' < $D/modpar-qed1/out | cut -c1-400)"
fi
nulls() { # NAME TEXT: rc ok, and the report has no keepfacts (assumptions and opacity_queries null)
  local d=$D/$1-qed1 a q
  a=$(field $d/B.vo assumptions); q=$(field $d/B.vo opacity_queries)
  if [ "$(cat $d/rc)" = ok ] && [ "$a" = null ] && [ "$q" = null ]; then
    pass "$2: compiles, and the library has no keepfacts (assumptions null, opacity_queries null)"
  else
    bad "$2 ($(cat $d/rc)): assumptions '$a', opacity_queries '$q': $(tr '\n' ' ' < $d/out | cut -c1-300)"
  fi
}
nulls torn "B_torn: a log whose last line has no newline"
nulls bad "B_bad: a log with a line that is not a record"
nulls notmp "B_notmp: TMPDIR is a missing directory"
cantwrite() { # NAME TEXT: the compile fails with the opacity log's write error
  local d=$D/$1-qed1
  if [ "$(cat $d/rc)" = failed ] && grep -q "Cannot write a record to the keep rule's opacity log" $d/out; then
    pass "$2: the compile fails with the write error"
  else
    bad "$2 ($(cat $d/rc)): $(tr '\n' ' ' < $d/out | cut -c1-400)"
  fi
}
cantwrite wmissing "B_wmissing: a worker whose log is in a missing directory"
cantwrite wmoved "B_wmoved: a worker whose log was moved away"
# Each compile's log is private and removed at exit: this fixture's TMPDIR is empty.
left=$(find "$TMPDIR" -mindepth 1 2>/dev/null | head -3 | tr '\n' ' ')
if [ -z "$left" ]; then
  pass "this fixture's TMPDIR ($TMPDIR) is empty: every opacity log was removed"
else
  bad "opacity logs left in $TMPDIR: $left"
fi

exit $fail
