#!/usr/bin/env bash
# A plugin's Global.body_of_constant on a foreign constant is recorded.
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
# - outside the compiling process: B_par runs B_axiom's check under
#   `par:` over two goals, which coqc runs in rocqworker processes, and B_parany reads
#   A.c there; B_fork reads A.c in a child the plugin forks (kfpeek's
#   fork_body_shape, as coq-hammer's best forks its candidates; the child leaves through
#   `exit 0`, so the owner check that keeps it from removing the parent's log is
#   exercised). Their records reach B's keepfacts through the opacity log file
#   (library/opacityLog.ml): the same records as in-process;
# - B_modpar (`Module M. Require A. End M.`, then a par: body read)
#   records it; B_torn (a record appended with no newline), B_bad (a line that is not a
#   record) and B_notmp (TMPDIR a missing directory) compile and have no keepfacts
#   (null/null), while B_whole (B_torn's record with its newline) reads as a record;
#   B_wmissing (the log's directory moved away before the par:) and
#   B_wmoved (the log moved away before the par:) fail with the opacity log's write
#   error;
# - B_devnull (B_parany with ROCQ_OPACITYLOG_FILE=/dev/null outside:
#   the compiling process ignores it) records the read; B_wenv (the compiling process
#   points the variable at a missing file before the par:: the worker pool still gives
#   the workers its own log) records it; B_parnotmp (B_parany with TMPDIR a missing
#   directory: the workers get an empty variable) compiles with no keepfacts; B_secpar
#   (`Section S. Require A. End S.`, then a par: body read) records it; a coqc without
#   -location-free-label and with ROCQ_OPACITYLOG_FILE=/nonexistent/x compiles a
#   Transparent on an axiom (B_stock) and a par: body read (B_stockpar);
# - B_asyncenv, a proof delegated to a proof worker (-async-proofs on)
#   that reads A.c's body there, with -async-proofs-private-flags
#   extra-env=KFPEEK_EXTRA_ENV=1;ROCQ_OPACITYLOG_FILE=/dev/null: the worker pool gives
#   the worker the compile's own log anyway, so the read is recorded. The pool spawns
#   its first workers before it parses extra-env, and gives extra-env only to a worker
#   spawned later; a proof worker is replaced after each proof, so with one worker the
#   second proof runs in a replacement. The proof reads the body only after it checks
#   that it runs in a worker and that its environment has KFPEEK_EXTRA_ENV=1, so a
#   master, or a worker that did not get extra-env, fails the compile;
# - B_modfail, `Module M. Require A. Fail Require Y.X. End M.` where
#   Y.X's file is qed2's A.vo (it holds the name A.A, so its Require fails), then a par:
#   worker checks that A.c's body is qed1's (shape 1): the failed Require leaves the
#   loaded A's opaque-proof handle in place, so the replay at End M gives the workers
#   qed1's proofs, and the read is recorded;
# - B_parfork: a par: worker's tactic reads A.c only in a child it forks, before the
#   worker has opened the log itself: the child's record reaches B;
# - B_workerreplace: the compiling process replaces its log with another file,
#   a par: worker makes its first body read there, and the worker restores the
#   owner's log before the save. The worker gets the owner log's device and
#   inode with its path and refuses the substitute, so the compile fails
#   rather than save a proper subset of the worker's records;
# - the log read back is the file the compile made, with what was written to it:
#   B_ident (a copy of the log's bytes put at its path before the save), B_empty (an
#   empty file put there) and B_trunc (the log emptied in place) compile and have no
#   keepfacts (null/null), and the files B_ident and B_empty put there are still there
#   after the compile; B_reltmp (TMPDIR relative, and a Cd before the par:) records
#   the workers' read and leaves no log behind;
# - B_forge: a par: worker records a constant whose name holds tabs and a newline,
#   spelled so that a log that wrote names as they are would read two records: it
#   reads back as one record, with its own name;
# - this fixture's compiles use their own TMPDIR, which is empty at the end (B_ident
#   and B_empty use two others).

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

(* Move the log's directory to [s] (the workers' path then names a file in a
   missing directory). *)
let () = str_ext "log_dir_move_to" (fun s -> Sys.rename (Filename.dirname (log_path ())) s; 0)

(* Set the variable in the compiling process, which a spawned worker would
   inherit if the worker pool did not set it itself. *)
let () = str_ext "log_env_set" (fun s -> Unix.putenv "ROCQ_OPACITYLOG_FILE" s; 0)

(* 1 when this process's environment sets the variable [s] to 1, else 0. *)
let () = str_ext "env_is_1" (fun s -> if Sys.getenv_opt s = Some "1" then 1 else 0)

(* 1 in a worker process (a par: or an -async-proofs proof worker), else 0. *)
let () =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kfpeek"; mltac_tactic = "in_worker" }
    Tac2externals.(Tac2ffi.unit @-> ret Tac2ffi.int)
    (fun () -> if Flags.async_proofs_is_worker () then 1 else 0)

(* Replace the live log, before the library is saved: "copy", a copy of its
   bytes in another file put at its path; "empty", an empty file put at its
   path; "truncate", the log itself emptied. *)
let () = str_ext "log_replace" (fun how ->
    let p = log_path () in
    let put s = Out_channel.with_open_bin (p ^ ".new") (fun oc -> output_string oc s);
      Sys.rename (p ^ ".new") p in
    (match how with
     | "copy" -> put (In_channel.with_open_bin p In_channel.input_all)
     | "empty" -> put ""
     | "truncate" -> Unix.truncate p 0
     | _ -> invalid_arg how);
    0)

(* Record [c]'s status, through the log, for a constant of [c]'s library
   whose name holds tabs and a newline (a plugin can make one,
   Id.of_string_soft), spelled so that a log that wrote names as they are
   would read it as two records: its own, cut short, and one for a constant
   [<library>.forged]. *)
let () =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kfpeek"; mltac_tactic = "record_forged" }
    Tac2externals.(Tac2ffi.constr @-> eret Tac2ffi.int)
    (fun c _env sigma ->
       match EConstr.kind sigma c with
       | Constr.Const (cst, _) ->
         let mp = Names.Constant.modpath cst in
         let lib = Names.ModPath.to_string mp in
         let id = Names.Id.of_string_soft (Printf.sprintf "x\t%s\t0\t-\nR\t%s.forged" lib lib) in
         let forged = Names.Constant.make1 (Names.KerName.make mp (Names.Label.of_id id)) in
         OpacityLog.record forged (Global.lookup_constant cst); 0
       | _ -> -1)

(* Put a substitute at the owner's log path. A [par:] worker later makes its
   first record there; it restores the owner file before the compilation can
   save the library. The worker must reject that substitute by identity. *)
let () = str_ext "log_worker_substitute" (fun _ ->
    let p = log_path () in
    Sys.rename p (p ^ ".owner");
    Out_channel.with_open_bin p (fun oc -> output_string oc "worker substitute\n");
    0)

let worker_shape_restore c sigma =
  let p = log_path () in
  Fun.protect
    ~finally:(fun () ->
        let owner = p ^ ".owner" in
        if Sys.file_exists owner then begin
          let substitute = p ^ ".substitute." ^ string_of_int (Unix.getpid ()) in
          Sys.rename p substitute;
          Fun.protect
            ~finally:(fun () -> if Sys.file_exists substitute then Sys.remove substitute)
            (fun () -> Sys.rename owner p)
        end)
    (fun () ->
       match EConstr.kind sigma c with
       | Constr.Const (cst, _) -> ignore (shape cst); 0
       | _ -> -1)

let () =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "kfpeek"; mltac_tactic = "worker_shape_restore" }
    Tac2externals.(Tac2ffi.constr @-> eret Tac2ffi.int)
    (fun c _env sigma -> worker_shape_restore c sigma)
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
Ltac2 @ external log_dir_move_to : string -> int := "kfpeek" "log_dir_move_to".
Ltac2 @ external log_env_set : string -> int := "kfpeek" "log_env_set".
Ltac2 @ external in_worker : unit -> int := "kfpeek" "in_worker".
Ltac2 @ external env_is_1 : string -> int := "kfpeek" "env_is_1".
Ltac2 @ external log_replace : string -> int := "kfpeek" "log_replace".
Ltac2 @ external record_forged : constr -> int := "kfpeek" "record_forged".
Ltac2 @ external log_worker_substitute : string -> int := "kfpeek" "log_worker_substitute".
Ltac2 @ external worker_shape_restore : constr -> int := "kfpeek" "worker_shape_restore".'
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

# B_modpar: A is required inside a module (the summary is rolled back at
# End M and the REQUIRE-SYNTAX object replayed), then a par: worker reads A.c's body.
mkdir -p $D/modpar
printf '%s\n' 'Require Import Ltac2.Ltac2.' 'Declare ML Module "kfpeek".' 'Module M. Require A. End M.' \
  'Ltac2 @ external body_shape : constr -> int := "kfpeek" "body_shape".' \
  'Ltac2 check () := let _ := body_shape constr:(A.c) in ().' 'Set Default Proof Mode "Classic".' \
  'Goal True /\ True.' '  split.' '  par: (ltac2:(check ()); exact I).' 'Qed.' > $D/modpar/B.v
build modpar qed1
# B_torn: a valid record (A.A.d, library A.A, an axiom, its names in hexadecimal) with
# no newline appended last; B_whole: the same record with its newline (a control: it
# reads as a record, beside the one the read itself made); B_bad: a line that is not a
# record.
b torn 'let _ := body_shape constr:(A.c) in let _ := log_append_raw "R|412e412e64|+412e41|0|-" in ().'
b whole 'let _ := body_shape constr:(A.c) in let _ := log_append_raw "R|412e412e64|+412e41|0|-~" in ().'
b bad 'let _ := body_shape constr:(A.c) in let _ := log_append_raw "garbage~" in ().'
build torn qed1; build whole qed1; build bad qed1
# B_wmissing: the log's directory is moved away before the par:, so the workers' path
# names a file in a missing directory; B_wmoved: the log itself is moved away. Either
# way the workers cannot open it. B_wenv: the compiling process points the
# variable at a missing file before the par:; the worker pool still gives the workers the
# compile's own log, so their reads are recorded.
parx() { # NAME PRE: B_parany with the toplevel command PRE before the goal
  mkdir -p $D/$1
  printf '%s\n%s\nLtac2 check () := let _ := body_shape constr:(A.c) in ().\nSet Default Proof Mode "Classic".\nGoal True /\\ True.\n  split.\n  par: (ltac2:(check ()); exact I).\nQed.\n' \
    "$head" "$2" > $D/$1/B.v
}
parx wmissing "Ltac2 Eval (log_dir_move_to \"$PWD/$D/tmpw-gone\")."
parx wmoved "Ltac2 Eval (log_move_to \"$PWD/$D/moved.log\")."
parx wenv "Ltac2 Eval (log_env_set \"$PWD/$D/missing/x.log\")."
mkdir -p $D/tmpw
mkdir -p $D/wmissing-qed1; cp $D/wmissing/B.v $D/wmissing-qed1/B.v
if TMPDIR="$PWD/$D/tmpw" comp -R $D/qed1 A -R $D/wmissing-qed1 Bdep $D/wmissing-qed1/B.v > $D/wmissing-qed1/out 2>&1
then echo ok > $D/wmissing-qed1/rc; else echo failed > $D/wmissing-qed1/rc; fi
rm -rf $D/tmpw $D/tmpw-gone
build wmoved qed1; build wenv qed1
# B_notmp: TMPDIR is a missing directory, so the log cannot be made.
mkdir -p $D/notmp-qed1; cp $D/print/B.v $D/notmp-qed1/B.v
if TMPDIR="$PWD/$D/nodir" comp -R $D/qed1 A -R $D/notmp-qed1 Bdep $D/notmp-qed1/B.v > $D/notmp-qed1/out 2>&1
then echo ok > $D/notmp-qed1/rc; else echo failed > $D/notmp-qed1/rc; fi

# envbuild NAME A ENV...: compile B NAME (copied to NAME-A) against A's variant
# with the environment ENV and -location-free-label; rc in NAME-A/rc.
envbuild() {
  local name=$1 a=$2 d=$D/$1-$2; shift 2
  mkdir -p $d; cp $D/$name/B.v $d/B.v
  if env "$@" rocq c -q -location-free-label -R $D/$a A -R $d Bdep $d/B.v > $d/out 2>&1
  then echo ok > $d/rc; else echo failed > $d/rc; fi
}
mkdir -p $D/devnull $D/parnotmp $D/stockpar
cp $D/parany/B.v $D/devnull/B.v; cp $D/parany/B.v $D/parnotmp/B.v; cp $D/parany/B.v $D/stockpar/B.v
envbuild devnull qed1 ROCQ_OPACITYLOG_FILE=/dev/null
envbuild parnotmp qed1 TMPDIR="$PWD/$D/nodir"
# B_secpar: A is required inside a section (rolled back at End S), then a par: body read.
mkdir -p $D/secpar
printf '%s\n' 'Require Import Ltac2.Ltac2.' 'Declare ML Module "kfpeek".' 'Section S. Require A. End S.' \
  'Ltac2 @ external body_shape : constr -> int := "kfpeek" "body_shape".' \
  'Ltac2 check () := let _ := body_shape constr:(A.c) in ().' 'Set Default Proof Mode "Classic".' \
  'Goal True /\ True.' '  split.' '  par: (ltac2:(check ()); exact I).' 'Qed.' > $D/secpar/B.v
build secpar qed1
# B_modfail: a failed Require, inside the module, of a file that holds A's
# name (qed2's A.vo as Y.X), then a par: worker that needs qed1's body (shape 1).
mkdir -p $D/modfail-qed1 $D/xq2
cp $D/qed2/A.vo $D/xq2/X.vo
printf '%s\n' 'Require Import Ltac2.Ltac2.' 'Declare ML Module "kfpeek".' 'Module M. Require A. Fail Require Y.X. End M.' \
  'Ltac2 @ external body_shape : constr -> int := "kfpeek" "body_shape".' \
  'Ltac2 check () := if Int.equal (body_shape constr:(A.c)) 1 then () else Control.throw (Tactic_failure (Some (Message.of_string "A.c is not the loaded A.c"))).' \
  'Set Default Proof Mode "Classic".' 'Goal True /\ True.' '  split.' '  par: (ltac2:(check ()); exact I).' 'Qed.' \
  > $D/modfail-qed1/B.v
if comp -R $D/qed1 A -Q $D/xq2 Y -R $D/modfail-qed1 Bdep $D/modfail-qed1/B.v > $D/modfail-qed1/out 2>&1
then echo ok > $D/modfail-qed1/rc; else echo failed > $D/modfail-qed1/rc; fi
# A coqc without -location-free-label, with ROCQ_OPACITYLOG_FILE naming a missing file:
# B_stock runs Transparent on an axiom in the compiling process, B_stockpar reads a body
# in par: workers.
mkdir -p $D/stock $D/stock-adm $D/stockpar-qed1
printf 'Require A.\nTransparent A.c.\n' > $D/stock/B.v
cp $D/stock/B.v $D/stock-adm/B.v; cp $D/stockpar/B.v $D/stockpar-qed1/B.v
for nd in stock-adm:adm stockpar-qed1:qed1; do
  d=$D/${nd%%:*}; a=${nd##*:}
  if ROCQ_OPACITYLOG_FILE=/nonexistent/x rocq c -q -R $D/$a A -R $d Bdep $d/B.v > $d/out 2>&1
  then echo ok > $d/rc; else echo failed > $d/rc; fi
done
# B_asyncenv: a delegated proof whose worker's variable extra-env points at
# /dev/null. One proof worker (-async-proofs-j 1): l0 runs in the first one, which the
# pool spawned before it parsed extra-env, and l in its replacement, which gets
# extra-env (KFPEEK_EXTRA_ENV=1 shows it did).
mkdir -p $D/asyncenv $D/asyncenv-qed1
{ printf '%s\n' "$head"
  printf '%s\n' 'Lemma l0 : True.' 'Proof. exact I. Qed.' 'Lemma l : True.' \
    'Proof. (if Int.equal (in_worker ()) 1 then () else Control.throw (Tactic_failure (Some (Message.of_string "not in a proof worker")))); (if Int.equal (env_is_1 "KFPEEK_EXTRA_ENV") 1 then () else Control.throw (Tactic_failure (Some (Message.of_string "the proof worker did not get extra-env")))); let _ := body_shape constr:(A.c) in exact I. Qed.'
} > $D/asyncenv/B.v
cp $D/asyncenv/B.v $D/asyncenv-qed1/B.v
if comp -async-proofs on -async-proofs-j 1 -async-proofs-delegation-threshold 0 \
     -async-proofs-private-flags "extra-env=KFPEEK_EXTRA_ENV=1;ROCQ_OPACITYLOG_FILE=/dev/null" \
     -R $D/qed1 A -R $D/asyncenv-qed1 Bdep $D/asyncenv-qed1/B.v > $D/asyncenv-qed1/out 2>&1
then echo ok > $D/asyncenv-qed1/rc; else echo failed > $D/asyncenv-qed1/rc; fi
# B_parfork: a par: worker's tactic reads A.c only in a child it forks, before the
# worker itself has opened the log (the child opens it from the variable it inherited).
parb parfork 'let _ := fork_body_shape constr:(A.c) in ().'
build parfork adm; build parfork qed1
# B_workerreplace: the compiling process puts a substitute at its log path;
# a par: worker makes its first body read there and puts the owner's file back
# before the save. The worker must refuse the substitute, so the compile fails
# instead of saving the restored owner's log with the worker's query missing.
mkdir -p $D/workerreplace
{ printf '%s\n' "$head"
  printf '%s\n' 'Ltac2 Eval (log_worker_substitute "").' \
    'Ltac2 check () := let _ := worker_shape_restore constr:(A.c) in ().' \
    'Set Default Proof Mode "Classic".' 'Goal True /\ True.' '  split.' \
    '  par: (ltac2:(check ()); exact I).' 'Qed.'
} > $D/workerreplace/B.v
build workerreplace qed1
# B_forge: a par: worker records, through the log, a constant whose name holds tabs
# and a newline (kfpeek's record_forged).
parb forge 'let _ := record_forged constr:(A.c) in ().'
build forge adm
# pard NAME POST: B_parany with the toplevel command POST after the proof, before the
# library is saved. B_ident puts a copy of the log's bytes at its path, B_empty an
# empty file, and B_trunc empties the log itself: the workers' records are in none.
# B_ident and B_empty use their own TMPDIR: the file put at the log's path is not the
# compile's, so it must stay there after the compile.
pard() {
  mkdir -p $D/$1
  printf '%s\nLtac2 check () := let _ := body_shape constr:(A.c) in ().\nSet Default Proof Mode "Classic".\nGoal True /\\ True.\n  split.\n  par: (ltac2:(check ()); exact I).\nQed.\n%s\n' \
    "$head" "$2" > $D/$1/B.v
}
pard ident 'Ltac2 Eval (log_replace "copy").'
pard empty 'Ltac2 Eval (log_replace "empty").'
pard trunc 'Ltac2 Eval (log_replace "truncate").'
mkdir -p $D/tmp-ident $D/tmp-empty
TMPDIR="$PWD/$D/tmp-ident" build ident qed1
TMPDIR="$PWD/$D/tmp-empty" build empty qed1
build trunc qed1
# B_reltmp: TMPDIR is relative (the compile runs in misc/), and B changes directory
# (Cd) before a par: body read; every path of the compile is absolute, so only the
# log's path could depend on the directory.
parx reltmp "Cd \"$PWD/$D/cdhere\"."
mkdir -p $D/cdhere $D/tmprel $D/reltmp-qed1; cp $D/reltmp/B.v $D/reltmp-qed1/B.v
if TMPDIR="$D/tmprel" comp -R "$PWD/$D/qed1" A -R "$PWD/$D/reltmp-qed1" Bdep "$PWD/$D/reltmp-qed1/B.v" \
     > $D/reltmp-qed1/out 2>&1
then echo ok > $D/reltmp-qed1/rc; else echo failed > $D/reltmp-qed1/rc; fi

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

# A broken log never gives an incomplete record.
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
q_whole="[{\"constant\":\"$alib.c\",\"library\":\"$alib\",\"opaque\":true,\"table\":\"$alib\"},{\"constant\":\"$alib.d\",\"library\":\"$alib\",\"opaque\":false,\"table\":null}]"
qwh=$(field $D/whole-qed1/B.vo opacity_queries)
if [ "$(cat $D/whole-qed1/rc)" = ok ] && [ "$qwh" = "$q_whole" ]; then
  pass "B_whole: the same record with its newline reads as a record, beside the read's own: $qwh"
else
  bad "B_whole ($(cat $D/whole-qed1/rc)): opacity_queries '$qwh', expected '$q_whole': $(tr '\n' ' ' < $D/whole-qed1/out | cut -c1-300)"
fi
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
nulls ident "B_ident: the log replaced, before the save, by a copy of its bytes (another file)"
nulls empty "B_empty: the log replaced, before the save, by an empty file"
nulls trunc "B_trunc: the log emptied in place before the save"
# The files put at the log's path stay: one file each, the copy holding the log's
# first line, the empty one empty.
li=$(find $D/tmp-ident -type f); le=$(find $D/tmp-empty -type f)
if [ "$(printf '%s\n' "$li" | grep -c .)" = 1 ] && head -1 "$li" | grep -q '^rocq-opacity-log ' \
   && [ "$(printf '%s\n' "$le" | grep -c .)" = 1 ] && [ ! -s "$le" ]; then
  pass "B_ident, B_empty: the file put at the log's path is still there after the compile (it removes only the file it made)"
else
  bad "B_ident, B_empty: left in $D/tmp-ident: '$li', in $D/tmp-empty: '$le'"
fi

# The log's encoding, a worker's forked child, and a relative TMPDIR.
q_forge="[{\"constant\":\"$alib.x\\u0009$alib\\u00090\\u0009-\\u000aR\\u0009$alib.forged\",\"library\":\"$alib\",\"opaque\":false,\"table\":null}]"
qg=$(field $D/forge-adm/B.vo opacity_queries)
if [ "$(cat $D/forge-adm/rc)" = ok ] && [ "$qg" = "$q_forge" ]; then
  pass "B_forge: a name with tabs and a newline reads back as itself, one record: $qg"
else
  bad "B_forge ($(cat $D/forge-adm/rc)): opacity_queries '$qg', expected '$q_forge': $(tr '\n' ' ' < $D/forge-adm/out | cut -c1-300)"
fi
qpf=$(field $D/parfork-adm/B.vo opacity_queries); qpfq=$(field $D/parfork-qed1/B.vo opacity_queries)
if [ "$(cat $D/parfork-adm/rc)" = ok ] && [ "$(cat $D/parfork-qed1/rc)" = ok ] && [ "$qpf" = "$q_adm" ] && [ "$qpfq" = "$q_qed" ]; then
  pass "B_parfork: the records of a child a par: worker forks reach the library: $qpf against the Admitted A, $qpfq against the proved A"
else
  bad "B_parfork ($(cat $D/parfork-adm/rc) $(cat $D/parfork-qed1/rc)): opacity_queries '$qpf' (Admitted A), '$qpfq' (proved A): $(tr '\n' ' ' < $D/parfork-qed1/out | cut -c1-300)"
fi
if [ "$(cat $D/workerreplace-qed1/rc)" = failed ] \
   && grep -q "Cannot write a record to the keep rule's opacity log" $D/workerreplace-qed1/out \
   && [ ! -e $D/workerreplace-qed1/B.vo ]; then
  pass "B_workerreplace: a worker refuses a substitute log even after the owner log returns before the save"
else
  bad "B_workerreplace ($(cat $D/workerreplace-qed1/rc)): $(tr '\n' ' ' < $D/workerreplace-qed1/out | cut -c1-400)"
fi
qr=$(field $D/reltmp-qed1/B.vo opacity_queries)
leftr=$(find "$D/tmprel" -mindepth 1 2>/dev/null | head -3 | tr '\n' ' ')
if [ "$(cat $D/reltmp-qed1/rc)" = ok ] && [ "$qr" = "$q_qed" ] && [ -z "$leftr" ]; then
  pass "B_reltmp: with a relative TMPDIR and a Cd before the par:, the workers' read is recorded and the log removed: $qr"
else
  bad "B_reltmp ($(cat $D/reltmp-qed1/rc)): opacity_queries '$qr', left in $D/tmprel: '$leftr': $(tr '\n' ' ' < $D/reltmp-qed1/out | cut -c1-400)"
fi

# Inherited log variables, sections, failed Requires and stock builds.
qw=$(field $D/wenv-qed1/B.vo opacity_queries)
if [ "$(cat $D/wenv-qed1/rc)" = ok ] && [ "$qw" = "$q_qed" ]; then
  pass "B_wenv: the compiling process pointed the variable at a missing file, and its workers still record into its log: $qw"
else
  bad "B_wenv ($(cat $D/wenv-qed1/rc)): opacity_queries '$qw': $(tr '\n' ' ' < $D/wenv-qed1/out | cut -c1-400)"
fi
qd=$(field $D/devnull-qed1/B.vo opacity_queries)
if [ "$(cat $D/devnull-qed1/rc)" = ok ] && [ "$qd" = "$q_qed" ]; then
  pass "B_devnull: with ROCQ_OPACITYLOG_FILE=/dev/null outside, the compile still records the workers' read: $qd"
else
  bad "B_devnull ($(cat $D/devnull-qed1/rc)): opacity_queries '$qd': $(tr '\n' ' ' < $D/devnull-qed1/out | cut -c1-300)"
fi
nulls parnotmp "B_parnotmp: a par: body read with TMPDIR a missing directory (the workers get an empty variable)"
qs=$(field $D/secpar-qed1/B.vo opacity_queries)
if [ "$(cat $D/secpar-qed1/rc)" = ok ] && [ "$qs" = "$q_qed" ]; then
  pass "B_secpar: after Section S. Require A. End S., a par: worker reads A.c's body and records it: $qs"
else
  bad "B_secpar ($(cat $D/secpar-qed1/rc)): opacity_queries '$qs': $(tr '\n' ' ' < $D/secpar-qed1/out | cut -c1-400)"
fi
qmf=$(field $D/modfail-qed1/B.vo opacity_queries)
if [ "$(cat $D/modfail-qed1/rc)" = ok ] && [ "$qmf" = "$q_qed" ]; then
  pass "B_modfail: after Module M. Require A. Fail Require Y.X. End M. (Y.X's file holds A.A, from qed2), a par: worker reads the loaded A.c's body (shape 1) and records it: $qmf"
else
  bad "B_modfail ($(cat $D/modfail-qed1/rc)): opacity_queries '$qmf'; $(grep -o 'A.c is not the loaded A.c' $D/modfail-qed1/out | head -1); $(tr '\n' ' ' < $D/modfail-qed1/out | cut -c1-400)"
fi
for nd in "stock-adm:B_stock (Transparent A.c on an axiom)" "stockpar-qed1:B_stockpar (a par: body read)"; do
  d=$D/${nd%%:*}
  if [ "$(cat $d/rc)" = ok ]; then
    pass "${nd#*:}: a coqc without -location-free-label and with ROCQ_OPACITYLOG_FILE=/nonexistent/x compiles"
  else
    bad "${nd#*:}: a coqc without the flag failed on the inherited variable: $(tr '\n' ' ' < $d/out | cut -c1-400)"
  fi
done
qa18=$(field $D/asyncenv-qed1/B.vo opacity_queries)
if [ "$(cat $D/asyncenv-qed1/rc)" = ok ] && [ "$qa18" = "$q_qed" ]; then
  pass "B_asyncenv: a proof worker that got extra-env naming /dev/null still records into the compile's log: $qa18"
else
  bad "B_asyncenv ($(cat $D/asyncenv-qed1/rc)): opacity_queries '$qa18': $(tr '\n' ' ' < $D/asyncenv-qed1/out | cut -c1-400)"
fi
# Each compile's log is private and removed at exit: this fixture's TMPDIR is empty.
left=$(find "$TMPDIR" -mindepth 1 2>/dev/null | head -3 | tr '\n' ' ')
if [ -z "$left" ]; then
  pass "this fixture's TMPDIR ($TMPDIR) is empty: every opacity log was removed"
else
  bad "opacity logs left in $TMPDIR: $left"
fi

exit $fail
