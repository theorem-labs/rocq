(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(* Records of whether a constant was an axiom or an opaque proof when a
   command whose outcome depends on that distinction ran while a library was
   compiled (design D18, dispatch://INFRA-361, Astra review 2 blocker 1).

   The observers, each of which logs here before it decides:
   - [Tactics.Redexpr.check_not_fully_opaque] rejects a non-opaque strategy
     command (`Transparent c.`, `Strategy expand [c].`) on a constant [c]
     whose body is an opaque proof ([OpaqueDef]), but accepts it on an axiom
     ([Undef]);
   - extraction warns about an axiom to realize, or about an opaque proof it
     accessed, and either warning can be an error
     ([Extraction.extract_constant]);
   - [Functional Scheme] makes the principle it generates an opaque proof
     when the function's equation lemma is one, and a transparent definition
     otherwise ([Gen_principle.make_scheme]);
   - [Global.body_of_constant], the plugin API for a constant's body, answers
     [None] for an axiom and the forced body for an opaque proof.
   (The sweep of every other reader in the tree and in the plugins the BET
   image installs is design D18's observer sweep.) The library label
   ([Vernac.LibkeyObjects]) deliberately gives an axiom and an opaque proof
   of the library's own signature the same label, so an edit that completes
   an admitted dependency constant with a [Qed] proof keeps the dependency's
   label, yet a real
   recompile of a dependent that ran such a command on that constant could
   now fail, or stop failing. A [local] strategy command (the default of
   [Opacity]) writes no persistent object, so a dependent's [.vo] does not
   record it. So the fact is logged here, outside the state a [Fail] rolls
   back, and [Vernac.Library] stores the foreign ones in the saved library
   ([KeepFacts]) for the keep rule to revalidate against the dependency's
   current status. Only a constant whose body is [Undef None] or [OpaqueDef]
   is logged: those are the two forms the label blinds into one, and a
   constant of any other form cannot become the other kind while the label
   stays equal, so a record of it could only make the keep rule rebuild a
   dependent forever (`Transparent Nat.add.` on a transparent definition). A
   library that makes no such query gets no record, so its file is what a
   stock [coqc] writes.

   An extraction with AccessOpaque (the default) also reads an opaque proof's
   BODY, and what it extracts depends on that body, which no label covers; so
   does [Global.body_of_constant]'s caller, and the walk that computes a
   library's assumption closures ([KeepFacts]), whose result is stored. Such a
   read is logged with the library whose opaque table it read
   ([record_body_read]): for a copy that a
   module operation did not strengthen (a functor application, an [Include]
   of one, at any depth, a sealed module whose implementation is such an
   expression) that table's library can differ from the one holding the
   constant read. The library's [foreign_opaque_libraries]
   ([LibkeyObjects.axiom_report]) names it only for a copy whose [Indirect]
   reference the compiled form keeps, not for one read from a sealed
   module's expression.

   Several processes. A record can be made outside the compiling process: a
   [par:] tactic runs in a [rocqworker] process ([Partac]), an [-async-proofs]
   proof in another, and a plugin tactic can fork (coq-hammer-tactics' [best]
   tries each candidate in a forked child); none of them sends its records
   back. So under [-location-free-label] the compiling process creates a
   private log file ([Filename.temp_file], mode 0600, in TMPDIR) when the flag
   is set, before any tactic runs, and exports its path in [ROCQ_OPACITYLOG_FILE];
   a spawned worker inherits the variable (the worker pool passes the
   environment, [AsyncTaskQueue]), a forked child the open descriptor. Every
   process that has the variable appends each record to that file as one line
   with one write on an [O_APPEND] descriptor, so the lines of several
   processes do not interleave, besides keeping it in memory. The compiling
   process reads the file back with its own records ([get]) when it saves the
   library and removes it at exit. A record a forked child made for a
   candidate the parent then dropped is kept: that only makes the keep rule
   rebuild more. A log that could not be created, written or read back makes
   [get] answer [None], and the library is saved with no [keepfacts] segment,
   which the keep rule rebuilds; a process other than the compiling one that
   cannot write a record fails its tactic. A coqc started with the variable
   already set (a worker that parses [-location-free-label] too, or a coqc
   that another one started) appends to that file and does not own it; its
   records reach the owner's library too, which again only makes the keep
   rule rebuild more. *)

type query = {
  constant : string;
  library : string option;
  opaque : bool;
  table : string option;
}

let env_var = "ROCQ_OPACITYLOG_FILE"

let enabled = ref false

(* The log file: its path, a descriptor opened on it in this process, the
   pid of the process that created it (only that one reads it back and
   removes it; a forked child inherits these refs, not the ownership), and
   whether a write or the creation failed. *)
let path : string option ref = ref None
let fd : Unix.file_descr option ref = ref None
let owner_pid : int option ref = ref None
let broken = ref false
let tried_env = ref false

let open_append p =
  try Some (Unix.openfile p [Unix.O_WRONLY; Unix.O_APPEND; Unix.O_CLOEXEC] 0o600)
  with Unix.Unix_error _ -> broken := true; None

(* A process that did not create the log opens the one its environment names,
   once, on its first record. *)
let current_fd () =
  match !fd with
  | Some _ as d -> d
  | None ->
    if not !tried_env then begin
      tried_env := true;
      match Sys.getenv_opt env_var with
      | Some p when p <> "" -> path := Some p; fd := open_append p
      | Some _ | None -> ()
    end;
    !fd

let owner () = match !owner_pid with Some p -> p = Unix.getpid () | None -> false

let set_enabled b =
  enabled := b;
  if b && Option.is_empty !fd then
    match Sys.getenv_opt env_var with
    | Some p when p <> "" -> tried_env := true; path := Some p; fd := open_append p
    | Some _ | None ->
      (* created empty, mode 0600, in TMPDIR *)
      match Filename.temp_file "rocq-opacitylog" ".log" with
      | p ->
        path := Some p;
        owner_pid := Some (Unix.getpid ());
        tried_env := true;
        fd := open_append p;
        Unix.putenv env_var p;
        at_exit (fun () -> if owner () then try Sys.remove p with Sys_error _ -> ())
      | exception Sys_error _ -> broken := true

let queries : query list ref = ref []

let reset () =
  queries := [];
  if owner () then
    match !path with
    | Some p -> (try Unix.truncate p 0 with Unix.Unix_error _ -> broken := true)
    | None -> ()

let rec mpfile_root = function
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> mpfile_root mp
  | ModPath.MPbound _ -> None

let line_of q =
  let opt = function Some s -> s | None -> "-" in
  String.concat "\t" ["R"; q.constant; opt q.library; (if q.opaque then "1" else "0"); opt q.table] ^ "\n"

let query_of_line l =
  let opt = function "-" -> Some None | "" -> None | s -> Some (Some s) in
  match String.split_on_char '\t' l with
  | ["R"; c; lib; o; t] when c <> "" ->
    (match opt lib, o, opt t with
     | Some library, ("0" | "1"), Some table ->
       Some { constant = c; library; opaque = String.equal o "1"; table }
     | _ -> None)
  | _ -> None

(* Appends [q]'s line to the log with one write. *)
let append_to_log q =
  match current_fd () with
  | None -> ()
  | Some d ->
    let l = line_of q in
    let ok = try Unix.write_substring d l 0 (String.length l) = String.length l
      with Unix.Unix_error _ -> false in
    if not ok then begin
      broken := true;
      if not (owner ()) then
        CErrors.user_err Pp.(str "Cannot write a record to the keep rule's opacity log " ++
                             str (Option.default "" !path) ++ str ".")
    end

let add c ~opaque ~table =
  let q = {
    constant = Constant.to_string c;
    library = Option.map DirPath.to_string (mpfile_root (Constant.modpath c));
    opaque;
    table = Option.map DirPath.to_string table;
  } in
  if !enabled then queries := q :: !queries;
  append_to_log q

let record c (cb : Declarations.constant_body) =
  match cb.Declarations.const_body with
  | Declarations.Undef None -> add c ~opaque:false ~table:None
  | Declarations.OpaqueDef _ -> add c ~opaque:true ~table:None
  | Declarations.Undef (Some _) | Declarations.Def _
  | Declarations.Primitive _ | Declarations.Symbol _ -> ()

let record_body_read c o =
  let (_, _, dp, _) = Opaqueproof.repr o in
  add c ~opaque:true ~table:(Some dp)

let get () =
  if !broken then None
  else match !path with
    | None -> if !enabled then None else Some !queries
    | Some p ->
      match In_channel.with_open_text p In_channel.input_all with
      | exception Sys_error _ -> None
      | text ->
        let lines = String.split_on_char '\n' text in
        let rec parse acc = function
          | [] -> Some acc
          | [""] -> Some acc
          | l :: rest ->
            match query_of_line l with
            | Some q -> parse (q :: acc) rest
            | None -> None
        in
        Option.map (fun from_file -> from_file @ !queries) (parse [] lines)
