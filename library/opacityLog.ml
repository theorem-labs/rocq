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
   compiled, and also of the opaque table that a proof body is read from.

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
   (Every other reader in this tree, and in each plugin of the audited plugin
   set, was checked for this distinction the same way. Nothing here enforces
   that set. Not every opaque read is logged either: [Global.force_proof] and
   [Global.body_of_constant_body] log nothing, and [Print] reads a proof
   through the first.
   What holds is narrower: a reader in this tree or that set whose answer can
   change whether a compile succeeds or what it produces either logs here or
   answers the same for an axiom and an opaque proof; how long a read takes,
   and what a printer shows, are outside it, see vernac/libkeyObjects.mli.)
   The library label
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
   private directory (mode 0700) and its log inside it (mode 0600) when the
   flag is set, before any tactic runs, through an [O_CREAT|O_EXCL]
   descriptor, and names it by an absolute path: a relative TMPDIR is taken
   from the directory current at that moment, so a later [Cd] does not change
   which file a worker, the read-back or the
   removal names. It never writes its records into a log it
   did not create (one named by an outer process, or a sink such as
   /dev/null, would lose them). A spawned worker gets the log's path and its
   device and inode from the worker pool, which sets [ROCQ_OPACITYLOG_FILE]
   and [ROCQ_OPACITYLOG_IDENTITY] to the values [worker_env_value] and
   [worker_identity_env_value] give, whatever the inherited environment or
   [-async-proofs-private-flags] say ([AsyncTaskQueue.spawn]): the log the
   spawning process has open (the owner's, a worker's or a forked child's),
   in a worker that has not opened it yet the values it captured at startup,
   and otherwise empty, so the workers of a coqc without
   [-location-free-label] record nothing. A worker clears both variables at
   startup, then opens its captured path at its first record and keeps the
   descriptor only when its device and inode are those it was given; another
   file at the path, even one put there only while the worker opens it, is
   refused like a missing one. The compiling process clears any inherited
   values too. Only a worker ([Flags.async_proofs_is_worker]) captures the
   variables; a forked child inherits the open descriptor instead, and any
   other process ignores them, so a coqc without the flag never writes to, or
   fails on, a log an outer process named. Only these append: the owner, a
   worker (through the captured values) and a forked child of either (through
   the descriptor). A
   process outside them -- a separate rocq process a plugin starts by its own
   means, rather than through the worker pool -- is outside the log; no plugin
   of the audited plugin set starts one, and nothing here keeps a plugin
   outside that set from starting one. Each of
   them appends each record to that file as one line with one write on an
   [O_APPEND] descriptor, so the lines of several processes do not
   interleave, besides keeping it in memory. A line writes each name in
   hexadecimal ([encode_line]), so a name can hold any byte (a plugin can
   make an identifier with a tab or a newline, [Names.Id.of_string_soft])
   and still read back as itself, never as another record or as an absent
   field. The compiling process reads the
   file back with its own records ([get]) when it saves the library and
   removes the log and its private directory at exit, but only when every
   component of TMPDIR was secure at creation ([path_secure]: owned by this
   uid or root, and either not group/other-writable or sticky) and lstat of
   each still matches the recorded dev:ino; a substitute at the log name
   (a different dev:ino) or an insecure parent leaves both. A child's records
   reach it only when the child writes them
   before that read-back: a plugin whose forked child outlives the tactic
   that forked it, and whose result reaches the compile later, is outside
   the log (the plugins of the audited set wait for their children). A record a
   forked child made for a candidate the parent then dropped is kept: that
   only makes the keep rule rebuild more. A log that could not be created,
   written or read back whole (every line a record, the last one ended)
   makes [get] answer [None], and the library is saved with no [keepfacts]
   segment, which the keep rule rebuilds. So does a log whose file is no
   longer the one the compiling process made: [get] reads the file only
   while its device and inode are the ones recorded when it was made, so
   another file put at its path (an empty one, or a copy of its bytes) is
   refused, and only while it starts with the line that names its format,
   which the file has from its creation, so the log emptied in place is
   refused too. These checks do not detect a rewrite of the log's own file
   that keeps its first line and drops or replaces records: only a process
   that can write the file (one of this user) can make one, the processes
   above only append, and nothing in this tree or the audited plugin set
   writes to the log otherwise. A worker that cannot open the log the
   variables name, or a worker or child that cannot write a record to
   it, raises an error before the caller gets the answer it records
   ([record], [record_body_read]), so its tactic fails having used nothing
   unrecorded. *)

type query = {
  constant : string;
  library : string option;
  opaque : bool;
  table : string option;
}

let enabled = ref false

(* The log file: its path, a descriptor opened on it in this process, the pid
   of the process that created it (only that one reads it back and removes
   it; a forked child inherits these refs, not the ownership), the device and
   inode of the file it created (its read-back reads no other file), and
   whether a write or the creation failed in the owner. The private directory
   is held by the owner's cleanup closure. *)
let path : string option ref = ref None
let fd : Unix.file_descr option ref = ref None
let owner_pid : int option ref = ref None
let identity : (int * int) option ref = ref None
let broken = ref false
let tried_env = ref false

(* A worker reads these once during its startup, then clears them from its
   environment. A child worker gets them explicitly again from the state
   below, not from its environment. *)
let worker_environment : (string * string option) option ref = ref None
let worker_environment_captured = ref false

(* The first line of the log: written when the log is made and again when
   [reset] empties it, so a file that does not start with it, an empty one
   among them, is not a log. Its number names the line format below. *)
let header = "rocq-opacity-log 2\n"

let env_var = "ROCQ_OPACITYLOG_FILE"
let identity_env_var = "ROCQ_OPACITYLOG_IDENTITY"

let string_of_identity (dev, ino) = Printf.sprintf "%d:%d" dev ino

let identity_of_string = function
  | s ->
    (match String.split_on_char ':' s with
     | [dev; ino] ->
       (try Some (int_of_string dev, int_of_string ino) with Failure _ -> None)
     | _ -> None)

let capture_worker_environment () =
  if not !worker_environment_captured then begin
    worker_environment_captured := true;
    if Flags.async_proofs_is_worker () then begin
      let p = Sys.getenv_opt env_var in
      let id = Sys.getenv_opt identity_env_var in
      Unix.putenv env_var "";
      Unix.putenv identity_env_var "";
      match p with
      | Some p when p <> "" -> worker_environment := Some (p, id)
      | _ -> ()
    end
  end

let open_append p =
  try Some (Unix.openfile p [Unix.O_WRONLY; Unix.O_APPEND; Unix.O_CLOEXEC] 0o600)
  with Unix.Unix_error _ -> None

(* Writes [s] to [d] with one write; [false] when it is not written whole. *)
let write_whole d s =
  try Unix.write_substring d s 0 (String.length s) = String.length s
  with Unix.Unix_error _ -> false

type checked_path = {
  canonical : string;
  stable : bool;
}

(* Secure-path walk: resolve [root] once, then lstat every directory from /
   down to that exact canonical path. Each directory must be owned by this uid
   or root and either not group/other-writable or sticky. When realpath fails,
   creation refuses; when the walk fails, creation still uses the canonical
   path but cleanup leaves the log and directory in place. *)
let path_secure root =
  let uid = Unix.getuid () in
  let component_ok p =
    match Unix.lstat p with
    | { Unix.st_kind = Unix.S_DIR; st_uid; st_perm; _ } ->
      let mine_or_root = st_uid = uid || st_uid = 0 in
      let no_other_write = st_perm land 0o022 = 0 in
      let sticky = st_perm land 0o1000 <> 0 in
      mine_or_root && (no_other_write || sticky)
    | _ | exception Unix.Unix_error _ -> false
  in
  match Unix.realpath root with
  | exception Unix.Unix_error _ -> None
  | canonical when Filename.is_relative canonical -> None
  | canonical ->
    let parts = String.split_on_char '/' canonical in
    let rec walk prefix = function
      | [] -> true
      | "" :: rest -> walk prefix rest
      | comp :: rest ->
        let dir = if prefix = "/" then "/" ^ comp else prefix ^ "/" ^ comp in
        component_ok dir && walk dir rest
    in
    Some { canonical; stable = component_ok "/" && walk "/" parts }

(* A directory that only this uid can enter. [mkdir] makes its name atomically
   and retries a collision; the log's fixed name is then private to it. *)
let make_private_dir root =
  let random = Random.State.make_self_init () in
  let rec make tries =
    if tries = 0 then
      raise (Unix.Unix_error (Unix.EEXIST, "mkdir", root))
    else
      let suffix =
        Printf.sprintf "%08x%08x"
          (Random.State.bits random) (Random.State.bits random)
      in
      let dir = Filename.concat root (".rocq-opacitylog-" ^ suffix) in
      match Unix.mkdir dir 0o700 with
      | () -> dir
      | exception Unix.Unix_error (Unix.EEXIST, _, _) -> make (tries - 1)
  in
  make 128

type log_creation =
  | Open_failed
  | Opened_failed of string * (int * int)
  | Opened of Unix.file_descr * string * (int * int)

let create_log_result dir =
  let p = Filename.concat dir "log" in
  match Unix.openfile p
          [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL; Unix.O_APPEND; Unix.O_CLOEXEC] 0o600 with
  | exception Unix.Unix_error _ -> Open_failed
  | d ->
    let close () = try Unix.close d with Unix.Unix_error _ -> () in
    match Unix.fstat d with
    | exception Unix.Unix_error _ -> close (); Open_failed
    | { Unix.st_dev; st_ino; _ } ->
      let log_id = (st_dev, st_ino) in
      if write_whole d header then Opened (d, p, log_id)
      else begin close (); Opened_failed (p, log_id) end

(* Create the log inside [dir]. Returns [(fd, path, log_id)] on success. *)
let create_log dir =
  match create_log_result dir with
  | Opened (d, p, log_id) -> Some (d, p, log_id)
  | Open_failed | Opened_failed _ -> None

(* Remove the log and its private directory when the path was secure and lstat
   still matches each recorded identity. [stable] was computed over every
   component of canonical TMPDIR at creation. When it is false, or lstat
   disagrees, nothing is removed: a small leak, never the wrong file. *)
let cleanup_log ~stable dir dir_id p log_id =
  if stable then begin
    (match Unix.lstat p with
     | { Unix.st_dev; st_ino; _ } when (st_dev, st_ino) = log_id ->
       (try Sys.remove p with Sys_error _ -> ())
     | _ | exception Unix.Unix_error _ -> ());
    (match Unix.lstat dir with
     | { Unix.st_dev; st_ino; _ } when (st_dev, st_ino) = dir_id ->
       (try Unix.rmdir dir with Unix.Unix_error _ -> ())
     | _ | exception Unix.Unix_error _ -> ())
  end

let owner () = match !owner_pid with Some p -> p = Unix.getpid () | None -> false

(* A worker opens the log it captured at startup, once, on its first record;
   a forked child of a process with a log has its descriptor already. The
   worker accepts an opened path only when it is the device and inode its
   parent captured. *)
let open_worker_log p expected =
  match open_append p with
  | None -> None
  | Some d ->
    (match Unix.fstat d with
     | { Unix.st_dev; st_ino; _ } when expected = (st_dev, st_ino) -> Some d
     | _ -> (try Unix.close d with Unix.Unix_error _ -> ()); None
     | exception Unix.Unix_error _ -> (try Unix.close d with Unix.Unix_error _ -> ()); None)

let current_fd () =
  capture_worker_environment ();
  match !fd with
  | Some _ as d -> d
  | None ->
    if not !tried_env then begin
      tried_env := true;
      match !worker_environment with
      | Some (p, expected) ->
        (* A missing or malformed identity is a refusal, not disabled
           logging: leaving [path] set makes [append_to_log] raise. *)
        path := Some p;
        (match Option.bind expected identity_of_string with
         | Some expected ->
           (match open_worker_log p expected with
            | Some d -> identity := Some expected; fd := Some d
            | None -> ())
         | None -> ())
      | None -> ()
    end;
    !fd

let set_enabled b =
  capture_worker_environment ();
  enabled := b;
  if b && not (owner ()) then begin
    (* The owner makes a private 0700 directory in TMPDIR, then creates the
       log through [create_log] with O_CREAT|O_EXCL; no path is reopened.
       Cleanup removes the log and directory only when every component of
       TMPDIR was secure at creation ([path_secure]) and lstat of each still
       matches ([cleanup_log]). *)
    tried_env := true;
    fd := None;
    path := None;
    identity := None;
    owner_pid := Some (Unix.getpid ());
    Unix.putenv env_var "";
    Unix.putenv identity_env_var "";
    let failed () =
      path := None; identity := None; broken := true;
      Unix.putenv env_var ""; Unix.putenv identity_env_var ""
    in
    match
      let root = Filename.get_temp_dir_name () in
      let root = if Filename.is_relative root then Filename.concat (Sys.getcwd ()) root else root in
      path_secure root
    with
    | Some { canonical; stable } ->
      let dir = make_private_dir canonical in
      let dir_id = match Unix.lstat dir with
        | { Unix.st_dev; st_ino; _ } -> Some (st_dev, st_ino)
        | exception Unix.Unix_error _ -> None
      in
      (match create_log_result dir with
       | Open_failed ->
         (* O_EXCL may have failed because another file was there. Remove
            only the empty private dir, after the same stable/dev:ino rule. *)
         (match stable, dir_id with
          | true, Some did ->
            (match Unix.lstat dir with
             | { Unix.st_dev; st_ino; _ } when (st_dev, st_ino) = did ->
               (try Unix.rmdir dir with Unix.Unix_error _ -> ())
             | _ | exception Unix.Unix_error _ -> ())
          | _ -> ());
         failed ()
       | Opened_failed (p, log_id) ->
         (match dir_id with
          | Some did -> cleanup_log ~stable dir did p log_id
          | None -> ());
         failed ()
       | Opened (d, p, log_id) ->
         identity := Some log_id; path := Some p; fd := Some d;
         at_exit (fun () ->
             if owner () then
               match dir_id with
               | Some did -> cleanup_log ~stable dir did p log_id
               | None -> ()))
    | None -> failed ()
  end

let worker_env_value () =
  capture_worker_environment ();
  match !fd, !path with
  | Some _, Some p -> p
  | _ ->
    (match !worker_environment with
     | Some (p, _) -> p
     | None -> "")

let worker_identity_env_value () =
  capture_worker_environment ();
  match !fd, !identity with
  | Some _, Some id -> string_of_identity id
  | _ ->
    (match !worker_environment with
     | Some (_, Some id) -> id
     | Some (_, None) | None -> "")

let queries : query list ref = ref []

let reset () =
  queries := [];
  if owner () then
    match !fd with
    | Some d ->
      (* Through this process's own descriptor, so it is the file it made
         whatever its path names now; then the first line again. *)
      (match Unix.ftruncate d 0 with
       | () -> if not (write_whole d header) then broken := true
       | exception Unix.Unix_error _ -> broken := true)
    | None -> ()

let rec mpfile_root = function
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> mpfile_root mp
  | ModPath.MPbound _ -> None

(* A name in hexadecimal, two lowercase digits a byte, and back; [unhex]
   refuses any other spelling, so each name has exactly one. *)
let hex s =
  let digits = "0123456789abcdef" in
  String.init (2 * String.length s) (fun i ->
      let c = Char.code s.[i / 2] in
      digits.[if i mod 2 = 0 then c lsr 4 else c land 15])

let unhex s =
  let digit c = match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
    | _ -> raise Exit
  in
  if String.length s mod 2 <> 0 then None
  else
    try Some (String.init (String.length s / 2) (fun i ->
        Char.chr (16 * digit s.[2 * i] + digit s.[2 * i + 1])))
    with Exit -> None

let encode_line q =
  let opt = function None -> "-" | Some s -> "+" ^ hex s in
  String.concat "\t"
    ["R"; hex q.constant; opt q.library; (if q.opaque then "1" else "0"); opt q.table] ^ "\n"

let decode_line l =
  let opt s =
    if String.equal s "-" then Some None
    else if String.starts_with ~prefix:"+" s then
      Option.map (fun n -> Some n) (unhex (String.sub s 1 (String.length s - 1)))
    else None
  in
  match String.split_on_char '\t' l with
  | ["R"; c; lib; o; t] ->
    (match unhex c, opt lib, o, opt t with
     | Some constant, Some library, ("0" | "1"), Some table when constant <> "" ->
       Some { constant; library; opaque = String.equal o "1"; table }
     | _ -> None)
  | _ -> None

let cannot_write why =
  CErrors.user_err Pp.(str "Cannot write a record to the keep rule's opacity log " ++
                       str (Option.default "" !path) ++ str ": " ++ str why ++ str ".")

(* Appends [q]'s line to the log with one write. A process with no log to
   write to (none named, or the owner whose log could not be made) adds
   nothing here; the owner's [get] then answers [None]. *)
let append_to_log q =
  match current_fd () with
  | None ->
    if Option.has_some !path then
      if owner () then broken := true else cannot_write "it cannot be opened"
  | Some d ->
    let l = encode_line q in
    let ok = write_whole d l in
    if not ok then
      if owner () then broken := true else cannot_write "the write failed"

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

(* The text of the file at [p], or [None] when it cannot be read or is not
   the file the owner made: another device or inode. *)
let read_own_log p =
  match Unix.openfile p [Unix.O_RDONLY; Unix.O_CLOEXEC] 0 with
  | exception Unix.Unix_error _ -> None
  | d ->
    let ic = Unix.in_channel_of_descr d in
    Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
        match Unix.fstat d with
        | exception Unix.Unix_error _ -> None
        | { Unix.st_dev; st_ino; _ } ->
          if !identity <> Some (st_dev, st_ino) then None
          else try Some (In_channel.input_all ic) with Sys_error _ -> None)

let get () =
  if !broken then None
  else match !path with
    | None -> if !enabled then None else Some !queries
    | Some p ->
      match read_own_log p with
      | None -> None
      | Some text when not (String.starts_with ~prefix:header text) ->
        None (* not a log: emptied, or written over *)
      | Some text when String.length text > String.length header
                       && text.[String.length text - 1] <> '\n' ->
        None (* a torn last line *)
      | Some text ->
        let rec parse acc = function
          | [] | [""] -> Some acc
          | l :: rest ->
            match decode_line l with
            | Some q -> parse (q :: acc) rest
            | None -> None
        in
        let n = String.length header in
        Option.map (fun from_file -> from_file @ !queries)
          (parse [] (String.split_on_char '\n' (String.sub text n (String.length text - n))))
