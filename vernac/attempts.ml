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

type request =
  | Require_qualified of { root : string option; name : string }
  | Require_absolute of string
  | Load of string
  | Ml_module of string

type probe = { dir : string; file : string; exists : bool }

type attempt = {
  request : request;
  probes : probe list;            (* every candidate looked for, in order *)
  library : DirPath.t option;     (* a Require: the library it resolved to *)
  found : string list;            (* the files the attempt read *)
  loadpath : int;                 (* index in [loadpaths], or -1 (a plugin) *)
}

type t = {
  attempts : attempt list;
  digests : (string * string) list;
  (* SHA-256 (hex) of every file in [found], when the library was saved *)
  loadpaths : (string * string list option) list list;
  (* per load path searched: each directory with its subdirectory names *)
}

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let sha_file f =
  match In_channel.with_open_bin f In_channel.input_all with
  | s -> hex (Libkey.sha256 s)
  | exception Sys_error _ -> "unreadable"

(* As Loadpath.select_vo_file reads a candidate: a .vos counts only when it
   is not empty. *)
let probe_exists dir file =
  let f = Filename.concat dir file in
  Sys.file_exists f &&
  (not (Filename.check_suffix file ".vos") || (Unix.stat f).Unix.st_size > 0)

(* The subdirectories of a load path directory that a recursive [-R] or
   [-Q] scan would turn into load path entries: not hidden, and named by a
   Rocq identifier (Loadpath.add_vo_path skips the others). A hidden one
   such as .coq-native, which a compile creates, is not listed, so that two
   compiles of the same file in the same tree give the same record. *)
let subdirs d =
  let entry n =
    n <> "" && n.[0] <> '.' && Sys.is_directory (Filename.concat d n) &&
    (match Id.of_string n with _ -> true | exception e when CErrors.noncritical e -> false)
  in
  match Sys.readdir d with
  | names -> Some (List.sort String.compare (List.filter entry (Array.to_list names)))
  | exception Sys_error _ -> None

(* Whether attempts are logged at all: only under -location-free-label
   ([Library.set_location_free_label]). Off, nothing is probed or hashed. *)
let enabled = ref false
let set_enabled b = enabled := b

(* The log of the library being compiled. Not a summary: a rollback does not
   remove an attempt. Each entry keeps the load path searched. *)
let log : (attempt * string list) list ref = ref []

let reset () = log := []

let load_path () = List.map Loadpath.physical (Loadpath.get_load_paths ())

let record request ~probes ~library ~found =
  if !enabled then begin
    let probes = List.map (fun (dir, file) -> { dir; file; exists = probe_exists dir file }) (probes ()) in
    let a = { request; probes; library; found = Option.List.cons found []; loadpath = 0 } in
    log := (a, load_path ()) :: !log
  end

(* Each entry point tests [enabled] before it builds anything, so that
   without the option a Require, Load or Declare ML Module does no work
   here beyond that test. *)
let record_require_qualified ~root qid ~probes ~library ~found =
  if !enabled then
    let root = Option.map DirPath.to_string root in
    record (Require_qualified { root; name = Libnames.string_of_qualid qid }) ~probes ~library ~found

let record_require_absolute dir ~probes ~found =
  if !enabled then
    record (Require_absolute (DirPath.to_string dir)) ~probes ~library:(Some dir) ~found

let record_load name ~probes ~found =
  if !enabled then record (Load name) ~probes ~library:None ~found

let plugin_resolver : (string -> string list option) ref = ref (fun _ -> None)
let set_plugin_resolver f = plugin_resolver := f

let plugin_files p = Option.default [] (!plugin_resolver p)

let record_ml_module p =
  if !enabled then begin
    let a = { request = Ml_module p; probes = []; library = None; found = plugin_files p; loadpath = -1 } in
    log := (a, []) :: !log
  end

let finish ~loaded ~loaded_plugin =
  let keep (a, _) = match a.request with
    | Require_qualified _ | Require_absolute _ ->
      (match a.library with Some dp -> not (loaded dp) | None -> true)
    | Load _ -> true
    | Ml_module p -> not (loaded_plugin p)
  in
  match List.filter keep (List.rev !log) with
  | [] -> None
  | kept ->
    let snapshots = ref [] in
    let index dirs =
      let rec find i = function
        | [] -> snapshots := !snapshots @ [dirs]; i
        | d :: l -> if List.equal String.equal d dirs then i else find (i + 1) l
      in
      find 0 !snapshots
    in
    let attempts = List.map (fun (a, dirs) ->
        match a.request with
        | Ml_module _ -> a
        | _ -> { a with loadpath = index dirs }) kept
    in
    let loadpaths = List.map (List.map (fun d -> (d, subdirs d))) !snapshots in
    let files = List.sort_uniq String.compare (List.concat_map (fun a -> a.found) attempts) in
    Some { attempts; digests = List.map (fun f -> (f, sha_file f)) files; loadpaths }

let describe_request = function
  | Require_qualified { root; name } ->
    "an attempted Require of " ^ (match root with Some r -> "From " ^ r ^ " " | None -> "") ^ name
  | Require_absolute name -> "an attempted Require of " ^ name
  | Load name -> "an attempted Load of " ^ name
  | Ml_module p -> "an attempted Declare ML Module of " ^ p

let describe t =
  List.map (fun a ->
      Printf.sprintf "%s: probes [%s] read [%s]" (describe_request a.request)
        (String.concat "; " (List.map (fun p ->
             Filename.concat p.dir p.file ^ (if p.exists then " found" else " absent")) a.probes))
        (String.concat "; " (List.map (fun f ->
             f ^ " sha256 " ^ Option.default "?" (List.assoc_opt f t.digests)) a.found)))
    t.attempts

let tag : t Libobject.Dyn.tag =
  let open Libobject in
  declare_object_full
    { (default_object "ATTEMPTS") with
      classify_function = (fun _ -> Keep);
      (* Paths, names and digests: no source location. *)
      interface_key = Key_as_is }

let inject t = Libobject.Dyn.Dyn (tag, t)

let find ((_, { Libobject.keep_objects }, _) : Declaremods.library_objects) : t option =
  List.find_map (function
      | Libobject.AtomicObject (Libobject.Dyn.Dyn (tg, v)) ->
        (match Libobject.Dyn.eq tg tag with Some CSig.Refl -> Some (v : t) | None -> None)
      | _ -> None)
    keep_objects
