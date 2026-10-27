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

(* What a load path entry's directory holds that the next start could turn
   into entries. The constructors without argument come first, so that a
   record written by 76d8b5da (where [string list option] stood here) reads
   [None] as [Unreadable]. *)
type scan =
  | Unreadable                (* a recursive entry whose directory could not be read *)
  | Not_recursive             (* the working directory: its subdirectories never become entries *)
  | Subdirs of string list    (* a recursive entry: the subdirectories a scan makes entries *)

type t = {
  attempts : attempt list;
  digests : (string * string) list;
  (* SHA-256 (hex) of every file in [found], when the library was saved *)
  loadpaths : (string * scan) list list;
  (* per load path searched: each directory with its scan *)
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
   compiles of the same file in the same tree give the same record. Only an
   entry that a recursive scan made is listed: the working directory's
   other subdirectories (other builds beside this one) are no input. *)
let scan (d, recursive) =
  let entry n =
    n <> "" && n.[0] <> '.' && Sys.is_directory (Filename.concat d n) &&
    (match Id.of_string n with _ -> true | exception e when CErrors.noncritical e -> false)
  in
  if not recursive then (d, Not_recursive)
  else match Sys.readdir d with
    | names -> (d, Subdirs (List.sort String.compare (List.filter entry (Array.to_list names))))
    | exception Sys_error _ -> (d, Unreadable)

(* Whether attempts are logged at all: only under -location-free-label
   ([Library.set_location_free_label]). Off, nothing is probed or hashed. *)
let enabled = ref false
let set_enabled b = enabled := b

(* The log of the library being compiled. Not a summary: a rollback does not
   remove an attempt. Each entry keeps the load path searched: each
   directory, and whether a recursive scan made it an entry. *)
let log : (attempt * (string * bool) list) list ref = ref []

let reset () = log := []

let load_path () =
  List.map (fun p -> (Loadpath.physical p, Loadpath.recursive p)) (Loadpath.get_load_paths ())

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
        | d :: l -> if List.equal (fun (d, r) (d', r') -> String.equal d d' && Bool.equal r r') d dirs
          then i else find (i + 1) l
      in
      find 0 !snapshots
    in
    let attempts = List.map (fun (a, dirs) ->
        match a.request with
        | Ml_module _ -> a
        | _ -> { a with loadpath = index dirs }) kept
    in
    let loadpaths = List.map (List.map scan) !snapshots in
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

let json_version = 1

exception Not_utf_8 of string

(* One JSON value is written into [b] by each function below; [fields]
   writes an object from (key, writer) pairs, in that order. *)
let to_json t =
  let b = Buffer.create 1024 in
  let str s =
    if not (String.is_valid_utf_8 s) then raise (Not_utf_8 s);
    Buffer.add_char b '"';
    String.iter (function
        | '"' -> Buffer.add_string b "\\\""
        | '\\' -> Buffer.add_string b "\\\\"
        | c when Char.code c < 0x20 -> Printf.bprintf b "\\u%04x" (Char.code c)
        | c -> Buffer.add_char b c) s;
    Buffer.add_char b '"'
  in
  let int n = Buffer.add_string b (string_of_int n) in
  let bool x = Buffer.add_string b (if x then "true" else "false") in
  let opt f = function None -> Buffer.add_string b "null" | Some x -> f x in
  let list f l =
    Buffer.add_char b '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; f x) l;
    Buffer.add_char b ']'
  in
  let fields l =
    Buffer.add_char b '{';
    List.iteri (fun i (k, f) ->
        if i > 0 then Buffer.add_char b ',';
        str k; Buffer.add_char b ':'; f ()) l;
    Buffer.add_char b '}'
  in
  let request = function
    | Require_qualified { root; name } ->
      fields [("kind", fun () -> str "require_qualified"); ("root", fun () -> opt str root);
              ("name", fun () -> str name)]
    | Require_absolute name -> fields [("kind", fun () -> str "require_absolute"); ("name", fun () -> str name)]
    | Load name -> fields [("kind", fun () -> str "load"); ("name", fun () -> str name)]
    | Ml_module p -> fields [("kind", fun () -> str "ml_module"); ("name", fun () -> str p)]
  in
  let probe { dir; file; exists } =
    fields [("dir", fun () -> str dir); ("file", fun () -> str file); ("exists", fun () -> bool exists)]
  in
  let attempt a =
    fields [("request", fun () -> request a.request);
            ("probes", fun () -> list probe a.probes);
            ("library", fun () -> opt (fun d -> str (DirPath.to_string d)) a.library);
            ("found", fun () -> list str a.found);
            ("loadpath", fun () -> int a.loadpath)]
  in
  let digest (file, sha) = fields [("file", fun () -> str file); ("sha256", fun () -> str sha)] in
  let entry (dir, scan) =
    let dir = ("dir", fun () -> str dir) in
    match scan with
    | Not_recursive -> fields [dir; ("recursive", fun () -> bool false)]
    | Unreadable -> fields [dir; ("recursive", fun () -> bool true); ("subdirs", fun () -> Buffer.add_string b "null")]
    | Subdirs l -> fields [dir; ("recursive", fun () -> bool true); ("subdirs", fun () -> list str l)]
  in
  let record t =
    fields [("attempts", fun () -> list attempt t.attempts);
            ("digests", fun () -> list digest t.digests);
            ("loadpaths", fun () -> list (list entry) t.loadpaths)]
  in
  match fields [("attempts_json_version", fun () -> int json_version); ("record", fun () -> opt record t)] with
  | () -> Ok (Buffer.contents b)
  | exception Not_utf_8 s -> Error ("not valid UTF-8: " ^ String.escaped s)

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
