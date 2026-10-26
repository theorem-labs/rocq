(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names

let chk_pp = Feedback.msg_notice

let pr_dirpath dp = str (DirPath.to_string dp)
let default_root_prefix = DirPath.empty
let split_dirpath d =
  let l = DirPath.repr d in (DirPath.make (List.tl l), List.hd l)
let extend_dirpath p id = DirPath.make (id :: DirPath.repr p)

type section_path = {
  dirpath : string list ;
  basename : string }

type object_file =
| PhysicalFile of CUnix.physical_path
| LogicalFile of section_path

let dir_of_path p =
  DirPath.make (List.map Id.of_string p.dirpath)
let path_of_dirpath dir =
  match DirPath.repr dir with
      [] -> failwith "path_of_dirpath"
    | l::dir ->
        {dirpath=List.map Id.to_string dir;basename=Id.to_string l}
let pr_dirlist dp =
  prlist_with_sep (fun _ -> str".") str (List.rev dp)
let pr_path sp =
  match sp.dirpath with
      [] -> str sp.basename
    | sl -> pr_dirlist sl ++ str"." ++ str sp.basename

(************************************************************************)

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type compilation_unit_name = DirPath.t

(* The boolean beside each proof records that coqc did not type it. The
   checker types every proof regardless, so it never reads the boolean. *)
type seg_proofs = (Opaqueproof.opaque_proofterm * bool) option array

type library_t = {
  library_name : compilation_unit_name;
  library_filename : CUnix.physical_path;
  library_compiled : Safe_typing.compiled_library;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_digest : Safe_typing.vodigest;
}

module LibraryOrdered =
  struct
    type t = DirPath.t
    let compare d1 d2 =
      compare
        (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))
  end

module LibrarySet = Set.Make(LibraryOrdered)
module LibraryMap = Map.Make(LibraryOrdered)

(* This is a map from names to loaded libraries *)
let libraries_table = ref LibraryMap.empty

(* various requests to the tables *)

let find_library dir =
  LibraryMap.find dir !libraries_table

let library_full_filename dir = (find_library dir).library_filename

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library m =
  libraries_table := LibraryMap.add m.library_name m !libraries_table

(* Where a library's table of opaque proofs is, and what the main process
   read of it.

   Where a worker can read that table, it is not parsed when the library
   is interned: the main process reads the bytes from the segment's
   position once, sequentially, and keeps their MD5. Whichever process
   first needs the table reads that same range again and compares its MD5
   with that one, then reads the table as stock does. So the opaque
   proofs, 846 MB of the whole r160 tree against 252 MB of library
   content, stay out of the main process's heap, and no fork copies them,
   except a table that the main process reads itself: for a sealed
   module's constant it cooks ([Mod_checking]), or for a batch it checks
   because it could not fork ([CheckWorkers.spawn]). Where no worker can
   ([-j 1]), the table is parsed when the library is interned, where
   stock parses it, and nothing is hashed: see [intern_opaques].

   The range is the segment and its trailing digest as the table of
   segments declares them, [pos, pos + len + 16), cut at the end of the
   file and at what an [int] holds, and never shorter than the digest.
   Stock never reads [len]: it seeks to [pos] and parses one value, so a
   wrong [len] decides nothing here either. It only chooses how many bytes
   the MD5 covers; the parse reads wherever stock's reads. *)
type opaque_source = {
  src_file : CUnix.physical_path;
  src_pos : int64;      (* of the segment in the file *)
  src_snap : int;       (* the number of bytes hashed, from [src_pos] *)
  src_hash : Digest.t;  (* of the data, from the file's table of segments *)
  src_md5 : Digest.t;   (* of those bytes, by the main process *)
  src_validate : bool;  (* whether stock validates this library's segments *)
}

(* What the main process did with the table when it interned the library:
   hashed its bytes, for the process that will read it, or -- where no
   other process can read it, and where there is nothing to hash --
   parsed it itself, then and there, as stock does. *)
type opaque_read =
| Hashed of opaque_source
| Parsed of seg_proofs

let opaque_sources : opaque_source LibraryMap.t ref = ref LibraryMap.empty

(* The tables this process has read. A worker reads the tables of the
   libraries its batch needs, and keeps them until it exits. *)
let opaque_cache : seg_proofs LibraryMap.t ref = ref LibraryMap.empty

(* The bytes hashed when the library was interned are no longer there, or
   differ: the file changed during the run, which stock, reading it once,
   cannot see. The message has the form of [System.marshal_in]'s. *)
let error_changed f =
  CErrors.user_err
    (str f ++ str ": its opaque proofs changed while it was being checked." ++
     str " Try to rebuild it.")

(* How many bytes a read of [ch] took from [pos], for the counters. *)
let bytes_from ch pos =
  let n = Int64.sub (LargeFile.pos_in ch) pos in
  if Int64.compare n (Int64.of_int max_int) > 0 then max_int else Int64.to_int n

(* What stock reads for one segment, from the channel: for a library it
   validates, the [Analyze] parse of the value at [pos] and a comparison
   of the digest stored after it with [hash]; for one it interns as a
   dependency, the demarshalling of [System.marshal_in].
   [marshal_in_segment] is this on a segment of the table of segments. *)
let marshal_in_at (type a) ~validate ~value ~pos ~hash f ch : a =
  NewProfile.profile "marshal_in_segment" (fun () ->
  let () = LargeFile.seek_in ch pos in
  if validate then
    let v =
      try
        let v = Analyze.parse_channel ch in
        let digest = Digest.input ch in
        let () = if not (String.equal digest hash) then raise_notrace Exit in
        v
      with exn when CErrors.noncritical exn ->
        CErrors.user_err (str "Corrupted file " ++ quote (str f))
    in
    let () = Validate.validate value v in
    let v = Analyze.instantiate v in
    Obj.obj v
  else
    System.marshal_in f ch)
    ()

(* Test only. ROCQCHK_OPAQUE_AT=before:lib:dir stops the process that reads
   the table of the library [lib] before it reads it, so that a test can
   open a race window on purpose, with no timing. The process creates
   [dir/before-pid] and waits for [dir/go], for at most a minute. *)
let opaque_test_at point dp =
  match Sys.getenv_opt "ROCQCHK_OPAQUE_AT" with
  | None | Some "" -> ()
  | Some v ->
    match String.split_on_char ':' v with
    | [p; lib; dir]
      when String.equal p point && String.equal lib (DirPath.to_string dp) ->
      let mark = Filename.concat dir (Printf.sprintf "%s-%d" point (Unix.getpid ())) in
      (try close_out (open_out mark) with Sys_error _ -> ());
      let go = Filename.concat dir "go" in
      let deadline = Unix.gettimeofday () +. 60. in
      while not (Sys.file_exists go) && Unix.gettimeofday () < deadline do
        (try Unix.sleepf 0.01 with Unix.Unix_error _ -> ())
      done
    | _ -> ()

(* Reads one library's table, in two passes over one channel. The first
   reads the range the main process hashed, sequentially, in a fixed
   buffer, and compares its MD5 with the one the main process recorded:
   a file that changed between the two processes' reads is refused. The
   second is stock's own read of the table, [marshal_in_at] at the
   segment's position, so every verdict of the parse, its message and its
   exit code are stock's, and no string of the table's size is ever held.
   The comparison does not see a file that changes between the two passes
   of this process; nothing of stock's sees a change at all.

   The parse is stock's channel reader on purpose. Do not replace it with
   a parse of bytes already read into a string: [Marshal.from_string]
   accepts bytes that [Marshal.from_channel] refuses. On a dependency's
   table with eight damaged bytes, stock refused the file in 40 runs of
   40 and a reader built on [Marshal.data_size] and [Marshal.from_string]
   accepted it in 40 of 40 (compatibility review D1, test (u) of
   test-suite/misc/rocqchk_lazyopaque.sh). A string of the table's size
   also costs that much memory, which stock never needs (D5, test (v)). *)
let read_opaque_table dp src =
  let f = src.src_file in
  let () = opaque_test_at "before" dp in
  let ch = try open_in_bin f with Sys_error _ -> error_changed f in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
      let () = LargeFile.seek_in ch src.src_pos in
      let md5 = try Digest.channel ch src.src_snap with End_of_file -> error_changed f in
      let () = if not (String.equal md5 src.src_md5) then error_changed f in
      let t : seg_proofs =
        marshal_in_at ~validate:src.src_validate ~value:Values.v_opaquetable
          ~pos:src.src_pos ~hash:src.src_hash f ch
      in
      let () = CheckWorkers.note_table_read ~bytes:src.src_snap in
      t)

(* The table of [dp], read on first use and kept for this process. *)
let opaque_table dp =
  match LibraryMap.find_opt dp !opaque_cache with
  | Some t -> t
  | None ->
    let src = match LibraryMap.find_opt dp !opaque_sources with
      | Some src -> src
      | None -> assert false
    in
    let t = read_opaque_table dp src in
    opaque_cache := LibraryMap.add dp t !opaque_cache;
    t

let access_opaque_table dp i =
  let t = opaque_table dp in
  let i = Opaqueproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  t.(i)

let indirect_accessor o =
  let (sub, ci, dp, i) = Opaqueproof.repr o in
  let c = access_opaque_table dp i in
  let c = match c with
  | None ->  CErrors.user_err Pp.(str "Cannot access opaque delayed proof.")
  | Some (c, _unchecked) -> c
  in
  let (c, prv) = Discharge.cook_opaque_proofterm ci c in
  let c = Mod_subst.subst_mps_list sub c in
  (c, prv)

let () = Mod_checking.set_indirect_accessor indirect_accessor

(* The tables of opaque proofs the main process hashed and did not parse,
   newest first, each recorded at the point of the walk where stock parses
   it: in [intern_from_file], after the library's other segments and
   before the checks of its OCaml version and its name. *)
let hashed_tables : (DirPath.t * opaque_source) list ref = ref []

(* Stock parses every table when it interns the library, so where several
   things are wrong, a table that does not parse is what it reports, if
   stock reached that table first: in the order of [hashed_tables], a
   failure in the walk comes after every table, and one of [intern_from_file]
   after the tables that its library and those before it recorded. So when
   coqchk fails with workers, the main process first parses, in that
   order, each recorded table that no process has already read without
   error, and the first that fails is the error, with stock's words.
   Without workers every table is parsed where stock parses it, and
   nothing is recorded. *)
let raise_first_table_error () =
  List.iter (fun (dp, src) ->
      if not (LibraryMap.mem dp !opaque_cache || CheckWorkers.table_checked dp)
      then ignore (read_opaque_table dp src))
    (List.rev !hashed_tables)

let check_one_lib admit senv (dir,m) =
  let md = m.library_compiled in
  let dig = m.library_digest in
  (* Stock parses the table of opaque proofs of every library it interns,
     so a malformed table fails coqchk even when no check reads it. With
     workers, the worker of [CheckWorkers.validate_tables] reads every
     hashed table before the walk, and this only opens the library's group;
     otherwise one deferred task reads the table the same way, queued just
     before the library's own checks, or alone when it has none. *)
  let () = CheckWorkers.defer_table dir (fun () -> ignore (opaque_table dir)) in
  (* Look up if the library is to be admitted correct. We could
     also check if it carries a validation certificate (yet to
     be implemented). *)
  let senv =
    if LibrarySet.mem dir admit then
      (Flags.if_verbose Feedback.msg_notice
         (str "Admitting library: " ++ pr_dirpath dir);
       Safe_checking.unsafe_import (fst senv) md dig),
      (snd senv)
    else
      (Flags.if_verbose Feedback.msg_notice
         (str "Checking library: " ++ pr_dirpath dir);
       Safe_checking.import (fst senv) (snd senv) md dig)
  in
    register_loaded_library m; senv

(*************************************************************************)
(*s Load path. Mapping from physical to logical paths etc.*)

type logical_path = DirPath.t

let load_paths = ref ([],[] : CUnix.physical_path list * logical_path list)


let find_logical_path phys_dir =
  let phys_dir = CUnix.canonical_path_name phys_dir in
  let physical, logical = !load_paths in
  match List.filter2 (fun p d -> p = phys_dir) physical logical with
  | _,[dir] -> dir
  | _,[] -> default_root_prefix
  | _,l -> CErrors.anomaly (Pp.str ("Two logical paths are associated to "^phys_dir^"."))

let remove_load_path dir =
  let physical, logical = !load_paths in
  load_paths := List.filter2 (fun p d -> p <> dir) physical logical

let add_load_path (phys_path,rocq_path) =
  if CDebug.(get_flag misc) then
    Feedback.msg_notice (str "path: " ++ pr_dirpath rocq_path ++ str " ->" ++ spc() ++
           str phys_path);
  let phys_path = CUnix.canonical_path_name phys_path in
  let physical, logical = !load_paths in
    match List.filter2 (fun p d -> p = phys_path) physical logical with
      | _,[dir] ->
          if rocq_path <> dir
            (* If this is not the default -I . to coqtop *)
            && not
            (phys_path = CUnix.canonical_path_name Filename.current_dir_name
                && rocq_path = default_root_prefix)
          then
            begin
              (* Assume the user is concerned by library naming *)
              if dir <> default_root_prefix then
                Feedback.msg_warning
                  (str phys_path ++ strbrk " was previously bound to " ++
                   pr_dirpath dir ++ strbrk "; it is remapped to " ++
                   pr_dirpath rocq_path);
              remove_load_path phys_path;
              load_paths := (phys_path::fst !load_paths, rocq_path::snd !load_paths)
            end
      | _,[] ->
          load_paths := (phys_path :: fst !load_paths, rocq_path :: snd !load_paths)
      | _ -> CErrors.anomaly (Pp.str ("Two logical paths are associated to "^phys_path^"."))

let load_paths_of_dir_path dir =
  let physical, logical = !load_paths in
  fst (List.filter2 (fun p d -> d = dir) physical logical)

(************************************************************************)
(*s Locate absolute or partially qualified library names in the path *)

exception LibUnmappedDir
exception LibNotFound

let locate_absolute_library dir =
  (* Search in loadpath *)
  let pref, base = split_dirpath dir in
  let loadpath = load_paths_of_dir_path pref in
  if loadpath = [] then raise LibUnmappedDir;
  try
    let name = Id.to_string base^".vo" in
    let _, file = System.where_in_path ~warn:false loadpath name in
    (dir, file)
  with Not_found ->
  (* Last chance, removed from the file system but still in memory *)
  try
    (dir, library_full_filename dir)
  with Not_found ->
    raise LibNotFound

let locate_qualified_library qid =
  try
    (* we assume qid is an absolute dirpath *)
    let loadpath = load_paths_of_dir_path (dir_of_path qid) in
    if loadpath = [] then raise LibUnmappedDir;
    let name =  qid.basename^".vo" in
    let path, file = System.where_in_path loadpath name in
    let dir =
      extend_dirpath (find_logical_path path) (Id.of_string qid.basename) in
    (* Look if loaded *)
    try
      (dir, library_full_filename dir)
    with Not_found ->
      (dir, file)
  with Not_found -> raise LibNotFound

let error_unmapped_dir qid =
  let prefix = qid.dirpath in
  CErrors.user_err
    (str "Cannot load " ++ pr_path qid ++ str ":" ++ spc () ++
     str "no physical path bound to" ++ spc () ++ pr_dirlist prefix
     ++ str "." ++ fnl ())

let error_lib_not_found qid =
  CErrors.user_err
    (str "Cannot find library " ++ pr_path qid ++ str " in loadpath.")

let try_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with
    | LibUnmappedDir -> error_unmapped_dir (path_of_dirpath dir)
    | LibNotFound -> error_lib_not_found (path_of_dirpath dir)

let try_locate_qualified_library lib = match lib with
| PhysicalFile f ->
  let () =
    if not (Sys.file_exists f) then
      CErrors.user_err Pp.(str f ++ str ": file not found.")
  in
  let dir = Filename.dirname f in
  let base = Filename.chop_extension (Filename.basename f) in
  let dir = extend_dirpath (find_logical_path dir) (Id.of_string base) in
  (dir, f)
| LogicalFile qid ->
  try
    locate_qualified_library qid
  with
    | LibUnmappedDir -> error_unmapped_dir qid
    | LibNotFound -> error_lib_not_found qid

let lib_to_string = function
  | PhysicalFile f -> f
  | LogicalFile qid -> String.concat "." (List.rev (qid.basename :: qid.dirpath))

let try_locate_qualified_library lib : _ * _ =
  NewProfile.profile "try_locate_qualified_library"
    ~args:(fun () -> [("name", `String (lib_to_string lib))])
    (fun () -> try_locate_qualified_library lib)
    ()

(************************************************************************)
(*s Low-level interning of libraries from files *)

let raw_intern_library f =
  ObjFile.open_in ~file:f

(************************************************************************)
(* Internalise libraries *)

type library_info

type summary_disk = {
  md_name : compilation_unit_name;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  md_ocaml : string;
  md_info : library_info;
  md_safe_deps : DirPath.Set.t;
}

type library_objects

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_syntax_objects : library_objects;
  md_objects : library_objects;
}

let mk_library sd md f digest = {
  library_name = sd.md_name;
  library_filename = f;
  library_compiled = md.md_compiled;
  library_deps = sd.md_deps;
  library_digest = digest;
}

let name_clash_message dir mdir f =
  str ("The file " ^ f ^ " contains library") ++ spc () ++
  pr_dirpath mdir ++ spc () ++ str "and not library" ++ spc() ++
  pr_dirpath dir

type intern_mode = Rec | Root | Dep (* Rec = standard, Root = -norec, Dep = dependency of norec *)

(* Dependency graph *)
let depgraph = ref LibraryMap.empty

let marshal_in_segment (type a) ~validate ~value ~(segment : a ObjFile.segment) f ch : a =
  marshal_in_at ~validate ~value
    ~pos:segment.ObjFile.pos ~hash:segment.ObjFile.hash f ch

(* What the main process does with the table of opaque proofs of a
   library it interns.

   [Hashed]: the MD5 of the bytes of the segment and of the digest stored
   after it, read once, sequentially, in a fixed buffer, and not parsed.
   Hashing the 846 MB of opaque proofs of the whole r160 tree takes
   seconds and allocates nothing. The range is [pos, min (pos + max len 0
   + 16, size of the file, pos + max_int)): it never runs past the file,
   so it raises nothing, and its length fits in an [int] on every build,
   whatever [len] the table of segments declares (see [opaque_source]).

   [Parsed]: nothing is hashed when no other process will read the table
   ([-j 1], and [-j N] where workers are unavailable), nor when the
   segment does not start in the file, where a read of it must do what
   stock's seek and parse do, on this channel, which is where stock's is.
   In both cases this process is the only reader, and it reads the table
   here, with stock's own [marshal_in_segment]: the run then rejects what
   stock rejects, where stock rejects it, down to the message. *)
let intern_opaques ~validate ~(segment : seg_proofs ObjFile.segment) f ch =
  NewProfile.profile "intern_opaques" (fun () ->
  let pos = segment.ObjFile.pos and len = segment.ObjFile.len in
  let size = LargeFile.in_channel_length ch in
  if not (CheckWorkers.parallel ())
     || Int64.compare pos 0L < 0 || Int64.compare pos size > 0 then begin
    let t = marshal_in_segment ~validate ~value:Values.v_opaquetable ~segment f ch in
    let () = CheckWorkers.note_table_read ~bytes:(bytes_from ch pos) in
    Parsed t
  end else begin
    let () = LargeFile.seek_in ch pos in
    let want =
      if Int64.compare len 0L < 0 then 16L
      else if Int64.compare len (Int64.sub Int64.max_int 16L) > 0 then Int64.max_int
      else Int64.add len 16L
    in
    let left = Int64.sub size pos in
    let n = Int64.to_int (min want (min left (Int64.of_int max_int))) in
    (* Shorter only if the file shrank since its length was read. *)
    let md5 = try Digest.channel ch n with End_of_file -> error_changed f in
    Hashed { src_file = f; src_pos = pos; src_snap = n;
             src_hash = segment.ObjFile.hash; src_md5 = md5;
             src_validate = validate }
  end)
    ()

let summary_seg : summary_disk ObjFile.id = ObjFile.make_id "summary"
let library_seg : library_disk ObjFile.id = ObjFile.make_id "library"
let opaques_seg : seg_proofs ObjFile.id = ObjFile.make_id "opaques"

(* [validated] is the set of libraries which must be validated when read even
   if they are interned as a dependency, namely those named on the command
   line and not admitted. *)
(* The [vmlibrary] segment is deliberately not read: the checker compiles the VM
   bytecode itself from the declarations it checks (see [Safe_checking]), so the
   serialized bytecode is neither trusted nor needed. *)
let intern_from_file ~intern_mode ~validated (dir, f) =
  let validate = intern_mode <> Dep || LibrarySet.mem dir validated in
  Flags.if_verbose chk_pp (str"[intern "++str f++str" ...");
  let (sd,md,src,digest) =
    try
      (* First pass to read the metadata of the file *)
      let ch = System.with_magic_number_check raw_intern_library f in
      let seg_sd = ObjFile.get_segment ch ~segment:summary_seg in
      let seg_md = ObjFile.get_segment ch ~segment:library_seg in
      let seg_opaque = ObjFile.get_segment ch ~segment:opaques_seg in
      let () = ObjFile.close_in ch in
      (* Actually read the data *)
      let ch = open_in_bin f in

      let sd = marshal_in_segment ~validate ~value:Values.v_libsum ~segment:seg_sd f ch in
      let md = marshal_in_segment ~validate ~value:Values.v_lib ~segment:seg_md f ch in
      (* The opaque proofs are not parsed here when another process will
         read them: their bytes are hashed, and the table is read, by
         whichever process first needs it, from that same range. Nothing
         the main process checks looks into an opaque body
         ([Mod_checking], [Check_stat]); the worker of
         [CheckWorkers.validate_tables] keeps the rejections of a table
         nothing reads.
         Without workers there is nothing to gain by waiting, and [-j 1]
         is stock to the byte: see [intern_opaques]. *)
      let src = intern_opaques ~validate ~segment:seg_opaque f ch in
      let () = match src with
        | Hashed s -> hashed_tables := (dir, s) :: !hashed_tables
        | Parsed _ -> ()
      in
      (* Verification of the final checksum *)
      let () = close_in ch in
      let () = System.check_caml_version ~caml:sd.md_ocaml ~file:f in
      if dir <> sd.md_name then
        CErrors.user_err
          (name_clash_message dir sd.md_name f);
      Flags.if_verbose chk_pp (str" done]" ++ fnl ());
      let digest =
        Safe_typing.Dvo_or_vi seg_md.hash in
      sd,md,src,digest
    with e -> Flags.if_verbose chk_pp (str" failed!]" ++ fnl ()); raise e in
  depgraph := LibraryMap.add sd.md_name sd.md_deps !depgraph;
  let () = match src with
    | Hashed src -> opaque_sources := LibraryMap.add sd.md_name src !opaque_sources
    | Parsed t -> opaque_cache := LibraryMap.add sd.md_name t !opaque_cache
  in
  mk_library sd md f digest

let intern_from_file ~intern_mode ~validated dirf : library_t =
  NewProfile.profile "intern_from_file"
    ~args:(fun () -> [("name", `String (DirPath.to_string (fst dirf)))])
    (fun () -> intern_from_file ~intern_mode ~validated dirf)
    ()

(* Read a compiled library and all dependencies, in reverse order.
   Do not include files that are already in the context. *)
let rec intern_library ~intern_mode ~validated seen (dir, f) needed =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  (* Look if in the current logical environment *)
  try let _ = find_library dir in needed
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  if List.mem_assoc_f DirPath.equal dir needed then needed
  else
    (* [dir] is an absolute name which matches [f] which must be in loadpath *)
    let m = intern_from_file ~intern_mode ~validated (dir,f) in
    let seen' = LibrarySet.add dir seen in
    let deps =
      Array.map (fun (d,_) -> try_locate_absolute_library d) m.library_deps
    in
    let intern_mode = match intern_mode with Rec -> Rec | Root | Dep -> Dep in
    (dir,m) :: Array.fold_right (intern_library ~intern_mode ~validated seen') deps needed

(* Compute the reflexive transitive dependency closure *)
let rec fold_deps seen ff (dir,f) (s,acc) =
  if LibrarySet.mem dir seen then failwith "Recursive dependencies!";
  if LibrarySet.mem dir s then (s,acc)
  else
    let deps = match LibraryMap.find_opt dir !depgraph with
      | Some deps -> deps
      | None ->
        CErrors.anomaly Pp.(str "missing dep when computing closure (" ++ DirPath.print dir ++ str ")")
    in
    let deps = Array.map (fun (d,_) -> try_locate_absolute_library d) deps in
    let seen' = LibrarySet.add dir seen in
    let (s',acc') = Array.fold_right (fold_deps seen' ff) deps (s,acc) in
    (LibrarySet.add dir s', ff dir acc')

and fold_deps_list seen ff modl needed =
  List.fold_right (fold_deps seen ff) modl needed

let fold_deps_list ff modl acc =
  snd (fold_deps_list LibrarySet.empty ff modl (LibrarySet.empty,acc))

let recheck_library_in_order senv ~norec ~admit ~check =
  let ml = List.map try_locate_qualified_library check in
  let nrl = List.map try_locate_qualified_library norec in
  let al =  List.map try_locate_qualified_library admit in
  (* A library named on the command line may also be a dependency of another
     one, in which case it may happen to be interned in [Dep] mode, which does
     not validate the marshalled data. Force its validation, unless it was
     admitted. *)
  let validated =
    let fold f l s = List.fold_right (fun (dir, _) s -> f dir s) l s in
    fold LibrarySet.remove al
      (fold LibrarySet.add nrl (fold LibrarySet.add ml LibrarySet.empty))
  in
  let needed = List.fold_right (intern_library ~intern_mode:Rec ~validated LibrarySet.empty) ml [] in
  let needed = List.fold_right (intern_library ~intern_mode:Root ~validated LibrarySet.empty) nrl needed in
  let needed = List.rev needed in
  (* first compute the closure of norec, remove closure of check,
     add closure of admit, and finally remove norec and check *)
  let nochk = fold_deps_list LibrarySet.add nrl LibrarySet.empty in
  let nochk = fold_deps_list LibrarySet.remove ml nochk in
  let nochk = fold_deps_list LibrarySet.add al nochk in
  (* explicitly required modules cannot be skipped... *)
  let nochk =
    List.fold_right LibrarySet.remove (List.map fst (nrl@ml)) nochk in
  (* *)
  Flags.if_verbose Feedback.msg_notice (fnl()++hv 2 (str "Ordered list:" ++ fnl() ++
    prlist
    (fun (dir,_) -> pr_dirpath dir ++ fnl()) needed));
  (* Every library is interned by now, so every table stock would have
     parsed is recorded: read them all early, in stock's order, so that a
     malformed one stops the run near where it stops stock. The reader
     keeps no table, so the worker holds at most one table beyond the heap
     it was forked with. *)
  let () = CheckWorkers.validate_tables
      (List.rev_map (fun (dp, src) -> dp, (fun () -> ignore (read_opaque_table dp src)))
         !hashed_tables) in
  let senv = List.fold_left (check_one_lib nochk) (senv, Cmap.empty) needed in
  CheckWorkers.finish ();
  Flags.if_verbose Feedback.msg_notice (str"Modules were successfully checked");
  senv

let recheck_library senv ~norec ~admit ~check =
  try recheck_library_in_order senv ~norec ~admit ~check
  with e ->
    let e = Exninfo.capture e in
    CheckWorkers.abort ();
    CheckWorkers.validator_progress ();
    let () = match fst e with
      | Sys.Break -> ()
      | _ ->
        try raise_first_table_error ()
        with e' ->
          let e' = Exninfo.capture e' in
          CheckWorkers.drop_held_output ();
          Exninfo.iraise e'
    in
    CheckWorkers.print_held_output ();
    Exninfo.iraise e
