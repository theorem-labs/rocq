(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Util
open Nativecode
open CErrors

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

let get_load_paths =
  ref (fun _ -> anomaly (Pp.str "get_load_paths not initialized.") : unit -> string list)

let open_header = ["Nativevalues";
                   "Nativecode";
                   "Nativelib";
                   "Nativeconv"]
let open_header = List.map mk_open open_header

(* Directory where compiled files are stored *)
let dft_output_dir = ".coq-native"
let output_dir = ref dft_output_dir

(* Extension of generated ml files, stored for debugging purposes *)
let source_ext = ".native"

let ( / ) = Filename.concat

(* Directory for temporary files for the conversion and normalisation
   (as opposed to compiling the library itself, which uses [output_dir]). *)
let my_temp_dir = lazy (CUnix.mktemp_dir "Coq_native" "")

let () = at_exit (fun () ->
    if not (keep_debug_files ()) && Lazy.is_val my_temp_dir then
      try
        let d = Lazy.force my_temp_dir in
        Array.iter (fun f -> Sys.remove (Filename.concat d f)) (Sys.readdir d);
        Unix.rmdir d
      with (Unix.Unix_error _ | Sys_error _) as e ->
        Feedback.msg_warning
          Pp.(str "Native compile: failed to cleanup: " ++
              str(Printexc.to_string e) ++ fnl()))

let delay_cleanup_file =
  let toclean = ref [] in
  let () = at_exit (fun () -> List.iter (fun f -> if Sys.file_exists f then Sys.remove f) !toclean) in
  fun f -> if not (keep_debug_files()) then toclean := f :: !toclean

(* We have to delay evaluation of include_dirs because coqlib cannot
   be guessed until flags have been properly initialized. It also lets
   us avoid forcing [my_temp_dir] if we don't need it (eg stdlib file
   without native compute or native conv uses). *)
let include_dirs = ref []

let default_include_dirs env = [ Boot.Env.(Path.to_string (native_cmi env "kernel")) ]

let get_include_dirs () =
  let base = match !include_dirs with
    | [] ->
      CErrors.user_err
        Pp.(str "Native compute with -boot: you must also give -nI pointing to the kernel.")
  | _::_ as l -> l
  in
  if Lazy.is_val my_temp_dir
  then (Lazy.force my_temp_dir) :: base
  else base

(* Pointer to the function linking an ML object into Rocq's toplevel *)
let load_obj = ref (fun _x -> () : string -> unit)

let rsymbols = ref Nativevalues.empty_symbols
let rt1 = ref None
let rt2 = ref None

let get_symbols () = !rsymbols

let render_ml_code ?(header=[]) code =
  let header = open_header@header in
  let buf = Buffer.create 4096 in
  let fmt = Format.formatter_of_buffer buf in
  List.iter (pp_global fmt) (header@code);
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let write_ml_code fn ?(header=[]) code =
  let text = render_ml_code ~header code in
  let ch_out = open_out fn in
  output_string ch_out text;
  close_out ch_out

(* Write already-rendered source bytes (as returned by [render_ml_code])
   directly, without re-running the pretty-printer: used by [compile] so the
   bytes it hashes for the cache are exactly the bytes it writes to disk. *)
let write_text_file fn text =
  let ch_out = open_out fn in
  output_string ch_out text;
  close_out ch_out

let error_native_compiler_failed e =
  let msg = match e with
  | Inl (Unix.WEXITED 127) -> Pp.(strbrk "The OCaml compiler was not found. Make sure it is installed, together with findlib.")
  | Inl (Unix.WEXITED n) ->
     Pp.(strbrk "Native compiler exited with status" ++ str" " ++ int n
         ++ strbrk (if n = 2 then " (in case of stack overflow, increasing stack size (typically with \"ulimit -s\") often helps)" else ""))
  | Inl (Unix.WSIGNALED n) -> Pp.(strbrk "Native compiler killed by signal" ++ str" " ++ int n)
  | Inl (Unix.WSTOPPED n) -> Pp.(strbrk "Native compiler stopped by signal" ++ str" " ++ int n)
  | Inr e -> Pp.(strbrk "Native compiler failed with error: " ++ strbrk (Unix.error_message e))
  in
  CErrors.user_err msg

let call_compiler ?profile:(profile=false) ml_filename =
  (* The below path is computed from Require statements, by uniquizing
     the paths, see [Library.get_used_load_paths] This is in general
     hacky and we should do a bit better once we move loadpath to its
     own library *)
  let require_load_path = !get_load_paths () in
  (* We assume that installed files always go in .coq-native for now *)
  (* To ease the build we also consider the current dir, but at some point the build system should manage both *)
  let install_load_path = List.map (fun dn -> dn / dft_output_dir) require_load_path @ require_load_path in
  let include_dirs = List.flatten (List.map (fun x -> ["-I"; x]) (get_include_dirs () @ install_load_path)) in
  let f = Filename.chop_extension ml_filename in
  let link_filename = f ^ ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let remove f = if Sys.file_exists f then Sys.remove f in
  remove link_filename;
  remove (f ^ ".cmi");
  let initial_args =
    if Dynlink.is_native then
      ["opt"; "-shared"]
     else
      ["ocamlc"; "-c"]
  in
  let profile_args =
    if profile then
      ["-g"]
    else
      []
  in
  let flambda_args = if Sys.(backend_type = Native) then ["-Oclassic"] else [] in
  let args =
    initial_args @
      profile_args @
        flambda_args @
      ("-o"::link_filename
       ::"-rectypes"
       ::"-w"::"a"
       ::include_dirs) @
    ["-impl"; ml_filename] in
  let ocamlfind = Boot.Env.ocamlfind () in
  debug_native_compiler (fun () -> Pp.str (ocamlfind ^ " " ^ (String.concat " " args)));
  (* BET #867/BET-29 diagnostic: on a non-zero ocamlopt exit, preserve exactly
     what failed (the generated source, the argv, and ocamlopt's own output)
     under ROCQCHK_NATIVE_FAILDIR, if set. A successful compile captures
     nothing extra: ocamlopt's output is still replayed to this process's own
     stdout/stderr afterward, so visible behavior on success is unchanged. *)
  let capture_failure () =
    match Sys.getenv_opt "ROCQCHK_NATIVE_FAILDIR" with
    | None -> ()
    | Some dir ->
      (try
         let dest = Filename.concat dir (Printf.sprintf "%d-%.0f" (Unix.getpid ()) (Unix.gettimeofday () *. 1000.)) in
         let rec mkdir_p d =
           if d = "" || d = "." || d = "/" || Sys.file_exists d then ()
           else begin
             mkdir_p (Filename.dirname d);
             try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
           end
         in
         mkdir_p dest;
         let copy src name =
           if Sys.file_exists src then begin
             let ic = open_in_bin src and oc = open_out_bin (Filename.concat dest name) in
             (try while true do output_char oc (input_char ic) done with End_of_file -> ());
             close_in ic; close_out oc
           end
         in
         copy ml_filename "source.native";
         copy (ml_filename ^ ".ocamlopt.out") "ocamlopt.stdout";
         copy (ml_filename ^ ".ocamlopt.err") "ocamlopt.stderr";
         let oc = open_out (Filename.concat dest "argv.txt") in
         output_string oc (ocamlfind ^ " " ^ String.concat " " args ^ "\n");
         close_out oc
       with _ -> ())
  in
  try
    let out_path = ml_filename ^ ".ocamlopt.out" and err_path = ml_filename ^ ".ocamlopt.err" in
    let out_fd = Unix.openfile out_path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
    let err_fd = Unix.openfile err_path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
    let pid = Unix.create_process ocamlfind (Array.of_list (ocamlfind :: args)) Unix.stdin out_fd err_fd in
    Unix.close out_fd; Unix.close err_fd;
    let (_, res) = Unix.waitpid [] pid in
    let replay path ch =
      if Sys.file_exists path then begin
        let ic = open_in_bin path in
        (try while true do output_char ch (input_char ic) done with End_of_file -> ());
        close_in ic
      end
    in
    replay out_path stdout; replay err_path stderr;
    (match res with
     | Unix.WEXITED 0 -> ()
     | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> capture_failure ());
    (try Sys.remove out_path with Sys_error _ -> ());
    (try Sys.remove err_path with Sys_error _ -> ());
    match res with
    | Unix.WEXITED 0 -> link_filename
    | Unix.WEXITED _n | Unix.WSIGNALED _n | Unix.WSTOPPED _n ->
      error_native_compiler_failed (Inl res)
  with Unix.Unix_error (e,_,_) ->
    error_native_compiler_failed (Inr e)

(* ---------------------------------------------------------------------- *)
(* Bounded compilation units for native conversion (BET-52).                *)
(*                                                                          *)
(* The code a conversion needs is cut into units of bounded size. Each unit *)
(* is compiled once, in dependency order, into a module whose name is the   *)
(* key of its content (Nativecache.key), published in the shared cache and  *)
(* loaded from there; a unit refers to an earlier one only through that     *)
(* module name, and is generated only after the earlier one is loaded.      *)
(* ---------------------------------------------------------------------- *)

(* A unit is closed right after an item whose name hashes to 0 modulo
   [ROCQCHK_NATIVE_UNIT_MOD] (default 128, about 0.7 MB of source on the
   measured closure), and in any case once it reaches
   [ROCQCHK_NATIVE_UNIT_MAX] bytes, which bounds ocamlopt's time and memory
   on one unit. Whether a unit ends after an item depends on that item and on
   the items since the previous cut only, never on what was linked before or
   on the term that asked: two plans that share a run of items between two
   cuts produce that unit byte for byte, so it is compiled once and every
   other process and cast finds it in the cache. *)
let env_int name default =
  match Sys.getenv_opt name with
  | Some s -> (match int_of_string_opt s with Some n when n > 0 -> n | _ -> default)
  | None -> default

let unit_max_bytes = lazy (env_int "ROCQCHK_NATIVE_UNIT_MAX" (4 * 1024 * 1024))
let unit_mod = lazy (env_int "ROCQCHK_NATIVE_UNIT_MOD" 128)

let fnv1a s =
  let h = ref 0x2bf29ce484222325 in
  String.iter (fun c -> h := (!h lxor Char.code c) * 0x100000001b3) s;
  !h land max_int

(* The arguments of every unit compile that do not depend on the unit. They
   are part of the cache epoch. *)
let unit_flags () =
  let initial_args = if Dynlink.is_native then ["opt"; "-shared"] else ["ocamlc"; "-c"] in
  let flambda_args = if Sys.(backend_type = Native) then ["-Oclassic"] else [] in
  initial_args @ flambda_args @ ["-rectypes"; "-w"; "a"]

let ensure_cache () = Nativecache.init ~include_dirs:!include_dirs ~flags:(unit_flags ())

let init_cache = ensure_cache

(* module name -> (directory of its cache entry, digest of its interface and
   implementation info). Everything a process has loaded as a dependency unit. *)
let loaded_units : (string, string * string) Hashtbl.t = Hashtbl.create 256

let unit_dir name =
  match Hashtbl.find_opt loaded_units name with
  | Some (dir, _) -> dir
  | None -> CErrors.anomaly Pp.(str "native conversion: unit " ++ str name ++ str " is referenced but not loaded.")

let unit_digest name = snd (Hashtbl.find loaded_units name)

(* The modules of earlier units that [text] names. A unit names another one
   only by [Coq_native<40 hex digits>.]; that is what [Nativecache.module_name]
   produces. *)
let referenced_units text =
  let tag = "Coq_native" in
  let n = String.length text and tl = String.length tag in
  let wl = tl + Nativecache.module_name_len in
  let is_hex c = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') in
  let has_tag i =
    let rec go k = k >= tl || (String.unsafe_get text (i + k) = String.unsafe_get tag k && go (k + 1)) in
    go 0
  in
  let found = ref [] in
  let i = ref 0 in
  while !i + wl < n do
    if String.unsafe_get text !i = 'C' && has_tag !i then begin
      let ok = ref (String.unsafe_get text (!i + wl) = '.') in
      let j = ref (!i + tl) in
      while !ok && !j < !i + wl do
        if not (is_hex (String.unsafe_get text !j)) then ok := false;
        incr j
      done;
      if !ok then begin
        found := String.sub text !i wl :: !found;
        i := !i + wl
      end
      else incr i
    end
    else incr i
  done;
  List.sort_uniq String.compare !found

let cpu_children () =
  let t = Unix.times () in
  t.Unix.tms_cutime +. t.Unix.tms_cstime

let read_small path =
  try
    let ic = open_in_bin path in
    Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
        let n = min (in_channel_length ic) 4096 in
        really_input_string ic n)
  with Sys_error _ -> ""

let copy_to_faildir ~scratch ~name ~argv ~log =
  match Sys.getenv_opt "ROCQCHK_NATIVE_FAILDIR" with
  | None -> ()
  | Some dir ->
    (try
       let dest = dir / Printf.sprintf "%s-%d" name (Unix.getpid ()) in
       Nativecache.mkdir_p dest;
       Nativecache.copy_file ~src:(scratch / (name ^ ".ml")) ~dst:(dest / "source.ml");
       let oc = open_out (dest / "argv.txt") in
       output_string oc (String.concat " " argv ^ "\n");
       output_string oc log;
       close_out oc
     with _ -> ())

let stats_line_unit fmt = Printf.ksprintf (fun s -> if Checkstats.stats_enabled then Printf.eprintf "%s\n%!" s) fmt

(* Compile the unit in a private directory and publish it; every failure is
   recorded for this run and reported with the unit's name. *)
let compile_unit ~key ~name ~text ~dep_dirs ~extra_flags ~desc =
  let scratch = Nativecache.scratch key in
  write_text_file (scratch / (name ^ ".ml")) text;
  let base = unit_flags () in
  let incl = List.concat_map (fun d -> ["-I"; d]) (!include_dirs @ !get_load_paths () @ dep_dirs) in
  let obj = name ^ Nativecache.object_ext in
  let args = base @ extra_flags @ ["-o"; obj] @ incl @ ["-impl"; name ^ ".ml"] in
  let ocamlfind = Boot.Env.ocamlfind () in
  let timed = Checkstats.stats_enabled && Sys.file_exists "/usr/bin/time" in
  let argv =
    (if timed then ["/usr/bin/time"; "-f"; "%M"; "-o"; scratch / "time.txt"] else [])
    @ ocamlfind :: args
  in
  let out_path = scratch / "ocamlopt.out" and err_path = scratch / "ocamlopt.err" in
  let fail why =
    let log = read_small out_path ^ read_small err_path in
    let msg =
      Printf.sprintf "native conversion unit %s (%s) failed to compile: %s%s" name desc why
        (if log = "" then "" else "\n" ^ log)
    in
    Nativecache.record_failure key msg;
    copy_to_faildir ~scratch ~name ~argv ~log;
    Nativecache.discard_scratch scratch;
    CErrors.user_err (Pp.str msg)
  in
  let cpu0 = cpu_children () in
  let res =
    try
      let out_fd = Unix.openfile out_path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
      let err_fd = Unix.openfile err_path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
      (* The compiler runs in [scratch] and is given relative file names, so
         the artifacts do not depend on where they were built. *)
      let old = Unix.getcwd () in
      Unix.chdir scratch;
      let pid =
        Fun.protect ~finally:(fun () -> Unix.chdir old) (fun () ->
            Unix.create_process (List.hd argv) (Array.of_list argv) Unix.stdin out_fd err_fd)
      in
      Unix.close out_fd; Unix.close err_fd;
      snd (Unix.waitpid [] pid)
    with Unix.Unix_error (e, f, _) -> fail (Printf.sprintf "%s: %s" f (Unix.error_message e))
  in
  (match res with
   | Unix.WEXITED 0 -> ()
   | Unix.WEXITED n -> fail (Printf.sprintf "exit status %d" n)
   | Unix.WSIGNALED n -> fail (Printf.sprintf "killed by signal %d (OCaml numbering)" n)
   | Unix.WSTOPPED n -> fail (Printf.sprintf "stopped by signal %d" n));
  let rss = if timed then String.trim (read_small (scratch / "time.txt")) else "" in
  let dir = Nativecache.publish key ~scratch in
  stats_line_unit "NATIVEUNIT pid=%d name=%s %s result=compiled ocamlopt_cpu_s=%.3f maxrss_kb=%s" (Unix.getpid ()) name
    desc (cpu_children () -. cpu0) rss;
  dir

(* The directory of the compiled unit with this content: from the cache if it
   is there, else compiled by exactly one process (the one holding the key's
   lock) while any other needing it waits. *)
let obtain_unit ~key ~name ~text ~dep_dirs ~extra_flags ~desc =
  let hit dir =
    stats_line_unit "NATIVEUNIT pid=%d name=%s %s result=hit" (Unix.getpid ()) name desc;
    dir
  in
  match Checkstats.time Checkstats.native_cache_hit (fun () -> Nativecache.lookup key) with
  | Some dir -> hit dir
  | None ->
    Nativecache.with_lock key (fun () ->
        match Nativecache.lookup key with
        | Some dir -> hit dir
        | None ->
          (match Nativecache.failure_of key with
           | Some msg -> CErrors.user_err (Pp.str msg)
           | None -> ());
          Nativecache.note_miss ();
          Checkstats.time Checkstats.native_ocamlopt (fun () ->
              compile_unit ~key ~name ~text ~dep_dirs ~extra_flags ~desc))

let load_object ~private_ name dir symbols =
  rsymbols := symbols;
  rt1 := None;
  rt2 := None;
  let f = dir / (name ^ Nativecache.object_ext) in
  Checkstats.time Checkstats.native_load_run (fun () ->
      try
        if Dynlink.is_native then
          (if private_ then Dynlink.loadfile_private f else Dynlink.loadfile f)
        else !load_obj f
      with Dynlink.Error e ->
        CErrors.user_err
          Pp.(str "native conversion unit " ++ str name ++ str " cannot be loaded: "
              ++ str (Dynlink.error_message e)))

(* Dependencies are listed with their digests, in name order: a unit compiled
   against another one's interface is only valid with that very interface. *)
let deps_string refs extra =
  String.concat ";" (List.map (fun n -> n ^ "=" ^ unit_digest n) refs) ^ "|" ^ extra

let render_unit_text ?(header = []) code =
  let buf = Buffer.create 65536 in
  let fmt = Format.formatter_of_buffer buf in
  List.iter (pp_global fmt) (open_header @ header @ code);
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* Link the dependency units: generate, compile, load and link them in order
   until nothing [ts] reaches is unlinked. *)
let link_dependencies env sigma ts =
  ensure_cache ();
  let plan = Checkstats.time Checkstats.native_codegen (fun () -> plan_deps env sigma ts) in
  (* Two items printing the same OCaml name would shadow each other inside a
     unit, silently binding later uses to the wrong definition. *)
  let names = Hashtbl.create 1024 in
  List.iter (fun (_, item) ->
      let n = item_def_name item in
      match Hashtbl.find_opt names n with
      | Some other when other <> item_key item ->
        CErrors.anomaly
          Pp.(str "native conversion: " ++ str other ++ str " and " ++ str (item_key item)
              ++ str " both print as " ++ str n ++ str ".")
      | _ -> Hashtbl.replace names n (item_key item))
    plan;
  let max_bytes = Lazy.force unit_max_bytes and modulus = Lazy.force unit_mod in
  let rec next_unit remaining =
    match remaining with
    | [] -> ()
    | _ ->
      let u = new_unit () in
      let buf = Buffer.create 65536 in
      let fmt = Format.formatter_of_buffer buf in
      List.iter (pp_global fmt) (open_header @ [ unit_header ]);
      let rec fill items remaining =
        match remaining with
        | [] -> (List.rev items, [])
        | (_, item) :: rest ->
          List.iter (pp_global fmt) (unit_add_item u env sigma item);
          Format.pp_print_flush fmt ();
          let size = Buffer.length buf in
          let items = item :: items in
          if size >= max_bytes || fnv1a (item_key item) mod modulus = 0
          then (List.rev items, rest)
          else fill items rest
      in
      let items, rest, text, symbols =
        Checkstats.time Checkstats.native_codegen (fun () ->
            let items, rest = fill [] remaining in
            (items, rest, Buffer.contents buf, unit_symbols u))
      in
      let refs = referenced_units text in
      let key = Nativecache.key ~text ~deps:(deps_string refs "") in
      let name = Nativecache.module_name key in
      (* The same content may already be loaded in this process, when the same
         library is checked twice (a signature and then its implementation)
         and so its constants are unlinked again: only the links are redone. *)
      if not (Hashtbl.mem loaded_units name) then begin
        let desc =
          Printf.sprintf "kind=dep bytes=%d items=%d first=%s last=%s" (String.length text) (List.length items)
            (item_key (List.hd items)) (item_key (List.nth items (List.length items - 1)))
        in
        let dep_dirs = List.map unit_dir refs in
        let dir = obtain_unit ~key ~name ~text ~dep_dirs ~extra_flags:[] ~desc in
        load_object ~private_:false name dir symbols;
        Hashtbl.replace loaded_units name (dir, Nativecache.artifact_digest ~dir ~name)
      end;
      let prefix = name ^ "." in
      register_native_file prefix;
      link_items items prefix;
      next_unit rest
  in
  next_unit (List.map (fun (l, it) -> (l, it)) plan)

(* Compile and run the unit holding the conversion's own code; its
   dependencies are linked ([link_dependencies]). It is loaded privately:
   nothing refers to it, and the same cast may come again. *)
let run_cast ~profile code symbols =
  ensure_cache ();
  let text = render_unit_text code in
  let refs = referenced_units text in
  let extra_flags = if profile then ["-g"] else [] in
  let key = Nativecache.key ~text ~deps:(deps_string refs (String.concat " " extra_flags)) in
  let name = Nativecache.module_name key in
  let desc = Printf.sprintf "kind=cast bytes=%d items=0" (String.length text) in
  let dir = obtain_unit ~key ~name ~text ~dep_dirs:(List.map unit_dir refs) ~extra_flags ~desc in
  load_object ~private_:true name dir symbols;
  (!rt1, !rt2)

type native_library = Nativecode.global list * Nativevalues.symbols

let compile_library (code, symb) fn =
  let header = mk_library_header symb in
  let fn = fn ^ source_ext in
  let basename = Filename.basename fn in
  let dirname =
    if Filename.is_relative !output_dir then Filename.dirname fn / !output_dir else !output_dir in
  let () =
    try Unix.mkdir dirname 0o755
    with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  in
  let fn = dirname / basename in
  write_ml_code fn ~header code;
  let _ = call_compiler fn in
  delay_cleanup_file fn


let link_library dirname prefix =
  let basename = Dynlink.adapt_filename (prefix ^ "cmo") in
  (* We try both [output_dir] and [.coq-native], unfortunately from
     [Require] we don't know if we are loading a library in the build
     dir or in the installed layout *)
  let install_location = dirname / dft_output_dir / basename in
  let build_location = dirname / !output_dir / basename in
  let f = if Sys.file_exists build_location then build_location else install_location in
  try
    if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
    register_native_file prefix
  with
  | Dynlink.Error _ as exn ->
      debug_native_compiler (fun () -> CErrors.iprint (Exninfo.capture exn))

let delayed_link = ref []

let link_libraries () =
  let delayed = List.rev !delayed_link in
  delayed_link := [];
  List.iter (fun (dirname, libname) ->
      let prefix = mod_uid_of_dirpath libname ^ "." in
      if not (Nativecode.is_loaded_native_file prefix) then
        link_library dirname prefix
    ) delayed

let enable_library dirname libname =
  delayed_link := (dirname, libname) :: !delayed_link
