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

let get_ml_filename () =
  let temp_dir = Lazy.force my_temp_dir in
  let filename = Filename.temp_file ~temp_dir "Coq_native" source_ext in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

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

let compile fn code ~profile:profile upds =
  let text = render_ml_code code in
  let stem = Filename.chop_extension fn in
  let link_filename = Dynlink.adapt_filename (stem ^ ".cmo") in
  let via_cache () =
    Checkstats.time Checkstats.native_cache_hit (fun () ->
        if Nativecache.fetch_to ~include_dirs:!include_dirs text ~dest_stem:stem then
          Some link_filename
        else None)
  in
  let r =
    match via_cache () with
    | Some r -> r
    | None ->
      Nativecache.with_lock ~include_dirs:!include_dirs text (fun () ->
          match via_cache () with
          | Some r -> r (* another worker published while we waited for the lock *)
          | None ->
            write_text_file fn text;
            let r = Checkstats.time Checkstats.native_ocamlopt (fun () -> call_compiler ~profile fn) in
            Nativecache.publish ~include_dirs:!include_dirs text ~compiled_stem:stem;
            r)
  in
  (* The recorded "linked at" prefix for every constant/inductive this bundle
     just defined must be a function of this bundle's own content, not of
     [fn]'s random temp name: otherwise a LATER bundle that references one of
     these constants embeds a different, process-specific qualifier every
     run, and can never match a cached entry even when its own content is
     otherwise identical. See Nativecode.stabilize_prefix. *)
  let upds = Nativecode.stabilize_prefix (Sha256.hex_digest text ^ ".") upds in
  (* NB: to prevent reusing the same filename we MUST NOT remove the file until exit
     cf #15263 *)
  delay_cleanup_file fn;
  r, upds

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

let execute_library ~prefix f symbols upds =
  let () = rt1 := None in
  let () = rt2 := None in
  let () = rsymbols := symbols in
  if not (Sys.file_exists f) then
    CErrors.user_err Pp.(str "Cannot find native compiler file " ++ str f);
  if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
  register_native_file prefix;
  update_locations upds;
  (!rt1, !rt2)

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
