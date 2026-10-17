(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let ( / ) = Filename.concat

let cache_root () = Sys.getenv_opt "ROCQCHK_NATIVE_CACHE"

let enabled () = match cache_root () with Some d -> d <> "" | None -> false

(* --- small filesystem helpers ------------------------------------------ *)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let len = in_channel_length ic in
      really_input_string ic len)

let rec mkdir_p dir =
  if dir = "" || dir = "." || dir = "/" || Sys.file_exists dir then ()
  else begin
    mkdir_p (Filename.dirname dir);
    try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* Copy [src] to [dst] byte-for-byte (used when a hardlink is not possible,
   e.g. the cache and the destination are on different filesystems). *)
let copy_file ~src ~dst =
  let ic = open_in_bin src in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let oc = open_out_bin dst in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () ->
          let buf = Bytes.create 65536 in
          let rec loop () =
            let n = input ic buf 0 (Bytes.length buf) in
            if n > 0 then begin
              output oc buf 0 n;
              loop ()
            end
          in
          loop ()))

(* Hash every regular file reachable under [dir], combined with its path
   relative to [dir], so the epoch changes if any byte of the kernel's
   native [.cmi]/[.cmx] tree this build compiles against changes. Directory
   walk order is sorted for determinism. *)
let hash_tree dir =
  let entries = ref [] in
  let rec walk rel abs =
    if Sys.is_directory abs then
      Array.iter
        (fun name -> walk (if rel = "" then name else rel / name) (abs / name))
        (let a = Sys.readdir abs in
         Array.sort String.compare a;
         a)
    else entries := (rel, Sha256.hex_digest (read_file abs)) :: !entries
  in
  (if Sys.file_exists dir then walk "" dir);
  let entries = List.sort (fun (a, _) (b, _) -> String.compare a b) !entries in
  String.concat "\n" (List.map (fun (rel, h) -> rel ^ " " ^ h) entries)

let read_process_stdout argv =
  let ic = Unix.open_process_args_in (List.hd argv) (Array.of_list argv) in
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  ignore (Unix.close_process_in ic);
  Buffer.contents buf

let try_read_process_stdout argv = try read_process_stdout argv with _ -> "<unavailable>"

(* --- epoch: everything that can change what a given source compiles to - *)

let epoch_cache : string option ref = ref None

(* Resolve the on-disk path of the running coqchk binary itself, so a
   different Rocq/kernel build (different [nativecode.ml], different
   OCaml runtime it was linked against) always gets a fresh epoch. Falls
   back gracefully: an epoch component we fail to read becomes a fixed
   marker string instead of raising, so a misconfigured environment fails
   CLOSED (an unreachable, ever-missing epoch -> every lookup misses ->
   plain recompilation, i.e. exactly today's behavior) rather than crashing
   the checker or, worse, silently reusing an unrelated epoch. *)
let self_binary_digest () =
  try
    let path =
      if Sys.file_exists "/proc/self/exe" then Unix.readlink "/proc/self/exe" else Sys.executable_name
    in
    Sha256.hex_digest (read_file path)
  with _ -> "<self-unavailable>"

let ocamlfind_digest () =
  try Sha256.hex_digest (read_file (Boot.Env.ocamlfind ())) with _ -> "<ocamlfind-unavailable>"

let compute_epoch ~include_dirs =
  let parts =
    [
      "self=" ^ self_binary_digest ();
      "ocamlfind_bin=" ^ ocamlfind_digest ();
      "ocamlopt_version=" ^ try_read_process_stdout [ Boot.Env.ocamlfind (); "ocamlopt"; "-version" ];
      "ocaml_version=" ^ Sys.ocaml_version;
      "backend=" ^ (match Sys.backend_type with Sys.Native -> "native" | Sys.Bytecode -> "bytecode" | Sys.Other s -> s);
      "flags=-rectypes -w a -Oclassic -shared";
    ]
    @ List.map (fun d -> "include_dir[" ^ d ^ "]=" ^ hash_tree d) (List.sort String.compare include_dirs)
  in
  Sha256.hex_digest (String.concat "\n" parts)

let epoch_tag ~include_dirs =
  match !epoch_cache with
  | Some e -> e
  | None ->
    let e = compute_epoch ~include_dirs in
    epoch_cache := Some e;
    e

(* --- content-addressed layout ------------------------------------------ *)

let key ~include_dirs source = Sha256.hex_digest (epoch_tag ~include_dirs ^ "\x00" ^ source)

(* A cache entry is a DIRECTORY, not a single file: compiling [fn.native]
   produces [fn.cmxs] (what gets Dynlinked) alongside [fn.cmi] and [fn.cmx],
   which a LATER bundle in the same process needs on its [-I] path to
   reference this one's constants (see [Nativecode.stabilize_prefix] for why
   that reference is even content-stable across processes in the first
   place). Caching only the [.cmxs] would make any later, genuinely-new
   compile that depends on a cache-served bundle fail outright for a missing
   [.cmi] -- publishing the whole sibling set under one atomic directory
   rename keeps every cache hit as capable of being depended on as a fresh
   compile would have been. *)
let companion_exts = [ ".cmxs"; ".cmi"; ".cmx" ]

let entry_dir root k = root / String.sub k 0 2 / k

let lock_path root k = root / String.sub k 0 2 / (k ^ ".lock")

(* --- stats --------------------------------------------------------------*)

let hits = ref 0
let misses = ref 0
let lock_wait = ref 0.

let stats_line () =
  Printf.sprintf "NATIVECACHE hits=%d misses=%d lock_wait_s=%.3f" !hits !misses !lock_wait

(* --- public API ----------------------------------------------------------*)

let cached_entry ~include_dirs source =
  match cache_root () with
  | None | Some "" -> None
  | Some root ->
    let k = key ~include_dirs source in
    let dir = entry_dir root k in
    if Sys.file_exists (dir / "obj.cmxs") then Some dir else None

let fetch_to ~include_dirs source ~dest_stem =
  match cached_entry ~include_dirs source with
  | None ->
    incr misses;
    false
  | Some dir ->
    incr hits;
    List.iter
      (fun ext ->
        let src = dir / ("obj" ^ ext) in
        if Sys.file_exists src then begin
          let dest = dest_stem ^ ext in
          if Sys.file_exists dest then Sys.remove dest;
          try Unix.link src dest
          with Unix.Unix_error ((Unix.EXDEV | Unix.EPERM | Unix.ENOSYS), _, _) -> copy_file ~src ~dst:dest
        end)
      companion_exts;
    true

let with_lock ~include_dirs source f =
  match cache_root () with
  | None | Some "" -> f ()
  | Some root ->
    let k = key ~include_dirs source in
    let lp = lock_path root k in
    mkdir_p (Filename.dirname lp);
    let fd = Unix.openfile lp [ Unix.O_CREAT; Unix.O_RDWR ] 0o644 in
    Fun.protect
      ~finally:(fun () -> Unix.close fd)
      (fun () ->
        let t0 = Unix.gettimeofday () in
        Unix.lockf fd Unix.F_LOCK 0;
        lock_wait := !lock_wait +. (Unix.gettimeofday () -. t0);
        Fun.protect ~finally:(fun () -> Unix.lockf fd Unix.F_ULOCK 0) f)

let publish ~include_dirs source ~compiled_stem =
  match cache_root () with
  | None | Some "" -> ()
  | Some root ->
    let k = key ~include_dirs source in
    let dest = entry_dir root k in
    mkdir_p (Filename.dirname dest);
    let tmp = Printf.sprintf "%s.tmp.%d.%d" dest (Unix.getpid ()) (Random.bits ()) in
    mkdir_p tmp;
    List.iter
      (fun ext ->
        let src = compiled_stem ^ ext in
        if Sys.file_exists src then copy_file ~src ~dst:(tmp / ("obj" ^ ext)))
      companion_exts;
    (* Same-directory rename is atomic on a POSIX filesystem: a concurrent
       reader either sees no directory yet, or the complete sibling set --
       never a partial one. [cached_entry] only trusts a directory once its
       [.cmxs] is visible, and [.cmxs] is always the last file written into
       [tmp] above relative to iteration order is irrelevant: the directory
       itself is invisible under [dest] until this rename. *)
    (try Unix.rmdir dest with Unix.Unix_error (Unix.ENOENT, _, _) -> ());
    Unix.rename tmp dest
