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

let rec remove_tree path =
  if Sys.is_directory path then begin
    Array.iter (fun f -> remove_tree (path / f)) (Sys.readdir path);
    Unix.rmdir path
  end
  else Sys.remove path

(* Copy [src] to [dst] byte-for-byte. *)
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

let absolute d = if Filename.is_relative d then Sys.getcwd () / d else d

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
  walk "" dir;
  let entries = List.sort (fun (a, _) (b, _) -> String.compare a b) !entries in
  String.concat "\n" (List.map (fun (rel, h) -> rel ^ " " ^ h) entries)

(* --- epoch: everything that can change what a given source compiles to - *)

(* An unreadable component of the epoch is an error, never a fixed marker: a
   marker would let two different toolchains share one epoch. *)
let read_process_stdout argv =
  let ic = Unix.open_process_args_in (List.hd argv) (Array.of_list argv) in
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  (match Unix.close_process_in ic with
   | Unix.WEXITED 0 -> ()
   | _ -> CErrors.user_err Pp.(str "native cache: cannot run " ++ str (String.concat " " argv)));
  Buffer.contents buf

let self_binary_digest () =
  let path =
    if Sys.file_exists "/proc/self/exe" then Unix.readlink "/proc/self/exe" else Sys.executable_name
  in
  Sha256.hex_digest (read_file path)

let compute_epoch ~include_dirs ~flags =
  let ocamlfind = Boot.Env.ocamlfind () in
  let parts =
    [
      "self=" ^ self_binary_digest ();
      "ocamlfind_bin=" ^ Sha256.hex_digest (read_file ocamlfind);
      "ocamlopt_version=" ^ read_process_stdout [ ocamlfind; "ocamlopt"; "-version" ];
      "ocaml_version=" ^ Sys.ocaml_version;
      "flags=" ^ String.concat " " flags;
    ]
    @ List.map (fun d -> "include_dir[" ^ d ^ "]=" ^ hash_tree d) include_dirs
  in
  Sha256.hex_digest (String.concat "\n" parts)

(* --- layout ------------------------------------------------------------- *)

(* One cache entry is one compilation UNIT of the native conversion's
   dependency closure (or one cast's own unit). Its key covers the epoch, the
   unit's generated source and the digests of the compiled artifacts of every
   earlier unit that source names ([deps]): the source mentions an earlier
   unit only by module name, and a compile against a different
   [.cmi]/[.cmx] of that module would link inconsistently, so the artifacts
   themselves are part of the key. The unit's OCaml module name is derived
   from the key, so two different artifacts can never share a name. *)
let module_name_len = 40

let module_name key = "Coq_native" ^ String.sub key 0 module_name_len

let object_ext = if Dynlink.is_native then ".cmxs" else ".cmo"

(* An entry is a DIRECTORY holding the loadable object next to the interface
   files a later unit needs on its [-I] path to reference this one's
   constants. It is published by one atomic directory rename, so a reader
   sees all of it or nothing. *)
let companion_exts = if Dynlink.is_native then [ ".cmxs"; ".cmi"; ".cmx" ] else [ ".cmo"; ".cmi" ]

let entry_dir root k = root / String.sub k 0 2 / k

let lock_path root k = root / String.sub k 0 2 / (k ^ ".lock")

(* --- stats --------------------------------------------------------------*)

let hits = ref 0
let misses = ref 0
let lock_wait = ref 0.

let reset_stats () =
  hits := 0;
  misses := 0;
  lock_wait := 0.

let stats_line () =
  Printf.sprintf "NATIVECACHE hits=%d misses=%d lock_wait_s=%.3f" !hits !misses !lock_wait

let note_miss () = incr misses

(* --- the cache root -----------------------------------------------------*)

type state = { root : string; epoch : string; run : string }

let state : state option ref = ref None

let get () =
  match !state with
  | Some s -> s
  | None -> CErrors.anomaly (Pp.str "Nativecache.init was not called before the first native conversion.")

let root () = (get ()).root

(* [ROCQCHK_NATIVE_CACHE] names the shared cache directory. Without it the
   checker still needs one (every unit is loaded from its entry directory, so
   that the artifacts a later unit compiled against are exactly the ones
   loaded): a private one is made and removed at exit by the process that
   made it. [init] must run before the [-j] workers fork so that they share it. *)
let init ~include_dirs ~flags =
  match !state with
  | Some _ -> ()
  | None ->
    let root =
      match Sys.getenv_opt "ROCQCHK_NATIVE_CACHE" with
      | Some d when d <> "" ->
        let d = absolute d in
        mkdir_p d;
        d
      | _ ->
        let d = CUnix.mktemp_dir "Coq_native_cache" "" in
        let owner = Unix.getpid () in
        at_exit (fun () -> if Unix.getpid () = owner then try remove_tree d with _ -> ());
        d
    in
    (* One id per run, shared with the workers through the environment: a
       failure marker only means something within the run that wrote it. *)
    let run =
      match Sys.getenv_opt "ROCQCHK_NATIVE_RUN" with
      | Some r when r <> "" -> r
      | _ ->
        Random.self_init ();
        let r = Printf.sprintf "%d-%d" (Unix.getpid ()) (Random.bits ()) in
        Unix.putenv "ROCQCHK_NATIVE_RUN" r;
        r
    in
    state := Some { root; epoch = compute_epoch ~include_dirs ~flags; run }

let key ~text ~deps = Sha256.hex_digest ((get ()).epoch ^ "\x00" ^ deps ^ "\x00" ^ text)

(* --- public API ----------------------------------------------------------*)

let lookup key =
  let dir = entry_dir (root ()) key in
  if Sys.file_exists (dir / (module_name key ^ object_ext)) then begin
    incr hits;
    Some dir
  end
  else None

let with_lock key f =
  let lp = lock_path (root ()) key in
  mkdir_p (Filename.dirname lp);
  let fd = Unix.openfile lp [ Unix.O_CREAT; Unix.O_RDWR ] 0o644 in
  Fun.protect
    ~finally:(fun () -> Unix.close fd)
    (fun () ->
      let t0 = Unix.gettimeofday () in
      Unix.lockf fd Unix.F_LOCK 0;
      lock_wait := !lock_wait +. (Unix.gettimeofday () -. t0);
      Fun.protect ~finally:(fun () -> Unix.lockf fd Unix.F_ULOCK 0) f)

let marker_path key = (root ()) / String.sub key 0 2 / (key ^ ".failed." ^ (get ()).run)

let failure_of key =
  let p = marker_path key in
  if Sys.file_exists p then Some (read_file p) else None

let record_failure key msg =
  let p = marker_path key in
  mkdir_p (Filename.dirname p);
  let oc = open_out_bin p in
  output_string oc msg;
  close_out oc

let scratch key =
  let dir = Printf.sprintf "%s.tmp.%d.%d" (entry_dir (root ()) key) (Unix.getpid ()) (Random.bits ()) in
  mkdir_p dir;
  dir

let publish key ~scratch =
  let name = module_name key in
  let dest = entry_dir (root ()) key in
  Array.iter
    (fun f -> if not (List.exists (fun ext -> f = name ^ ext) companion_exts) then Sys.remove (scratch / f))
    (Sys.readdir scratch);
  List.iter
    (fun ext ->
      if not (Sys.file_exists (scratch / (name ^ ext))) then
        CErrors.user_err Pp.(str "native unit " ++ str name ++ str " compiled without producing " ++ str ext))
    companion_exts;
  (* Same-directory rename is atomic on POSIX. An entry that already exists
     (published by a process that did not hold the lock) wins: every user, in
     every process, then loads that one set of artifacts. *)
  (try Unix.rename scratch dest
   with Unix.Unix_error ((Unix.ENOTEMPTY | Unix.EEXIST), _, _) -> remove_tree scratch);
  dest

let discard_scratch scratch = try remove_tree scratch with _ -> ()

let artifact_digest ~dir ~name =
  Sha256.hex_digest
    (String.concat "\x00"
       (List.map
          (fun ext -> read_file (dir / (name ^ ext)))
          (List.filter (fun e -> e <> object_ext) companion_exts)))
