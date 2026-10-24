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

let force_temp_dir () = ignore (Lazy.force my_temp_dir : string)

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

(* coqchk's [-j] workers are forked with one copy of [Filename]'s random
   state, and write their units in one directory ([force_temp_dir]): the
   names that [Filename.temp_file] draws in one worker are those it draws
   in the next, and after 1000 names taken it fails. So while
   [Nativecode.native_vm_conversion ()] holds, a unit is named after the
   pid of its process and a counter of that process; [O_EXCL] settles a
   pid that an earlier worker had. *)
let unit_counter = ref 0

let rec fresh_unit_filename temp_dir =
  incr unit_counter;
  let base = Printf.sprintf "Coq_native%d_%d" (Unix.getpid ()) !unit_counter in
  let filename = temp_dir / (base ^ source_ext) in
  match Unix.openfile filename Unix.[O_WRONLY; O_CREAT; O_EXCL; O_CLOEXEC] 0o600 with
  | fd -> Unix.close fd; filename
  | exception Unix.Unix_error (Unix.EEXIST, _, _) -> fresh_unit_filename temp_dir

let get_ml_filename () =
  let temp_dir = Lazy.force my_temp_dir in
  let filename =
    if Nativecode.native_vm_conversion () then fresh_unit_filename temp_dir
    else Filename.temp_file ~temp_dir "Coq_native" source_ext
  in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

(* The directory of the checker's unit cache (see checker/convCache.ml),
   made by the main process before the first fork and added to the include
   dirs, so that a unit finds the .cmi of the units it refers to. The cache
   removes it itself, before the temp dir goes. *)
let cache_dir = ref None

let cache_directory () = match !cache_dir with
  | Some d -> d
  | None ->
    let d = CUnix.mktemp_dir ~temp_dir:(Lazy.force my_temp_dir) "cache" "" in
    cache_dir := Some d;
    include_dirs := d :: !include_dirs;
    d

let cache_directory_made () = !cache_dir

let cache_ml_filename () =
  let filename = fresh_unit_filename (cache_directory ()) in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

let write_ml_code fn ?(header=[]) code =
  let header = open_header@header in
  let ch_out = open_out fn in
  let fmt = Format.formatter_of_out_channel ch_out in
  List.iter (pp_global fmt) (header@code);
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

(* The flags of every compile of generated code: the same for a unit
   compiled whole and for the parts of one. *)
let compiler_flags ~profile =
  (* The below path is computed from Require statements, by uniquizing
     the paths, see [Library.get_used_load_paths] This is in general
     hacky and we should do a bit better once we move loadpath to its
     own library *)
  let require_load_path = !get_load_paths () in
  (* We assume that installed files always go in .coq-native for now *)
  (* To ease the build we also consider the current dir, but at some point the build system should manage both *)
  let install_load_path = List.map (fun dn -> dn / dft_output_dir) require_load_path @ require_load_path in
  let include_dirs = List.flatten (List.map (fun x -> ["-I"; x]) (get_include_dirs () @ install_load_path)) in
  let profile_args =
    if profile then
      ["-g"]
    else
      []
  in
  let flambda_args = if Sys.(backend_type = Native) then ["-Oclassic"] else [] in
  profile_args @ flambda_args @ ("-rectypes" :: "-w" :: "a" :: include_dirs)

(** {6 Compile slots}

    With a check-wide directory and a cap, every compile of generated code
    in the check holds one slot while its compiler runs. Slot [k] is the
    file [slot.<k>.<generation>], for [k] below the cap.

    - Ownership is published whole: the taker writes its pid into a
      private file, then installs it under the slot's name with
      [Unix.link], which fails when the name exists. A slot file is never
      visible incomplete, and two takers of one generation cannot both win.
    - The live generation of slot [k] is the highest one present. It is
      held while its holder lives, or while the compile it runs lives: the
      holder records the compiler's process group in [<slot>.child] before
      the compiler may start ([spawn_compiler] below), and the compiler and
      every process it starts are in that group. When both are gone, the
      next taker creates the next generation; nobody removes a file another
      process made.
    - A holder removes its own slot file when it releases it, and nothing
      else removes one. So a file still present after its holder was seen
      dead is the file of a holder that is gone, and the next generation
      belongs above it; a file that went while it was read was released
      by a live holder, and the slot itself is free again. Taking the
      next generation there would leave a free generation below for
      another taker, and two live holders in one slot. [slot_state] tells
      the two apart on the descriptor it read the record from
      ([Unix.fstat], [st_nlink]), and every slot file is a fresh file.
    - A slot file that cannot be parsed counts as held: only a recorded pid
      that no longer exists frees a slot.
    - Only [EEXIST] means contention. Any other error on the slot files
      ends the compile with [Unix.Unix_error], which the native conversion
      turns into its VM fallback, rather than waiting for a slot that
      cannot be taken. A wait that lasts [slot_wait_limit] ends the same
      way.
    - A slot is released on every exit of the compile that holds it, after
      the compiler is killed and reaped. A process waits for a slot only
      before a compile, never while it holds a claim it would wait on.
    - A compile dies with the process that started it: its supervisor
      ([spawn_compiler]) kills the compile's group when the gate pipe of
      the process that asked for it closes. So the slot frees too, and
      nothing of the check keeps a core or coqchk's output after coqchk
      is gone. *)

let slots : (string * int) option ref = ref None

let held_slots : string list ref = ref []

let slot_file dir k g = dir / Printf.sprintf "slot.%d.%d" k g
let child_file slot = slot ^ ".child"

let pid_alive pid = match Unix.kill pid 0 with
  | () -> true
  | exception Unix.Unix_error (Unix.ESRCH, _, _) -> false
  | exception Unix.Unix_error _ -> true

let group_alive pgid = pid_alive (- pgid)

(* The pid a slot file holds: [`Pid p], [`Garbled] for a file that exists
   but holds no pid, [`Gone] for a file removed meanwhile. Any other error
   is raised. *)
let read_pid_fd fd =
  let buf = Bytes.create 32 in
  let n = Unix.read fd buf 0 32 in
  match int_of_string_opt (String.trim (Bytes.sub_string buf 0 n)) with
  | Some p when p > 0 -> `Pid p
  | Some _ | None -> `Garbled

let read_pid f =
  match Unix.openfile f Unix.[O_RDONLY; O_CLOEXEC] 0 with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> `Gone
  | fd -> Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> read_pid_fd fd)

(* Write [content] into a new private file, then install it as [dest];
   [Unix.link] fails with [EEXIST] when [dest] exists. *)
let install_new ~dest content =
  let tmp = Printf.sprintf "%s.tmp%d" dest (Unix.getpid ()) in
  let fd = Unix.openfile tmp Unix.[O_WRONLY; O_CREAT; O_EXCL; O_CLOEXEC] 0o600 in
  Fun.protect ~finally:(fun () -> try Unix.unlink tmp with Unix.Unix_error _ -> ()) (fun () ->
      let () =
        Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
            let n = Unix.write_substring fd content 0 (String.length content) in
            if n <> String.length content then
              raise (Unix.Unix_error (Unix.EIO, "write", tmp)))
      in
      Unix.link tmp dest)

let rec live_generation dir k g =
  if Sys.file_exists (slot_file dir k (g + 1)) then live_generation dir k (g + 1) else g

(* The state of the slot file [f]: [`Held] (its holder is alive, or the
   compile it recorded is, or its record cannot be read), [`Stale] (the
   file of a holder that is gone: the next generation belongs above it)
   or [`Free] (no file at all: the slot is free from generation 0).

   The record is read through one descriptor, and the holder's life is
   tested between that read and [Unix.fstat] of the same descriptor. A
   link count of zero there says that this very file was removed, which
   only its holder does, and only while it is alive: the holder released
   the slot under the reader, so the slot is free rather than stale. A
   new holder's file is always a new file ([install_new] links one), so
   the count never answers for another holder's file. *)
let slot_state f =
  match Unix.openfile f Unix.[O_RDONLY; O_CLOEXEC] 0 with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> `Free
  | fd ->
    Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
        match read_pid_fd fd with
        | `Garbled -> `Held
        | `Pid p ->
          let compiling () = match read_pid (child_file f) with
            (* Until the compile's [setsid], only its pid exists. *)
            | `Pid g -> pid_alive g || group_alive g
            | `Garbled -> true
            | `Gone -> false
          in
          if pid_alive p || compiling () then `Held
          else if Int.equal (Unix.fstat fd).Unix.st_nlink 0 then `Free
          else `Stale)

let try_slot dir k =
  let g =
    if not (Sys.file_exists (slot_file dir k 0)) then Some 0
    else
      let g = live_generation dir k 0 in
      match slot_state (slot_file dir k g) with
      | `Held -> None
      | `Free -> None               (* released meanwhile: look again *)
      | `Stale -> Some (g + 1)
  in
  match g with
  | None -> None
  | Some g ->
    let f = slot_file dir k g in
    match install_new ~dest:f (string_of_int (Unix.getpid ())) with
    | () -> held_slots := f :: !held_slots; Some f
    | exception Unix.Unix_error (Unix.EEXIST, _, _) -> None

(* A backstop for a slot wait that never ends (a recorded pid reused by an
   unrelated process). *)
let slot_wait_limit = 600.

(* A slot, waiting until one frees; [poll] runs between attempts (a
   caller reaps its own finished compiles there). [None] when the check
   has no slots. *)
let acquire_slot ?(poll = fun () -> ()) () =
  match !slots with
  | None -> None
  | Some (dir, cap) ->
    let t0 = Unix.gettimeofday () in
    let rec first k = if k >= cap then None else
        match try_slot dir k with Some f -> Some f | None -> first (k + 1) in
    let rec go () = match first 0 with
      | Some f -> f
      | None ->
        if Unix.gettimeofday () -. t0 > slot_wait_limit then begin
          (* r3-b instrumentation *)
          ConvLog.event "slot-backstop" [Printf.sprintf "%.3f" (Unix.gettimeofday () -. t0)];
          raise (Unix.Unix_error (Unix.ETIMEDOUT, "acquire_slot", dir))
        end;
        poll (); (try Unix.sleepf 0.02 with Unix.Unix_error _ -> ()); go ()
    in
    let f = go () in
    let waited = Unix.gettimeofday () -. t0 in
    (* r3-b instrumentation *)
    if waited > 0.01 then ConvLog.event "slot-wait" [Printf.sprintf "%.6f" waited];
    Some f

let release_slot = function
  | None -> ()
  | Some f ->
    (try Sys.remove (child_file f) with Sys_error _ -> ());
    (try Sys.remove f with Sys_error _ -> ());
    held_slots := List.filter (fun g -> not (String.equal f g)) !held_slots

(** {6 Compiler processes} *)

let rec waitpid_non_intr flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr flags pid

(* The write ends of the gate pipes of the compiles this process has
   running. A new compile's supervisor closes every one of them, so that
   the end of its own pipe reaches it when the process that started it
   is gone, and not when that process's last other compile ends. *)
let gate_fds : Unix.file_descr list ref = ref []

let close_gate fd =
  gate_fds := List.filter (fun g -> g <> fd) !gate_fds;
  (try Unix.close fd with Unix.Unix_error _ -> ())

(* The longest a supervisor waits before it looks at its child again. *)
let supervise_poll = 0.5

(* The supervisor of one compile. It is the leader of the compile's
   process group [pgid], starts the compiler in that group, and exits
   with the compiler's status, as the compiler itself did before. If the
   process that asked for the compile dies first, the supervisor reads
   end-of-file on [gate] and kills the group, itself included: a compile
   never outlives the coqchk process that started it, neither holding a
   core nor keeping coqchk's output open. Ctrl-C and [timeout] signal
   coqchk's process group, which the compile's own group is not part of
   ([setsid] below), and [CheckWorkers.abort] kills a worker outright, so
   this is what ends a compile in all three cases. (Linux's
   [PR_SET_PDEATHSIG] would reach the compiler alone and leave the
   processes it started, which is where the work is: [ocamlfind] runs
   [ocamlopt] as a child.)

   The compiler is this process's only child. SIGCHLD is turned into a
   byte on a pipe that [select] watches, so the compiler's exit usually
   ends the wait at once. OCaml runs a signal handler only at a safe
   point, though: a SIGCHLD that arrives after the runtime's last check
   before [select] enters the kernel writes its byte only once [select]
   returns, and a SIGCHLD blocked in the mask this process inherited is
   never handled. So [select] waits at most [supervise_poll] seconds, and
   the child's status is read before each wait: a missed wake-up costs
   that long, never a hang. *)
let supervise ~gate ~pgid ocamlfind argv =
  let sigr, sigw = Unix.pipe ~cloexec:true () in
  Sys.set_signal Sys.sigchld
    (Sys.Signal_handle (fun _ -> try ignore (Unix.write_substring sigw "x" 0 1 : int) with _ -> ()));
  let pid = match Unix.fork () with
    | 0 ->
      (try
         Sys.set_signal Sys.sigchld Sys.Signal_default;
         Unix.close gate; Unix.close sigr; Unix.close sigw;
         Unix.execvp ocamlfind argv
       with _ -> ());
      Unix._exit 127
    | pid -> pid
  in
  let buf = Bytes.create 64 in
  let rec wait () =
    match waitpid_non_intr [Unix.WNOHANG] pid with
    | 0, _ ->
      let ready = match Unix.select [gate; sigr] [] [] supervise_poll with
        | r, _, _ -> r
        | exception Unix.Unix_error (Unix.EINTR, _, _) -> []
        | exception Unix.Unix_error _ ->
          (* A [select] that keeps failing must not spin: wait as long. *)
          (try Unix.sleepf supervise_poll with Unix.Unix_error _ -> ()); []
      in
      let gone = List.exists (fun fd -> fd = gate) ready
                 && (match Unix.read gate buf 0 1 with
                     | n -> Int.equal n 0
                     | exception Unix.Unix_error _ -> true)
      in
      if gone then begin
        (* The compiler, what it started, and this process. *)
        (try Unix.kill (- pgid) Sys.sigkill with Unix.Unix_error _ -> ());
        Unix._exit 137
      end;
      if List.exists (fun fd -> fd = sigr) ready then
        (try ignore (Unix.read sigr buf 0 64 : int) with Unix.Unix_error _ -> ());
      wait ()
    | _, status -> status
    | exception Unix.Unix_error _ -> Unix.WEXITED 127
  in
  match wait () with
  | Unix.WEXITED n -> Unix._exit n
  | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> Unix._exit 128

(* Start [ocamlfind args] in a process group of its own, holding [slot],
   under a supervisor ([supervise]) that ties it to this process. The
   child makes its group, then waits on the gate pipe; the parent records
   the group in [<slot>.child] and only then lets it start the compiler.
   If the parent dies before that, the child reads end-of-file and exits
   without running the compiler, so no compile ever runs that its slot
   does not account for. The parent keeps the gate pipe's write end, and
   closes it ([close_gate]) when the compile is over and reaped: its end
   is how the supervisor learns that this process is gone. The supervisor
   is reaped by its pid: in a worker, the main process's [waitpid (-1)]
   never sees it. *)
let spawn_compiler ?slot args =
  let ocamlfind = Boot.Env.ocamlfind () in
  debug_native_compiler (fun () -> Pp.str (ocamlfind ^ " " ^ (String.concat " " args)));
  let argv = Array.of_list (ocamlfind :: args) in
  let r, w = Unix.pipe ~cloexec:true () in
  match Unix.fork () with
  | exception e -> Unix.close r; Unix.close w; raise e
  | 0 ->
    (try
       List.iter (fun fd -> try Unix.close fd with Unix.Unix_error _ -> ()) !gate_fds;
       Unix.close w;
       let pgid = Unix.setsid () in
       let b = Bytes.create 1 in
       if Int.equal (Unix.read r b 0 1) 1 then supervise ~gate:r ~pgid ocamlfind argv
     with _ -> ());
    Unix._exit 127
  | pid ->
    Unix.close r;
    let gate () =
      Option.iter (fun s ->
          let c = child_file s in
          let tmp = Printf.sprintf "%s.tmp%d" c (Unix.getpid ()) in
          let fd = Unix.openfile tmp Unix.[O_WRONLY; O_CREAT; O_TRUNC; O_CLOEXEC] 0o600 in
          let () =
            Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
                let s = string_of_int pid in
                if Unix.write_substring fd s 0 (String.length s) <> String.length s then
                  raise (Unix.Unix_error (Unix.EIO, "write", tmp)))
          in
          Unix.rename tmp c)
        slot;
      if Unix.write_substring w "x" 0 1 <> 1 then raise (Unix.Unix_error (Unix.EIO, "write", "gate"))
    in
    match gate () with
    | () -> gate_fds := w :: !gate_fds; pid, w
    | exception e ->
      (* The child sees end-of-file and exits without starting it. *)
      Unix.close w;
      ignore (waitpid_non_intr [] pid);
      raise e

(* Kill a compile's process group, and reap its supervisor. *)
let kill_compiler pid =
  (try Unix.kill (- pid) Sys.sigkill
   with Unix.Unix_error _ -> (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ()));
  (try ignore (waitpid_non_intr [] pid) with Unix.Unix_error _ -> ())

(* Run [ocamlfind args] to completion under a slot; on any exit other than
   its completion, the compiler is killed and reaped before the slot is
   released. Without slots, as [CUnix.sys_command] runs it. *)
let run_command args =
  match !slots with
  | None ->
    let ocamlfind = Boot.Env.ocamlfind () in
    debug_native_compiler (fun () -> Pp.str (ocamlfind ^ " " ^ (String.concat " " args)));
    CUnix.sys_command ocamlfind args
  | Some _ ->
    let slot = acquire_slot () in
    Fun.protect ~finally:(fun () -> release_slot slot) (fun () ->
        let pid, gate = spawn_compiler ?slot args in
        let finished = ref false in
        Fun.protect
          ~finally:(fun () -> if not !finished then kill_compiler pid; close_gate gate)
          (fun () ->
            let _, status = waitpid_non_intr [] pid in
            finished := true;
            status))

let call_compiler ?profile:(profile=false) ml_filename =
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
  let args =
    initial_args @ ("-o" :: link_filename :: compiler_flags ~profile) @ ["-impl"; ml_filename] in
  (* [run_command] (or [spawn_compiler] under slots) prints the command
     under [debug_native_compiler]. *)
  try
    let res = run_command args in
    match res with
    | Unix.WEXITED 0 -> link_filename
    | Unix.WEXITED _n | Unix.WSIGNALED _n | Unix.WSTOPPED _n ->
      error_native_compiler_failed (Inl res)
  with Unix.Unix_error (e,_,_) ->
    error_native_compiler_failed (Inr e)

let compile fn code ~profile:profile =
  (* r3-b instrumentation *)
  ConvLog.time ConvLog.Codegen (fun () -> write_ml_code fn code);
  let r =
    (* r3-b instrumentation *)
    ConvLog.time ConvLog.Compile (fun () -> call_compiler ~profile fn) in
  (* NB: to prevent reusing the same filename we MUST NOT remove the file until exit
     cf #15263 *)
  delay_cleanup_file fn;
  r

(** {6 Units compiled as parts}

    A dependency unit of the checker's cache (checker/convCache.ml) above
    a size threshold is compiled as several OCaml modules, its parts:
    the globals, in emission order, which is dependency order, are cut
    into contiguous groups, each ending after a constant's own global so
    that a constant stays with the helpers emitted for it. The first part
    holds [symbols_tbl], the unit's one symbols table; every part opens
    every earlier part, so unprefixed names (helpers, constructors, the
    table) resolve to the earlier part that defines them, and names are
    unique within a unit, so an [open] shadows nothing. Each part gets a
    generated interface (see [Nativecode.interface_of_global]); the
    interfaces compile first, then every part compiles in parallel with
    [-opaque] against them, each holding a compile slot, then one
    [-shared] link joins the parts in order into the unit's [.cmxs].
    OCaml's interface digests check every reference across parts at
    compile, link and load time: a reference to a name a part does not
    export fails to compile. *)

type unit_part = {
  part_prefix : string;                        (* "<module>." of the part *)
  part_defs : Nativecode.definition list;   (* the definitions it defines *)
}

(* r3-b instrumentation: ROCQCHK_PARTS forces the number of parts of every
   dependency unit, for the measurement; tests set it through
   [set_forced_parts]. *)
let forced_parts = ref (Option.bind (Sys.getenv_opt "ROCQCHK_PARTS") int_of_string_opt)
let set_forced_parts p = forced_parts := p

(* The size that predicts a part's compile time: the bytes of its source
   outside string literals. A literal (a primitive string, written as one
   hexadecimal escape per byte, or the symbols table) costs the compiler
   almost nothing per byte: measured on Main5BothCerts0's dependency unit,
   a 44 MB part that is almost all one literal compiled in 0.64 s, while
   4 MB parts of code took 6 to 8 s. *)
let code_bytes s =
  let n = String.length s in
  let rec go i inside acc =
    if i >= n then acc
    else match s.[i] with
      | '"' -> go (i + 1) (not inside) (acc + 1)
      | '\\' when inside -> go (i + 2) inside acc
      | _ -> go (i + 1) inside (if inside then acc else acc + 1)
  in
  go 0 false 0

(* Parts of a unit of [code] code bytes: one below [part_threshold];
   above it, one part per [part_target] code bytes, at most [max_parts],
   and never more than the cap of compile slots. The figures come from the
   measurement (reports/step7-impl.md): about 1.8 s of compile per
   million code bytes, a fixed cost of about 0.3 s for the interfaces and
   0.4 s for the link. *)
let part_threshold = 3_000_000
let part_target = 1_500_000
let max_parts = 16

let parts_for code =
  match !forced_parts with
  | Some n -> max 1 n
  | None ->
    if code < part_threshold || not Dynlink.is_native then 1
    else
      let cap = match !slots with Some (_, c) -> c | None -> max_parts in
      max 1 (min (min max_parts cap) (Stdlib.( / ) (code + part_target - 1) part_target))

let write_file fn texts =
  let ch = open_out_bin fn in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () -> List.iter (output_string ch) texts)

(* Run a compile to completion under a slot; fail as a compile fails. *)
let run_compiler args =
  match run_command args with
  | Unix.WEXITED 0 -> ()
  | status -> error_native_compiler_failed (Inl status)

(* Compile the parts [(mli, ml)] of base [base], [ml] and [mli] the texts;
   return the [.cmxs]. Interfaces first, then the parts in parallel under
   slots, then the link. On every exit, every compiler still running is
   killed and reaped before its slot is released ([run_command],
   [kill_compiler]). *)
let compile_part_files ~base files =
  let n = Array.length files in
  let name k = Printf.sprintf "%s_p%d" base k in
  Array.iteri (fun k (mli, ml) ->
      write_file (name (k + 1) ^ ".mli") [mli];
      write_file (name (k + 1) ^ source_ext) [ml])
    files;
  Array.iteri (fun k _ ->
      delay_cleanup_file (name (k + 1) ^ ".mli");
      delay_cleanup_file (name (k + 1) ^ source_ext))
    files;
  (* A part's compile finds its own interface, and the earlier parts', in
     the parts' directory: OCaml looks for an .mli's .cmi on the include
     path only. *)
  let flags = "-I" :: Filename.dirname base :: compiler_flags ~profile:false in
  let t0 = Unix.gettimeofday () in
  run_compiler (["opt"; "-c"] @ flags @ List.init n (fun k -> name (k + 1) ^ ".mli"));
  let t_intf = Unix.gettimeofday () -. t0 in
  let running = ref [] in          (* (pid, gate, slot, part, start) *)
  let times = Array.make n 0. in
  let failed = ref None in
  let reap ~block =
    running := List.filter (fun (pid, gate, slot, k, start) ->
        match waitpid_non_intr (if block then [] else [Unix.WNOHANG]) pid with
        | 0, _ -> true
        | _, status ->
          times.(k) <- Unix.gettimeofday () -. start;
          close_gate gate;
          release_slot slot;
          (match status with
           | Unix.WEXITED 0 -> ()
           | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
             if Option.is_empty !failed then failed := Some status);
          false)
      !running
  in
  let kill_all () =
    List.iter (fun (pid, gate, slot, _, _) -> kill_compiler pid; close_gate gate; release_slot slot) !running;
    running := []
  in
  let t1 = Unix.gettimeofday () in
  Fun.protect ~finally:kill_all (fun () ->
      for k = 0 to n - 1 do
        if Option.is_empty !failed then begin
          let slot = acquire_slot ~poll:(fun () -> reap ~block:false) () in
          let args = ["opt"; "-c"; "-opaque"] @ flags @ ["-impl"; name (k + 1) ^ source_ext] in
          match spawn_compiler ?slot args with
          | pid, gate -> running := (pid, gate, slot, k, Unix.gettimeofday ()) :: !running
          | exception e -> release_slot slot; raise e
        end
      done;
      while not (CList.is_empty !running) do
        reap ~block:false;
        if not (CList.is_empty !running) then (try Unix.sleepf 0.01 with Unix.Unix_error _ -> ())
      done);
  let t_parts = Unix.gettimeofday () -. t1 in
  (match !failed with Some status -> error_native_compiler_failed (Inl status) | None -> ());
  let cmxs = Dynlink.adapt_filename (base ^ ".cmo") in
  let t2 = Unix.gettimeofday () in
  run_compiler (["opt"; "-shared"; "-o"; cmxs] @ List.init n (fun k -> name (k + 1) ^ ".cmx"));
  let t_link = Unix.gettimeofday () -. t2 in
  (* r3-b instrumentation *)
  ConvLog.event "dep-unit-compile"
    [Filename.basename base; string_of_int n;
     Printf.sprintf "intf_s=%.3f" t_intf; Printf.sprintf "parts_s=%.3f" t_parts;
     Printf.sprintf "link_s=%.3f" t_link;
     "part_s=" ^ String.concat "," (Array.to_list (Array.map (Printf.sprintf "%.3f") times))];
  cmxs

(* Compile the dependency unit [code] (its first global the symbols table)
   of source file [ml] and prefix [prefix], whole or as parts; return the
   [.cmxs] and the parts, each with the definitions it defines. *)
let compile_unit ~ml ~prefix code =
  (* r3-b instrumentation *)
  let texts, header =
    ConvLog.time ConvLog.Codegen (fun () ->
        List.map (fun g -> g, Nativecode.print_global g) code,
        String.concat "" (List.map Nativecode.print_global open_header))
  in
  let bytes = List.fold_left (fun a (_, t) -> a + String.length t) 0 texts in
  let code = List.fold_left (fun a (_, t) -> a + code_bytes t) 0 texts in
  let parts = parts_for code in
  let all_defs gs = List.sort_uniq Nativecode.definition_compare
      (List.concat_map (fun (g, _) -> Nativecode.definitions_of_global g) gs) in
  (* r3-b instrumentation *)
  ConvLog.time ConvLog.Compile @@ fun () ->
  if parts <= 1 then begin
    write_file ml (header :: List.map snd texts);
    delay_cleanup_file ml;
    (* r3-b instrumentation *)
    ConvLog.event "dep-unit" [Filename.basename ml; "1"; string_of_int bytes; "code=" ^ string_of_int code];
    let cmxs = call_compiler ml in
    cmxs, [{ part_prefix = prefix; part_defs = all_defs texts }]
  end else begin
    (* Items end after a constant's own global; parts take whole items,
       about [code / parts] code bytes each. *)
    let target = Stdlib.( / ) (code + parts - 1) parts in
    let groups = ref [] and cur = ref [] and cur_code = ref 0 in
    List.iter (fun ((g, t) as x) ->
        cur := x :: !cur;
        cur_code := !cur_code + code_bytes t;
        if Nativecode.ends_item g && !cur_code >= target && List.length !groups < parts - 1 then begin
          groups := List.rev !cur :: !groups;
          cur := [];
          cur_code := 0
        end)
      texts;
    if not (CList.is_empty !cur) then groups := List.rev !cur :: !groups;
    let groups = Array.of_list (List.rev !groups) in
    let n = Array.length groups in
    let base = Filename.chop_extension ml in
    let modname k = String.capitalize_ascii (Filename.basename base) ^ Printf.sprintf "_p%d" k in
    let files = Array.mapi (fun k gs ->
        let mli = String.concat "" (List.filter_map (fun (g, _) -> Nativecode.interface_of_global g) gs) in
        let opens = String.concat "" (List.init k (fun j -> Printf.sprintf "open %s\n" (modname (j + 1)))) in
        let ml = String.concat "" (header :: opens :: List.map snd gs) in
        mli, ml)
        groups
    in
    (* r3-b instrumentation *)
    ConvLog.event "dep-unit"
      [Filename.basename ml; string_of_int n; string_of_int bytes; "code=" ^ string_of_int code;
       "part_bytes=" ^ String.concat "," (Array.to_list (Array.map (fun (_, ml) -> string_of_int (String.length ml)) files));
       "part_code=" ^ String.concat "," (Array.to_list (Array.map (fun (_, ml) -> string_of_int (code_bytes ml)) files))];
    let cmxs = compile_part_files ~base files in
    cmxs, Array.to_list (Array.mapi (fun k gs ->
        { part_prefix = modname (k + 1) ^ "."; part_defs = all_defs gs }) groups)
  end

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

(* A unit of the checker's cache: it defines constants and inductives
   only, and carries its own symbols in its source, so the loading process
   needs nothing of the process that generated it. It leaves [rt1] and
   [rt2] alone, and marks nothing linked: the caller marks the definitions
   it has checked ([Nativecode.link_definitions]). A unit compiled as
   parts registers the prefix of every part. *)
let load_unit ~prefixes f =
  if not (Sys.file_exists f) then
    CErrors.user_err Pp.(str "Cannot find native compiler file " ++ str f);
  if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
  (* Only now: a unit that fails to load must not be referred to, and
     OCaml cannot unload it (see [Nativeconv.native_conv_gen]). *)
  List.iter register_native_file prefixes

(* What a process does before it generates the code of a conversion: the
   checker's cache reuses here the definitions another worker has already
   compiled, and compiles and publishes the rest, so that the conversion
   itself compiles almost nothing. It does nothing in a process that has
   no cache. *)
let prepare_conversion :
  (Environ.env -> Constr.t -> Constr.t -> unit) ref =
  ref (fun _ _ _ -> ())

let execute_library ~prefix f symbols upds =
  let () = rt1 := None in
  let () = rt2 := None in
  let () = rsymbols := symbols in
  if not (Sys.file_exists f) then
    CErrors.user_err Pp.(str "Cannot find native compiler file " ++ str f);
  if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
  (* Only now: a unit that fails to load must not be referred to, and
     OCaml cannot unload it (see [Nativeconv.native_conv_gen]). *)
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
