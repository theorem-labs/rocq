(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* r3-b instrumentation: this whole file, and every line marked
   "r3-b instrumentation" in kernel/ and checker/, is measurement scaffolding
   for speed lane R3 design b. Remove it before release.

   With ROCQCHK_CONV_LOG=<dir> set, every VM cast that [Typeops.check_cast]
   decides appends one tab-separated line to <dir>/<pid>.tsv: pid, the
   constant being checked (or "-"), the backend, total seconds, code
   generation seconds, OCaml compile seconds, load-and-evaluate seconds, the
   bytes of the unit's .ml file, and the seconds the VM ran under its budget;
   "-" where a field does not apply. Times are wall-clock
   ([Unix.gettimeofday]). *)

let dir =
  lazy (match Sys.getenv_opt "ROCQCHK_CONV_LOG" with
      | Some d when not (String.equal d "") -> Some d
      | Some _ | None -> None)

let enabled () = Option.has_some (Lazy.force dir)

type phase = Codegen | Compile | Load | Vm | Index | Wait

type unit_kind = Conv | Dep

type cast = {
  mutable backend : string;
  mutable codegen : float option;
  mutable compile : float option;
  mutable load : float option;
  mutable vm : float option;
  mutable unit_file : string option;
  (* The unit cache of the native conversion (checker/convCache.ml): the
     dependency unit's own code generation and compile, the time spent
     reading the index and waiting for another worker's claim, and what
     the cast took from the cache. *)
  mutable dep_codegen : float option;
  mutable dep_compile : float option;
  mutable index : float option;
  mutable wait : float option;
  mutable cache : string;
  mutable reused : int;
  mutable units : int;
  mutable copied : int;
  mutable copied_bytes : int;
  mutable manifest_bytes : int;
}

let cast = {
  backend = "vm"; codegen = None; compile = None; load = None; vm = None; unit_file = None;
  dep_codegen = None; dep_compile = None; index = None; wait = None;
  cache = "-"; reused = 0; units = 0; copied = 0; copied_bytes = 0; manifest_bytes = 0;
}

let unit_kind = ref Conv

let constant : Names.Constant.t option ref = ref None

let with_constant c f =
  if not (enabled ()) then f ()
  else begin
    let saved = !constant in
    constant := Some c;
    Fun.protect ~finally:(fun () -> constant := saved) f
  end

let start () =
  if not (enabled ()) then 0.
  else begin
    cast.backend <- "vm";
    cast.codegen <- None;
    cast.compile <- None;
    cast.load <- None;
    cast.vm <- None;
    cast.unit_file <- None;
    cast.dep_codegen <- None;
    cast.dep_compile <- None;
    cast.index <- None;
    cast.wait <- None;
    cast.cache <- "-";
    cast.reused <- 0;
    cast.units <- 0;
    cast.copied <- 0;
    cast.copied_bytes <- 0;
    cast.manifest_bytes <- 0;
    unit_kind := Conv;
    Unix.gettimeofday ()
  end

let set_backend b = if enabled () then cast.backend <- b

let set_unit_file f = if enabled () then cast.unit_file <- Some f

let set_cache ~status ~reused ~units ~copied ~copied_bytes ~manifest_bytes =
  if enabled () then begin
    cast.cache <- status;
    cast.reused <- reused;
    cast.units <- units;
    cast.copied <- copied;
    cast.copied_bytes <- copied_bytes;
    cast.manifest_bytes <- manifest_bytes
  end

let add phase dt =
  let plus = function None -> Some dt | Some t -> Some (t +. dt) in
  match phase, !unit_kind with
  | Codegen, Conv -> cast.codegen <- plus cast.codegen
  | Codegen, Dep -> cast.dep_codegen <- plus cast.dep_codegen
  | Compile, Conv -> cast.compile <- plus cast.compile
  | Compile, Dep -> cast.dep_compile <- plus cast.dep_compile
  | Load, _ -> cast.load <- plus cast.load
  | Vm, _ -> cast.vm <- plus cast.vm
  | Index, _ -> cast.index <- plus cast.index
  | Wait, _ -> cast.wait <- plus cast.wait

let time_add phase dt = if enabled () then add phase dt

let time phase f =
  if not (enabled ()) then f ()
  else begin
    let t0 = Unix.gettimeofday () in
    Fun.protect ~finally:(fun () -> add phase (Unix.gettimeofday () -. t0)) f
  end

let with_unit_kind k f =
  if not (enabled ()) then f ()
  else begin
    let saved = !unit_kind in
    unit_kind := k;
    Fun.protect ~finally:(fun () -> unit_kind := saved) f
  end

(* One descriptor per process: a [-j] worker is forked with its parent's
   descriptor, and opens its own file. Each line is one [write] on an
   [O_APPEND] descriptor, so nothing is buffered across a fork. *)
let out = ref None

let descriptor d =
  let pid = Unix.getpid () in
  match !out with
  | Some (p, fd) when Int.equal p pid -> fd
  | Some _ | None ->
    let file = Filename.concat d (string_of_int pid ^ ".tsv") in
    let fd = Unix.openfile file Unix.[O_WRONLY; O_APPEND; O_CREAT; O_CLOEXEC] 0o644 in
    out := Some (pid, fd);
    fd

let rec write_all fd s off len =
  if len > 0 then
    let n = Unix.write_substring fd s off len in
    write_all fd s (off + n) (len - n)

let seconds = function None -> "-" | Some t -> Printf.sprintf "%.6f" t

let field s = String.map (function '\t' | '\n' -> ' ' | c -> c) s

let finish t0 =
  match Lazy.force dir with
  | None -> ()
  | Some d ->
    let total = Unix.gettimeofday () -. t0 in
    let constant = match !constant with
      | None -> "-"
      | Some c -> field (Names.Constant.to_string c)
    in
    let bytes = match cast.unit_file with
      | None -> "-"
      | Some f ->
        (try string_of_int (Unix.stat f).Unix.st_size
         with Unix.Unix_error _ -> "-")
    in
    let line =
      Printf.sprintf "%d\t%s\t%s\t%.6f\t%s\t%s\t%s\t%s\t%s\t%.6f\t%s\t%d\t%d\t%d\t%d\t%d\t%s\t%s\t%s\t%s\n"
        (Unix.getpid ()) constant cast.backend total
        (seconds cast.codegen) (seconds cast.compile) (seconds cast.load) bytes
        (seconds cast.vm) t0
        cast.cache cast.reused cast.units cast.copied cast.copied_bytes cast.manifest_bytes
        (seconds cast.index) (seconds cast.wait)
        (seconds cast.dep_codegen) (seconds cast.dep_compile)
    in
    write_all (descriptor d) line 0 (String.length line)

(* The timeline: each process also writes <dir>/<pid>.events.tsv, one line
   per event, with its absolute wall-clock time ([Unix.gettimeofday]), the
   pid, the event's name and its fields. Merged and sorted by time, the
   files of all processes give the timeline of a check. *)
let module_init = Unix.gettimeofday ()

let events_out = ref None

let events_descriptor d =
  let pid = Unix.getpid () in
  match !events_out with
  | Some (p, fd) when Int.equal p pid -> fd
  | Some _ | None ->
    let file = Filename.concat d (string_of_int pid ^ ".events.tsv") in
    let fd = Unix.openfile file Unix.[O_WRONLY; O_APPEND; O_CREAT; O_CLOEXEC] 0o644 in
    events_out := Some (pid, fd);
    fd

let event name fields =
  match Lazy.force dir with
  | None -> ()
  | Some d ->
    let line =
      String.concat "\t"
        (Printf.sprintf "%.6f" (Unix.gettimeofday ()) :: string_of_int (Unix.getpid ()) ::
         name :: List.map field fields) ^ "\n"
    in
    write_all (events_descriptor d) line 0 (String.length line)

let process_start () =
  event "process-start" [Printf.sprintf "module_init=%.6f" module_init]
