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
open Names

let debug = CDebug.create ~name:"checker-workers" ()

type task = Constant.t * (unit -> unit)

(* What the main process keeps about a running worker, for error
   messages. The closures are dropped once the worker is forked. *)
type batch = {
  size : int;
  first : Constant.t;
  last : Constant.t;
}

exception CheckError of Constant.t * exn
exception WorkerFailed of int * Unix.process_status * batch

(* Maximal number of workers alive at the same time. 0 means that
   deferred checks are run immediately, in the main process. *)
let max_workers = ref 0

let set_jobs ~profiling n =
  if n > 1 then
    if not Sys.unix then
      Feedback.msg_warning
        (str "Option -j needs Unix.fork, which is not available on this platform;" ++
         spc () ++ str "checking sequentially.")
    else if profiling then
      Feedback.msg_warning
        (str "Option -j is ignored when profiling; checking sequentially.")
    else max_workers := n - 1

let error_printer = ref (fun _ -> ())
let set_error_printer f = error_printer := f

(* Scheduling.

   Forking is not free: the fork itself, and the copy-on-write faults
   that follow in the main process, cost time in proportion to the size
   of the heap. The faults are paid once per fork, or once for several
   forks made together. So while the libraries are being checked,
   deferred checks are handed out at most once every [window] seconds,
   to all the free worker slots at once. The main process does not wait
   for workers until it is done with the libraries.

   The cost of a proof is not known in advance, it varies wildly, and
   costly proofs tend to be in the same library, hence deferred in a
   row. So the checks handed out together are dealt round-robin to the
   workers, and a worker is given at most a [1/N] share of the queued
   checks, where [N] is the number of processes.

   Once the libraries are checked, all that is left is known. It is
   dealt out by guided self-scheduling: whenever a worker slot is free,
   it is given a share of what remains, proportional to it, and in
   between the main process checks the remaining proofs itself, one at a
   time, so that all processes finish at about the same time. *)
let window = 1.0

(* Below this, a batch is not worth a fork, while the libraries are
   being checked, and once they are. *)
let min_batch = 50
let min_share = 10

(* Deferred checks not yet given to a worker, oldest first. *)
let queue : task Queue.t = Queue.create ()
let last_dispatch = ref 0.

(* Running workers, by pid. *)
let running : (int * batch) list ref = ref []

let flush_output () =
  Format.pp_print_flush Format.std_formatter ();
  Format.pp_print_flush Format.err_formatter ();
  flush_all ()

let rec waitpid_non_intr flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr flags pid

(* A worker only reads the heap it inherits, but the GC writes to the
   headers of the objects it marks, and each page written to is copied.
   A larger minor heap promotes fewer objects, so there is less work for
   the major GC, and compaction, which would copy everything, is turned
   off. The space overhead is left alone: a lazier major GC would copy
   fewer pages, but let the heap grow with garbage instead. *)
let tune_gc () =
  let gc = Gc.get () in
  Gc.set { gc with
           Gc.minor_heap_size = max gc.Gc.minor_heap_size (4 * 1024 * 1024);
           max_overhead = 1000000 }

(* Runs in the child, never returns. *)
let run_worker parent (tasks : task array) =
  let current = ref (fst tasks.(0)) in
  (* Only reaching the end of the batch may count as success. *)
  at_exit (fun () -> Unix._exit 2);
  let code =
    try
      tune_gc ();
      Array.iter (fun (kn, check) ->
          (* Nobody is waiting for the result any more. *)
          if Unix.getppid () <> parent then Unix._exit 1;
          current := kn;
          check ())
        tasks;
      0
    with e ->
      (try !error_printer (CheckError (!current, e)) with _ -> ());
      CErrors.exit_code e
  in
  (try flush_output () with _ -> ());
  (* Not [exit]: the at_exit functions of the main process must not run
     here. *)
  Unix._exit code

let check_here (kn, check) =
  try check ()
  with e ->
    let e, info = Exninfo.capture e in
    Exninfo.iraise (CheckError (kn, e), info)

let batch_of_tasks tasks =
  let size = Array.length tasks in
  { size; first = fst tasks.(0); last = fst tasks.(size - 1) }

let pr_batch b =
  int b.size ++ str " " ++ str (CString.plural b.size "opaque proof") ++ spc () ++
  str "(the first is " ++ Constant.print b.first ++ str "," ++ spc () ++
  str "the last " ++ Constant.print b.last ++ str ")"

let spawn tasks =
  let batch = batch_of_tasks tasks in
  (* Otherwise the child would print again what is still buffered. *)
  flush_output ();
  let parent = Unix.getpid () in
  match Unix.fork () with
  | 0 -> run_worker parent tasks
  | pid ->
    debug (fun () -> str "worker " ++ int pid ++ str ": " ++ pr_batch batch);
    running := (pid, batch) :: !running
  | exception Unix.Unix_error (err, _, _) ->
    debug (fun () ->
        str "cannot fork (" ++ str (Unix.error_message err) ++
        str "), checking here " ++ pr_batch batch);
    Array.iter check_here tasks

let signal_name s =
  let names = Sys.[
      sigabrt, "SIGABRT"; sigbus, "SIGBUS"; sigfpe, "SIGFPE";
      sighup, "SIGHUP"; sigill, "SIGILL"; sigint, "SIGINT";
      sigkill, "SIGKILL"; sigpipe, "SIGPIPE"; sigquit, "SIGQUIT";
      sigsegv, "SIGSEGV"; sigterm, "SIGTERM"; sigxcpu, "SIGXCPU";
    ]
  in
  match List.assoc_opt s names with
  | Some name -> name
  | None -> "signal " ^ string_of_int s

let abort () =
  let workers = !running in
  running := [];
  Queue.clear queue;
  List.iter (fun (pid, _) ->
      try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ())
    workers;
  List.iter (fun (pid, _) ->
      try ignore (waitpid_non_intr [] pid) with Unix.Unix_error _ -> ())
    workers

(* Anything but a normal exit with code 0 means that the batch is not
   known to be correct. *)
let reaped pid status =
  match List.assoc_opt pid !running with
  | None -> ()
  | Some batch ->
    running := List.remove_assoc pid !running;
    match status with
    | Unix.WEXITED 0 -> debug (fun () -> str "worker " ++ int pid ++ str " succeeded")
    | _ ->
      abort ();
      raise (WorkerFailed (pid, status, batch))

let rec reap_finished () =
  if not (CList.is_empty !running) then
    match waitpid_non_intr [Unix.WNOHANG] (-1) with
    | 0, _ -> ()
    | pid, status -> reaped pid status; reap_finished ()

let free_slots () = !max_workers - List.length !running

(* Take [k * size] checks (or all) from the front of the queue and deal
   them round-robin into [k] batches. *)
let deal k size =
  let n = min (Queue.length queue) (k * size) in
  let batches = Array.make k [] in
  for i = 0 to n - 1 do
    batches.(i mod k) <- Queue.pop queue :: batches.(i mod k)
  done;
  Array.iter (fun l -> if not (CList.is_empty l) then spawn (Array.of_list (List.rev l))) batches

let defer kn check =
  if !max_workers = 0 then check ()
  else begin
    Queue.push (kn, check) queue;
    let now = Unix.gettimeofday () in
    if now -. !last_dispatch >= window then begin
      last_dispatch := now;
      reap_finished ();
      let n = Queue.length queue in
      let size = max min_batch ((n + !max_workers) / (!max_workers + 1)) in
      let k = min (free_slots ()) (n / size) in
      if k > 0 then deal k size
    end
  end

let finish () =
  if !max_workers > 0 then begin
    let nprocs = !max_workers + 1 in
    (* Shares are taken from the front of the queue: interleave it, so
       that each share is spread over all of it. *)
    let tasks = Array.of_seq (Queue.to_seq queue) in
    let stride = 2 * nprocs in
    Queue.clear queue;
    for s = 0 to stride - 1 do
      let i = ref s in
      while !i < Array.length tasks do
        Queue.push tasks.(!i) queue;
        i := !i + stride
      done
    done;
    while not (Queue.is_empty queue) do
      reap_finished ();
      let size = Queue.length queue / (2 * nprocs) in
      if free_slots () > 0 && size >= min_share then deal 1 size
      else check_here (Queue.pop queue)
    done;
    while not (CList.is_empty !running) do
      let pid, status = waitpid_non_intr [] (-1) in
      reaped pid status
    done
  end
