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

(* What the main process keeps about a running worker. The batch is for
   error messages. The tasks are kept to re-queue what the worker did not
   check before its time budget ran out. [report] is the read end of the
   pipe on which the worker says how many checks it completed. *)
type batch = {
  size : int;
  first : Constant.t;
  last : Constant.t;
}

type worker = {
  pid : int;
  batch : batch;
  tasks : task array;
  report : Unix.file_descr;
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

(* Wall time, in seconds, after which a worker stops, once it has
   completed a check. See [run_worker]. *)
let default_budget = 20.
let budget = ref default_budget

let set_budget t =
  if not (t >= 0.) then invalid_arg "CheckWorkers.set_budget";
  budget := t

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
   row. So a batch is not a run of the queue but a stride of it: when
   the queue holds [s] batches of the size wanted, a batch takes one
   check in [s], from the front. Checks next to each other in the queue
   go to different batches. A worker that stops early puts the checks
   it did not do back at the front, so the first of them head the next
   batches: a long check given back does not wait behind the checks
   that followed it in its batch.

   While the libraries are being checked, the main process checks them,
   so there are at most [N-1] workers, where [N] is the number of
   processes, and a worker is given at most a [1/N] share of the queued
   checks.

   Once the libraries are checked, all that is left is known, and the
   main process only hands out checks and waits for workers, which costs
   it no processor time. So there are up to [N] workers, and the main
   process checks nothing itself. It deals by guided self-scheduling:
   whenever a worker slot is free, it is given [1/(2N)] of what remains,
   and at least one check, so that all workers end at about the same
   time. *)
let window = 1.0

(* Below this, a batch is not worth a fork while the libraries are
   being checked. *)
let min_batch = 50

(* Deferred checks not yet given to a worker, oldest first. *)
let queue : task Queue.t = Queue.create ()
let last_dispatch = ref 0.

(* Running workers. *)
let running : worker list ref = ref []

(* Statistics, for the debug output. *)
let forks = ref 0
let early_stops = ref 0

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

(* What a worker tells the main process, in order on its pipe:
   - the number of checks it completed, the first ones of its batch in
     order, as [report_size] bytes (big endian); then
   - the constants whose VM globals it linked while checking them, framed
     with an 8-byte big-endian byte length followed by that many bytes of
     a marshalled [Constant.t list].
   The count is still a message of exactly [report_size] bytes, validated
   as before. The main process links the same constants before its next
   deal, so that later forks inherit them. Nothing but this count then
   frame is ever written. *)
let report_size = 8

let write_all fd b =
  let n = Bytes.length b in
  let rec go off = if off < n then go (off + Unix.write fd b off (n - off)) in
  go 0

let default_report_writer fd completed linked =
  let blob = Marshal.to_bytes (linked : Constant.t list) [] in
  let header = Bytes.create (report_size + 8) in
  Bytes.set_int64_be header 0 (Int64.of_int completed);
  Bytes.set_int64_be header report_size (Int64.of_int (Bytes.length blob));
  write_all fd header;
  write_all fd blob

let report_writer = ref default_report_writer
let set_report_writer f = report_writer := f

(* Runs in the child, never returns.

   The batch is checked in order. The time a worker lives is what makes
   its private memory grow: the garbage collector keeps touching the heap
   it shares copy-on-write with the main process. So once the budget has
   passed, the worker stops after the check it is in, reports how many it
   completed, and exits; the main process re-queues the rest. At least
   one check is completed first, whatever the budget, so that the
   checking always progresses. *)
let run_worker parent report (tasks : task array) =
  let size = Array.length tasks in
  let current = ref (fst tasks.(0)) in
  let completed = ref 0 in
  (* Only reaching the end of the batch, or a stop that is reported, may
     count as success. *)
  at_exit (fun () -> Unix._exit 2);
  let deadline = Unix.gettimeofday () +. !budget in
  (* Collect the constants whose VM globals this worker links while
     checking its batch, to report them so the main process links them
     too and later forks inherit them. A constant is recorded once, when
     first linked; globals inherited from the main process at fork time
     are already linked and are not recorded. *)
  let linked = ref [] in
  Vmsymtable.set_link_recorder (fun kn -> linked := kn :: !linked);
  let code =
    try
      tune_gc ();
      while !completed < size
            && (!completed = 0 || Unix.gettimeofday () < deadline) do
        let kn, check = tasks.(!completed) in
        (* Nobody is waiting for the result any more. *)
        if Unix.getppid () <> parent then Unix._exit 1;
        current := kn;
        check ();
        incr completed
      done;
      0
    with e ->
      (try !error_printer (CheckError (!current, e)) with _ -> ());
      CErrors.exit_code e
  in
  let code =
    if code <> 0 then code
    else (try !report_writer report !completed !linked; 0 with _ -> 3)
  in
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
  let check_here_instead err =
    debug (fun () ->
        str "cannot fork (" ++ str err ++
        str "), checking here " ++ pr_batch batch);
    Array.iter check_here tasks
  in
  match Unix.pipe ~cloexec:true () with
  | exception Unix.Unix_error (err, _, _) -> check_here_instead (Unix.error_message err)
  | report, report_out ->
    match Unix.fork () with
    | 0 ->
      Unix.close report;
      List.iter (fun w -> try Unix.close w.report with Unix.Unix_error _ -> ()) !running;
      run_worker parent report_out tasks
    | pid ->
      Unix.close report_out;
      incr forks;
      debug (fun () -> str "worker " ++ int pid ++ str ": " ++ pr_batch batch);
      running := { pid; batch; tasks; report } :: !running
    | exception Unix.Unix_error (err, _, _) ->
      Unix.close report;
      Unix.close report_out;
      check_here_instead (Unix.error_message err)

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

let close_report fd = try Unix.close fd with Unix.Unix_error _ -> ()

let abort () =
  let workers = !running in
  running := [];
  Queue.clear queue;
  List.iter (fun w ->
      try Unix.kill w.pid Sys.sigkill with Unix.Unix_error _ -> ())
    workers;
  List.iter (fun w ->
      (try ignore (waitpid_non_intr [] w.pid) with Unix.Unix_error _ -> ());
      close_report w.report)
    workers

(* The worker's message on its pipe: the [report_size]-byte count, then,
   optionally, the constants whose VM globals it linked, framed with an
   8-byte big-endian byte length and that many bytes of a marshalled
   [Constant.t list]. A message of exactly the count and nothing else is a
   complete report of no linked constants; the count is validated as
   before either way. Reading drains the pipe to its end, so a worker
   writing a large frame makes progress even before the main process waits
   for it. A short count, a truncated or over-long frame, or anything
   after the frame is rejected — the overrun check is kept exact — by
   returning an empty count, which [completed_count] refuses. Returns the
   count bytes and the linked constants. *)
let max_frame = 1 lsl 30

let read_exact fd n =
  let buf = Bytes.create n in
  let rec go off =
    if off = n then `Full (Bytes.unsafe_to_string buf)
    else match Unix.read fd buf off (n - off) with
      | 0 -> if off = 0 then `Eof else `Short
      | k -> go (off + k)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error _ -> `Short
  in
  go 0

let rec at_eof fd =
  match Unix.read fd (Bytes.create 1) 0 1 with
  | 0 -> true
  | _ -> false
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> at_eof fd
  | exception Unix.Unix_error _ -> false

let read_frame fd =
  match read_exact fd 8 with
  | `Eof -> Some []                (* no frame: no linked constants *)
  | `Short -> None
  | `Full lenb ->
    let len = Int64.to_int (String.get_int64_be lenb 0) in
    if len < 0 || len > max_frame then None
    else match read_exact fd len with
      | `Eof | `Short -> None
      | `Full blob ->
        if not (at_eof fd) then None
        else (try Some (Marshal.from_string blob 0 : Constant.t list)
              with _ -> None)

let read_report fd =
  let parsed =
    match read_exact fd report_size with
    | `Eof | `Short -> None
    | `Full count ->
      match read_frame fd with
      | None -> None
      | Some linked -> Some (count, linked)
  in
  close_report fd;
  match parsed with Some r -> r | None -> ("", [])

(* The only way for a batch to be known to be correct, or partly so, is
   a normal exit with code 0 and a report of exactly the right form,
   saying that between 1 and [size] checks were completed. *)
let completed_count ~size status report =
  match status with
  | Unix.WEXITED 0 when String.length report = report_size ->
    let k = String.get_int64_be report 0 in
    if Int64.compare k 1L >= 0 && Int64.compare k (Int64.of_int size) <= 0
    then Some (Int64.to_int k)
    else None
  | _ -> None

(* Put [tasks] back at the front of the queue, in order. *)
let push_front tasks =
  let front = Queue.create () in
  Array.iter (fun t -> Queue.push t front) tasks;
  Queue.transfer queue front;
  Queue.transfer front queue

(* The environment the main process links reported constants in. The
   checker sets it to the environment it is checking in, which grows
   monotonically, so the latest one holds every constant any reaped
   worker could have linked. *)
let link_env : Environ.env option ref = ref None
let set_link_env env = link_env := Some env

(* Link, in the main process, the VM globals the worker reported, so that
   a later fork inherits them instead of linking them again. This fills
   caches only: it computes the same values and never changes a verdict,
   so a name that cannot be linked is skipped — merely not shared. *)
let relink linked =
  match !link_env with
  | None -> ()
  | Some env ->
    let sigma = Genlambda.empty_evars env in
    List.iter
      (fun kn ->
        try ignore (Vmsymtable.val_of_constr env sigma (Constr.UnsafeMonomorphic.mkConst kn))
        with e ->
          debug (fun () ->
              str "could not pre-link " ++ Constant.print kn ++ str ": " ++
              str (Printexc.to_string e)))
      linked

(* A batch is known to be correct only for the checks its worker reported
   as completed. The others are queued again: each check runs once, in the
   worker or later, and its result counts only if the process that ran it
   ended successfully. The constants it linked are linked here too, before
   the next deal, so later forks inherit them. Reading the report drains
   the pipe, then the exited worker is waited for. *)
let reap_worker w =
  running := List.filter (fun w' -> w'.pid <> w.pid) !running;
  let count, linked = read_report w.report in
  let _, status = waitpid_non_intr [] w.pid in
  match completed_count ~size:w.batch.size status count with
  | None ->
    abort ();
    raise (WorkerFailed (w.pid, status, w.batch))
  | Some k ->
    relink linked;
    if k = w.batch.size then
      debug (fun () -> str "worker " ++ int w.pid ++ str " succeeded")
    else begin
      incr early_stops;
      debug (fun () ->
          str "worker " ++ int w.pid ++ str " stopped early after " ++ int k ++
          str " of " ++ int w.batch.size ++ str ", queueing the rest again");
      push_front (Array.sub w.tasks k (w.batch.size - k))
    end

(* A worker's report pipe becomes readable when it has finished checking
   and is reporting, or has closed it by exiting. Reaping is driven by
   that, not by [waitpid], so the main process drains a worker's pipe as
   it writes and a large frame never blocks it. *)
let ready_workers ~block =
  match !running with
  | [] -> []
  | ws ->
    let fds = List.map (fun w -> w.report) ws in
    let timeout = if block then -1.0 else 0.0 in
    let readable =
      try let r, _, _ = Unix.select fds [] [] timeout in r
      with Unix.Unix_error (Unix.EINTR, _, _) -> []
    in
    List.filter_map
      (fun fd -> List.find_opt (fun w -> w.report = fd) !running) readable

let rec reap_finished () =
  match ready_workers ~block:false with
  | [] -> ()
  | ws -> List.iter reap_worker ws; reap_finished ()

let free_slots slots = slots - List.length !running

(* Deal [k] batches of at most [size] checks from the front of the
   queue. When it holds [s >= k] batches of [size], batch [j] takes the
   checks at positions [j], [j + s], [j + 2s]... of the first [s * size].
   The checks not taken stay at the front, in order. *)
let deal ?(newest_first = false) k size =
  let n = Queue.length queue in
  let lanes = max k (n / size) in
  let batches = Array.make k [] in
  let rest = Queue.create () in
  for i = 0 to min n ((size - 1) * lanes + k) - 1 do
    let task = Queue.pop queue in
    let j = i mod lanes in
    if j < k then batches.(j) <- task :: batches.(j) else Queue.push task rest
  done;
  Queue.transfer queue rest;
  Queue.transfer rest queue;
  Array.iter (fun l ->
      if not (CList.is_empty l) then spawn (Array.of_list (if newest_first then l else List.rev l)))
    batches

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
      let k = min (free_slots !max_workers) (n / size) in
      (* While the libraries are checked, a worker checks its batch
         newest first: costly proofs come late in a library, so one
         deferred last no longer waits for the rest of its batch and is
         not the one given back when the worker's budget runs out. *)
      if k > 0 then deal ~newest_first:true k size
    end
  end

let finish () =
  if !max_workers > 0 then begin
    (* The main process checks nothing from now on, so one more worker
       can run. *)
    let slots = !max_workers + 1 in
    (* A worker that stops early queues checks again, so the queue is
       only known to be empty when no worker is left. *)
    while not (Queue.is_empty queue) || not (CList.is_empty !running) do
      reap_finished ();
      if free_slots slots > 0 && not (Queue.is_empty queue) then
        deal 1 ((Queue.length queue + 2 * slots - 1) / (2 * slots))
      else if not (CList.is_empty !running) then
        List.iter reap_worker (ready_workers ~block:true)
    done;
    debug (fun () ->
        str "done: " ++ int !forks ++ str " workers forked, " ++
        int !early_stops ++ str " stopped early")
  end
