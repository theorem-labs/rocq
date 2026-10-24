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
   check: the checks it released on request, or those it did not reach
   before its time budget ran out. [report] is the read end of the pipe on
   which the worker says how many checks it will complete, and then how
   many it completed. [buf] holds the bytes read from that pipe that are
   not a whole message yet. [asked] says that a release has been
   requested, which happens at most once per worker, and [released] the
   number of checks the worker answered that it will complete. *)
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
  mutable asked : bool;
  mutable released : int option;
  mutable buf : string;
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

(* Statistics, for the debug output. [checks_done] counts the checks that
   a process ended successfully after running, and [deferred] the checks
   handed to [defer]: with [-j] they are equal at the end, because every
   check runs exactly once. *)
let forks = ref 0
let early_stops = ref 0
let releases = ref 0
let checks_done = ref 0
let deferred = ref 0

(* Wall time since the first worker was forked, for the debug output. *)
let start_time = ref 0.
let elapsed () = if !start_time = 0. then 0. else Unix.gettimeofday () -. !start_time

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

(* What a worker tells the main process at the end: the number of checks
   it completed, the first ones of its batch in order, as 8 bytes (big
   endian). The only other message on that pipe is the release message
   below, which comes before it. *)
let report_size = 8

let default_report_writer fd completed =
  let b = Bytes.create report_size in
  Bytes.set_int64_be b 0 (Int64.of_int completed);
  if Unix.write fd b 0 report_size <> report_size then failwith "short write"

let report_writer = ref default_report_writer
let set_report_writer f = report_writer := f

(** Release on request.

    Once the libraries are walked ([finish]), when the main process has a
    free worker slot and an empty queue, it asks a running worker to give
    back the checks it has not started, so that they are dealt at once
    rather than waiting behind a long check.

    The request is SIGUSR1. In a worker the handler writes one release
    message and lets the loop stop after the check in progress. Outside a
    worker it only records the request: in OCaml 4.14 a signal is handled
    at the next safe point, which in a child can fall after [Unix.fork]
    returns but before the child marks itself a worker. *)
let release_signal = Sys.sigusr1
let release_tag = 'R'

(* A release message is [report_size] bytes: [release_tag], then the
   number of checks the worker will complete, in the low seven. The first
   byte of a final report is 0 for any count below 2^56, so one byte tells
   the two apart. *)
let write_release_message fd k =
  let b = Bytes.create report_size in
  Bytes.set_int64_be b 0 (Int64.of_int k);
  Bytes.set b 0 release_tag;
  if Unix.write fd b 0 report_size <> report_size then failwith "short write"

(* The worker's state. [started] is the number of checks it has begun and
   [completed] the number it has finished. Once a release is asked for,
   [release_at] is the number the worker will complete, and
   [release_written] says that its one release message has been written.
   Only a worker uses these; in the main process [pending_request] is set
   by a handler that ran outside a worker, and nothing acts on it. *)
let in_worker = ref false
let pending_request = ref false
let started = ref 0
let completed = ref 0
let release_at = ref 0
let release_written = ref false
let release_failed = ref false
let release_fd = ref Unix.stdout

(* Writes the one release message, for the handler and for [run_worker]'s
   entry alike. A worker always completes at least one check, as the
   budget stop does, so a request that arrives before the first check
   cannot give a whole batch back and make the main process fork again for
   nothing. *)
let write_release () =
  if not !release_written then begin
    release_written := true;
    release_at := max !started 1;
    try write_release_message !release_fd !release_at
    with _ -> release_failed := true
  end

(* Must never raise: an exception here would leave the VM through its
   signal poll (kernel/byterun/rocq_interp.c) and be reported as a failed
   proof. A failed write makes the worker exit non-zero instead, after the
   check it is in. *)
let release_handler (_ : int) =
  try if !in_worker then write_release () else pending_request := true
  with _ -> release_failed := true

let handler_installed = ref false

(* In the main process, before any fork: the default action of SIGUSR1 is
   to terminate the process, so a child must inherit the handler. *)
let install_release_handler () =
  if not !handler_installed then begin
    handler_installed := true;
    try Sys.set_signal release_signal (Sys.Signal_handle release_handler)
    with Invalid_argument _ | Sys_error _ -> ()
  end

(* Test only. ROCQCHK_WORKER_RELEASE_AT=point[:index] sends the request at
   one point, so that each race window can be opened on purpose, with no
   timing. In a worker: "fork" (in the child, before it marks itself a
   worker), "entry" (after that, before the first check), "started"
   (between [started := i + 1] and the release test), "check" (after that
   test, before check [i] runs), "between" (after check [i]), and "report"
   (after the loop, before the final report). [index] is the check [i] of
   "started", "check" and "between", 0 by default; the other points occur
   once, and ignore it. "main" sends the request to the main process
   itself, just after it forks its first worker: the main process must
   drop it, so that no worker forked later releases without being
   asked. *)
let release_test_point = ref None
let release_test_index = ref 0

(* Read before each fork, in the main process and so in the child, so
   that a test can set the variable between runs of one process. *)
let read_release_test () =
  match Sys.getenv_opt "ROCQCHK_WORKER_RELEASE_AT" with
  | None | Some "" -> release_test_point := None
  | Some v ->
    match String.index_opt v ':' with
    | None -> release_test_point := Some v; release_test_index := 0
    | Some i ->
      release_test_point := Some (String.sub v 0 i);
      release_test_index :=
        (match int_of_string_opt (String.sub v (i + 1) (String.length v - i - 1)) with
         | Some n -> n
         | None -> 0)

let release_test_at point i =
  match !release_test_point with
  | None -> ()
  | Some p ->
    let indexed = List.mem point ["started"; "check"; "between"] in
    if String.equal p point && (not indexed || Int.equal i !release_test_index) then begin
      (* [Unix.kill] runs the pending handler before it returns, so the
         request is handled exactly here. The sleep leaves the main
         process time to read a release message while the worker still
         runs. *)
      (try Unix.kill (Unix.getpid ()) release_signal with Unix.Unix_error _ -> ());
      (try Unix.sleepf 0.05 with Unix.Unix_error _ -> ())
    end

(* Runs in the child, never returns.

   The batch is checked in order. The time a worker lives is what makes
   its private memory grow: the garbage collector keeps touching the heap
   it shares copy-on-write with the main process. So once the budget has
   passed, the worker stops after the check it is in, reports how many it
   completed, and exits; the main process re-queues the rest. A release
   request stops it the same way, at the number of checks its release
   message named. At least one check is completed first, in both cases, so
   that the checking always progresses. *)
let run_worker parent report (tasks : task array) =
  let size = Array.length tasks in
  let current = ref (fst tasks.(0)) in
  release_fd := report;
  started := 0;
  completed := 0;
  release_at := 0;
  release_written := false;
  release_failed := false;
  release_test_at "fork" 0;
  (* A handler that runs from here on writes the release message itself;
     one that ran before left [pending_request]. Both go through
     [write_release], so the worker writes at most one message. *)
  in_worker := true;
  if !pending_request then write_release ();
  release_test_at "entry" 0;
  (* Only reaching the end of the batch, or a stop that is reported, may
     count as success. *)
  at_exit (fun () -> Unix._exit 2);
  let deadline = Unix.gettimeofday () +. !budget in
  let code =
    try
      tune_gc ();
      let stop = ref false in
      while not !stop && not !release_failed && !completed < size
            && (!completed = 0 || Unix.gettimeofday () < deadline) do
        let i = !completed in
        started := i + 1;
        release_test_at "started" i;
        if !release_written && !release_at <= i then begin
          (* Check [i] is not begun, so another process will run it. *)
          started := i;
          stop := true
        end else begin
          let kn, check = tasks.(i) in
          (* Nobody is waiting for the result any more. *)
          if Unix.getppid () <> parent then Unix._exit 1;
          current := kn;
          release_test_at "check" i;
          check ();
          incr completed;
          release_test_at "between" i
        end
      done;
      0
    with e ->
      (try !error_printer (CheckError (!current, e)) with _ -> ());
      CErrors.exit_code e
  in
  release_test_at "report" 0;
  (* No release message may follow the final report, and no write of that
     report may be interrupted: OCaml 4.14 installs handlers without
     SA_RESTART, and its runtime runs no handler for a blocked signal,
     including one it has already recorded. *)
  (try ignore (Unix.sigprocmask Unix.SIG_BLOCK [release_signal]) with _ -> ());
  let code =
    if code <> 0 then code
    else if !release_failed then 4
    else (try !report_writer report !completed; 0 with _ -> 3)
  in
  (try flush_output () with _ -> ());
  (* Not [exit]: the at_exit functions of the main process must not run
     here. So the worker prints its own VM counters, if they are on. *)
  (try Vmbinnum.print_stats () with _ -> ());
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
  (* Before any fork, so that a child cannot be killed by the default
     action of the request signal. *)
  install_release_handler ();
  if !start_time = 0. then start_time := Unix.gettimeofday ();
  read_release_test ();
  let parent = Unix.getpid () in
  let check_here_instead err =
    debug (fun () ->
        str "cannot fork (" ++ str err ++
        str "), checking here " ++ pr_batch batch);
    Array.iter (fun t -> check_here t; incr checks_done) tasks
  in
  match Unix.pipe ~cloexec:true () with
  | exception Unix.Unix_error (err, _, _) -> check_here_instead (Unix.error_message err)
  | report, report_out ->
    (* The main process never acts on a request; it sends them. A handler
       that ran here, for a signal from outside, set this flag, which the
       child would inherit and act on at entry, so it is dropped before the
       fork. A signal that the runtime has recorded but not yet handled is
       copied by the fork too, and is not dropped: then one child releases
       at entry, which is harmless, since the main process accepts any
       release whose count the final report matches. *)
    pending_request := false;
    match Unix.fork () with
    | 0 ->
      Unix.close report;
      List.iter (fun w -> try Unix.close w.report with Unix.Unix_error _ -> ()) !running;
      (* The worker counts only what it runs itself. *)
      Vmbinnum.reset_stats ();
      run_worker parent report_out tasks
    | pid ->
      Unix.close report_out;
      incr forks;
      debug (fun () -> str "worker " ++ int pid ++ str ": " ++ pr_batch batch);
      running := { pid; batch; tasks; report; asked = false; released = None; buf = "" } :: !running;
      if !forks = 1 then release_test_at "main" 0
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

(* The messages a worker writes: at most one release message, then its
   final report. Each is one [write] of [report_size] bytes, far below
   PIPE_BUF, so it arrives whole. The main process keeps what it has read
   of each pipe in [w.buf] and parses it at message boundaries. *)
let release_count s =
  if Char.equal (String.get s 0) release_tag then begin
    let b = Bytes.of_string s in
    Bytes.set b 0 '\000';
    Some (Int64.to_int (Bytes.get_int64_be b 0))
  end
  else None

(* Reads what the worker has written, without blocking: the caller has
   seen the pipe readable, or is reaping the worker, whose end of the pipe
   is then closed. False at the end of the pipe, or on an error, which the
   missing final report turns into a failure. *)
let read_some w =
  let b = Bytes.create 256 in
  match Unix.read w.report b 0 (Bytes.length b) with
  | 0 -> false
  | n -> w.buf <- w.buf ^ Bytes.sub_string b 0 n; true
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> true
  | exception Unix.Unix_error _ -> false

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

(* A release message says how many checks the worker will complete. The
   rest of its batch is queued again at once, at the front, so that the
   first of them head the next batches. A second release message, or a
   count outside 1 to [size], is not something a worker writes: the check
   is aborted, as for any other malformed report. *)
let release_received w k =
  if w.released <> None || k < 1 || k > w.batch.size then begin
    abort ();
    raise (WorkerFailed (w.pid, Unix.WEXITED 0, w.batch))
  end;
  w.released <- Some k;
  (* A worker past its last check releases nothing; that is not counted. *)
  if k < w.batch.size then incr releases;
  debug (fun () ->
      str "worker " ++ int w.pid ++ str " releases " ++
      int (w.batch.size - k) ++ str " of " ++ int w.batch.size ++
      str " after " ++ int k ++ str ", queued again at " ++
      str (Printf.sprintf "%.1f s" (elapsed ())));
  push_front (Array.sub w.tasks k (w.batch.size - k))

(* Takes the release messages at the front of what was read. What is left
   is the final report, once the worker has written it. *)
let rec take_releases w =
  if String.length w.buf >= report_size then
    match release_count (String.sub w.buf 0 report_size) with
    | None -> ()
    | Some k ->
      w.buf <- String.sub w.buf report_size (String.length w.buf - report_size);
      release_received w k;
      take_releases w

(* A batch is known to be correct only for the checks its worker reported
   as completed. The others are queued again: each check runs once, in the
   worker or later, and its result counts only if the process that ran it
   ended successfully. A worker that released a tail must complete exactly
   the number of checks its release message named. *)
let reaped pid status =
  match List.find_opt (fun w -> w.pid = pid) !running with
  | None -> ()
  | Some w ->
    running := List.filter (fun w' -> w'.pid <> pid) !running;
    let rec drain () = if read_some w then drain () in
    drain ();
    close_report w.report;
    take_releases w;
    match completed_count ~size:w.batch.size status w.buf with
    | None ->
      abort ();
      raise (WorkerFailed (pid, status, w.batch))
    | Some k ->
      checks_done := !checks_done + k;
      match w.released with
      | Some r ->
        if not (Int.equal r k) then begin
          abort ();
          raise (WorkerFailed (pid, status, w.batch))
        end;
        debug (fun () ->
            str "worker " ++ int pid ++ str " completed the " ++ int k ++
            str " checks it kept")
      | None ->
        if Int.equal k w.batch.size then
          debug (fun () -> str "worker " ++ int pid ++ str " succeeded")
        else begin
          incr early_stops;
          debug (fun () ->
              str "worker " ++ int pid ++ str " stopped early after " ++ int k ++
              str " of " ++ int w.batch.size ++ str ", queueing the rest again");
          push_front (Array.sub w.tasks k (w.batch.size - k))
        end

let rec reap_finished () =
  if not (CList.is_empty !running) then
    match waitpid_non_intr [Unix.WNOHANG] (-1) with
    | 0, _ -> ()
    | pid, status -> reaped pid status; reap_finished ()

let free_slots slots = slots - List.length !running

(* Asks the worker with the largest batch to release the checks it has not
   started, while a slot is free and nothing is queued: then the released
   checks are dealt at once, instead of waiting behind a long check in a
   batch that a busy worker holds.

   A worker is asked at most once, and only if its batch has two or more
   checks, because it always completes its first one. Only a worker that
   has not been reaped is signalled, so the pid cannot have been reused;
   an error from [kill] is ignored, since a worker that has just exited
   needs no request. *)
let request_release slots =
  if free_slots slots > 0 && Queue.is_empty queue then begin
    let best =
      List.fold_left (fun best w ->
          if w.asked || w.batch.size < 2 then best
          else match best with
            | Some b when b.batch.size >= w.batch.size -> best
            | Some _ | None -> Some w)
        None !running
    in
    match best with
    | None -> ()
    | Some w ->
      w.asked <- true;
      debug (fun () ->
          str "asking worker " ++ int w.pid ++ str " to release what is left of its " ++
          int w.batch.size ++ str " checks at " ++
          str (Printf.sprintf "%.1f s" (elapsed ())));
      (try Unix.kill w.pid release_signal with Unix.Unix_error _ -> ())
  end

(* Waits until a worker writes to its pipe or closes it, or [timeout]
   passes, and takes the release messages that arrived. Retries on EINTR:
   the main process has a handler for the request signal, which OCaml 4.14
   installs without SA_RESTART, so a signal from outside interrupts
   [select]. *)
let rec wait_for_messages timeout =
  let fds = List.map (fun w -> w.report) !running in
  if not (CList.is_empty fds) then
    match Unix.select fds [] [] timeout with
    | ready, _, _ ->
      List.iter (fun fd ->
          match List.find_opt (fun w -> w.report = fd) !running with
          | None -> ()
          | Some w -> if read_some w then take_releases w)
        ready
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> wait_for_messages timeout
    | exception Unix.Unix_error _ ->
      (* Not expected (an fd above FD_SETSIZE, or EBADF). The caller reaps
         and parses as usual, so the result is still right; this only keeps
         [finish] from spinning until the workers exit. *)
      (try Unix.sleepf timeout with Unix.Unix_error _ -> ())

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
  incr deferred;
  if !max_workers = 0 then begin check (); incr checks_done end
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
      (* No release is requested here: a request needs an empty queue,
         which the walk rarely leaves, and the walk reads a release message
         only when it reaps its worker, and deals only batches of at least
         [min_batch]; so a released tail would wait here anyway. [finish]
         asks, reads and deals at once. *)
    end
  end

let finish () =
  if !max_workers > 0 then begin
    (* The main process checks nothing from now on, so one more worker
       can run. *)
    let slots = !max_workers + 1 in
    (* A worker that stops early, or releases a tail, queues checks again,
       so the queue is only known to be empty when no worker is left. *)
    while not (Queue.is_empty queue) || not (CList.is_empty !running) do
      reap_finished ();
      if free_slots slots > 0 && not (Queue.is_empty queue) then
        deal 1 ((Queue.length queue + 2 * slots - 1) / (2 * slots))
      else if not (CList.is_empty !running) then begin
        request_release slots;
        (* A release message is read as soon as it is written, not only
           when its worker exits. *)
        wait_for_messages 0.05;
        reap_finished ()
      end
    done;
    debug (fun () ->
        str "done: " ++ int !forks ++ str " workers forked, " ++
        int !early_stops ++ str " stopped early, " ++
        int !releases ++ str " released a tail, " ++
        int !checks_done ++ str " checks run of " ++ int !deferred ++ str " deferred")
  end
