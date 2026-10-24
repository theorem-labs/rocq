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

let jobs () = !max_workers + 1

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
   time.

   Proofs whose body holds a VM or native cast are the exception: one of
   them can take a minute (its conversion may compile a whole closure of
   definitions), and a batch that ends with one holds its worker for that
   long, whatever its other checks are. So such a proof is dealt to a
   worker of its own, ahead of the other proofs: in [finish], and in each
   dispatch while the libraries are checked, where it is dealt to any free
   slot even though it is below [min_batch]. And costly casts come from
   the same library, deferred in a row, so the compilation units take
   turns: one proof of each unit in turn, in the order their first such
   proof was deferred. One library's casts cannot take every slot while
   another's wait. *)
let window = 1.0

(* Below this, a batch is not worth a fork while the libraries are
   being checked. It does not hold back a proof with a VM cast. *)
let min_batch = 50

(* Deferred checks not yet given to a worker, oldest first, except those
   whose body holds a VM cast. *)
let queue : task Queue.t = Queue.create ()
let last_dispatch = ref 0.

(* Deferred checks whose body holds a VM cast, by compilation unit (the
   library of the constant: [ModPath.dp] of its module path, so the
   submodules of a library are one unit), each unit's oldest first. A
   unit is in [vm_lanes] while it has such a check left; the next check
   dealt comes from the unit at the front, which then goes to the back. *)
let vm_lanes : (DirPath.t * task Queue.t) Queue.t = Queue.create ()
let vm_queued = ref 0

let push_vm_cast ((kn, _) as task) =
  let dp = ModPath.dp (Constant.modpath kn) in
  let lane =
    Queue.fold (fun found (d, q) ->
        match found with
        | Some _ -> found
        | None -> if DirPath.equal d dp then Some q else None)
      None vm_lanes
  in
  let () = match lane with
    | Some q -> Queue.push task q
    | None ->
      let q = Queue.create () in
      Queue.push task q;
      Queue.push (dp, q) vm_lanes
  in
  incr vm_queued

let pop_vm_cast () =
  let (dp, q) = Queue.pop vm_lanes in
  let task = Queue.pop q in
  if not (Queue.is_empty q) then Queue.push (dp, q) vm_lanes;
  decr vm_queued;
  task

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

(* What a worker tells the main process: the number of checks it
   completed, the first ones of its batch in order, as 8 bytes (big
   endian). Nothing else is ever written to the pipe. *)
let report_size = 8

let default_report_writer fd completed =
  let b = Bytes.create report_size in
  Bytes.set_int64_be b 0 (Int64.of_int completed);
  if Unix.write fd b 0 report_size <> report_size then failwith "short write"

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
  (* r3-b instrumentation *)
  ConvLog.event "worker-start" [string_of_int parent; string_of_int size];
  let code =
    try
      tune_gc ();
      while !completed < size
            && (!completed = 0 || Unix.gettimeofday () < deadline) do
        let kn, check = tasks.(!completed) in
        (* Nobody is waiting for the result any more. *)
        if Unix.getppid () <> parent then Unix._exit 1;
        current := kn;
        (* r3-b instrumentation *)
        ConvLog.event "check-start" [Constant.to_string kn];
        check ();
        (* r3-b instrumentation *)
        ConvLog.event "check-end" [Constant.to_string kn];
        incr completed
      done;
      0
    with e ->
      (* r3-b instrumentation *)
      ConvLog.event "check-error" [Constant.to_string !current];
      (try !error_printer (CheckError (!current, e)) with _ -> ());
      CErrors.exit_code e
  in
  let code =
    if code <> 0 then code
    else (try !report_writer report !completed; 0 with _ -> 3)
  in
  (* r3-b instrumentation *)
  ConvLog.event "worker-end" [string_of_int !completed; string_of_int size; string_of_int code];
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
  let check_here_instead err =
    debug (fun () ->
        str "cannot fork (" ++ str err ++
        str "), checking here " ++ pr_batch batch);
    (* r3-b instrumentation *)
    ConvLog.event "check-here" [string_of_int (Array.length tasks); err];
    Array.iter check_here tasks
  in
  (* r3-b instrumentation *)
  let t_fork = Unix.gettimeofday () in
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
      running := { pid; batch; tasks; report } :: !running;
      (* r3-b instrumentation *)
      if ConvLog.enabled () then
        ConvLog.event "fork"
          [string_of_int pid; string_of_int (Array.length tasks);
           Printf.sprintf "fork_s=%.6f" (Unix.gettimeofday () -. t_fork);
           String.concat "," (Array.to_list (Array.map (fun (kn, _) -> Constant.to_string kn) tasks))]
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
  Queue.clear vm_lanes;
  vm_queued := 0;
  List.iter (fun w ->
      try Unix.kill w.pid Sys.sigkill with Unix.Unix_error _ -> ())
    workers;
  List.iter (fun w ->
      (try ignore (waitpid_non_intr [] w.pid) with Unix.Unix_error _ -> ());
      close_report w.report)
    workers

(* What the worker wrote, at most one byte more than a report. *)
let read_report fd =
  let buf = Bytes.create (report_size + 1) in
  let rec go off =
    if off = Bytes.length buf then off
    else match Unix.read fd buf off (Bytes.length buf - off) with
      | 0 -> off
      | n -> go (off + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error _ -> -1
  in
  let n = go 0 in
  close_report fd;
  if n < 0 then "" else Bytes.sub_string buf 0 n

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

(* A batch is known to be correct only for the checks its worker
   reported as completed. The others are queued again: each check runs
   once, in the worker or later, and its result counts only if the
   process that ran it ended successfully. *)
let reaped pid status =
  match List.find_opt (fun w -> w.pid = pid) !running with
  | None -> ()
  | Some w ->
    running := List.filter (fun w' -> w'.pid <> pid) !running;
    let report = read_report w.report in
    let completed = completed_count ~size:w.batch.size status report in
    (* r3-b instrumentation *)
    ConvLog.event "reaped"
      [string_of_int pid;
       (match status with
        | Unix.WEXITED n -> "exit " ^ string_of_int n
        | Unix.WSIGNALED s -> "signal " ^ string_of_int s
        | Unix.WSTOPPED s -> "stopped " ^ string_of_int s);
       (match completed with Some k -> string_of_int k | None -> "-");
       string_of_int w.batch.size; string_of_int (List.length !running)];
    match completed with
    | None ->
      abort ();
      raise (WorkerFailed (pid, status, w.batch))
    | Some k when k = w.batch.size ->
      debug (fun () -> str "worker " ++ int pid ++ str " succeeded")
    | Some k ->
      incr early_stops;
      debug (fun () ->
          str "worker " ++ int pid ++ str " stopped early after " ++ int k ++
          str " of " ++ int w.batch.size ++ str ", queueing the rest again");
      push_front (Array.sub w.tasks k (w.batch.size - k))

let rec reap_finished () =
  if not (CList.is_empty !running) then
    match waitpid_non_intr [Unix.WNOHANG] (-1) with
    | 0, _ -> ()
    | pid, status -> reaped pid status; reap_finished ()

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

(* Deal the checks whose body holds a VM cast, one per worker, to the
   free slots among [slots], the compilation units taking turns. *)
let deal_vm_casts slots =
  while !vm_queued > 0 && free_slots slots > 0 do
    spawn [| pop_vm_cast () |]
  done

let defer ~vm_cast kn check =
  if !max_workers = 0 then check ()
  else begin
    if vm_cast then push_vm_cast (kn, check) else Queue.push (kn, check) queue;
    (* r3-b instrumentation *)
    ConvLog.event "defer"
      [Constant.to_string kn; string_of_int (Queue.length queue); string_of_int (List.length !running);
       (if vm_cast then "vm_cast" else "-"); string_of_int !vm_queued];
    let now = Unix.gettimeofday () in
    if now -. !last_dispatch >= window then begin
      last_dispatch := now;
      reap_finished ();
      (* r3-b instrumentation *)
      let vm_before = !vm_queued in
      deal_vm_casts !max_workers;
      let n = Queue.length queue in
      let size = max min_batch ((n + !max_workers) / (!max_workers + 1)) in
      let k = min (free_slots !max_workers) (n / size) in
      (* r3-b instrumentation *)
      ConvLog.event "dispatch-window"
        [string_of_int n; string_of_int size; string_of_int k; string_of_int (List.length !running);
         Printf.sprintf "vm_dealt=%d" (vm_before - !vm_queued); string_of_int !vm_queued];
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
    (* r3-b instrumentation *)
    ConvLog.event "finish-start"
      [string_of_int (Queue.length queue); string_of_int (List.length !running); string_of_int slots];
    (* A worker that stops early queues checks again, so the queue is
       only known to be empty when no worker is left. A check with a VM
       cast is dealt alone, so its worker never stops early. *)
    while not (Queue.is_empty queue) || !vm_queued > 0 || not (CList.is_empty !running) do
      reap_finished ();
      if free_slots slots > 0 && !vm_queued > 0 then begin
        (* r3-b instrumentation *)
        ConvLog.event "finish-deal-vm"
          [string_of_int !vm_queued; string_of_int (List.length !running)];
        spawn [| pop_vm_cast () |]
      end
      else if free_slots slots > 0 && not (Queue.is_empty queue) then begin
        let size = (Queue.length queue + 2 * slots - 1) / (2 * slots) in
        (* r3-b instrumentation *)
        ConvLog.event "finish-deal"
          [string_of_int (Queue.length queue); string_of_int size; string_of_int (List.length !running)];
        deal 1 size
      end
      else if not (CList.is_empty !running) then begin
        (* r3-b instrumentation *)
        ConvLog.event "finish-wait"
          [string_of_int (Queue.length queue); string_of_int (List.length !running)];
        let pid, status = waitpid_non_intr [] (-1) in
        reaped pid status
      end
    done;
    (* r3-b instrumentation *)
    ConvLog.event "finish-end" [string_of_int !forks; string_of_int !early_stops];
    debug (fun () ->
        str "done: " ++ int !forks ++ str " workers forked, " ++
        int !early_stops ++ str " stopped early")
  end
