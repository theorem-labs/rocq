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

let debug_flag, debug = CDebug.create_full ~name:"checker-workers" ()

let debugging () = CDebug.get_flag debug_flag

(* What a process is given to do: check the body of one opaque constant,
   or read one library's table of opaque proofs. *)
type job =
| Proof of Constant.t
| Table of DirPath.t

(* A task, and the library whose walk deferred it. The jobs of one library
   are next to each other in the queue -- its table first, unless the
   worker of [validate_tables] reads the tables, then the checks of its
   opaque bodies -- and [group] numbers those runs, so that a batch can
   take them whole and parse each table once. *)
type task = {
  job : job;
  group : int;
  run : unit -> unit;
}

(* What the main process keeps about a running worker. The batch is for
   error messages. The tasks are kept to re-queue what the worker did not
   check: the checks it released on request, or those it did not reach
   before its time budget ran out (the worker of [validate_tables] has no
   budget and is never asked to release). [report] is the read end of the pipe on
   which the worker says how many checks it will complete, and then how
   many it completed. [buf] holds the bytes read from that pipe that are
   not a whole message yet. [asked] says that a release has been
   requested, which happens at most once per worker, and [released] the
   number of checks the worker answered that it will complete. [output]
   is the pair of files, standard output and standard error, that the
   worker writes to instead of the terminal (see [run_worker]), until the
   main process prints or drops them. *)
type batch = {
  size : int;
  first : job;
  last : job;
  proofs : int;
  first_proof : Constant.t option;
  last_proof : Constant.t option;
}

type worker = {
  pid : int;
  batch : batch;
  tasks : task array;
  report : Unix.file_descr;
  mutable output : (Unix.file_descr * Unix.file_descr) option;
  mutable asked : bool;
  mutable released : int option;
  mutable buf : string;
}

exception CheckError of job * exn
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

let parallel () = !max_workers > 0
let processes () = !max_workers + 1

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
   row; and every process that checks a library's opaque proofs parses
   that library's whole table first. So a batch is a stripe of the
   queue over whole libraries: a library's jobs, with the task that reads
   its table when there is one (see [validate_tables]), are cut into pieces of the size wanted, which a library of
   ordinary size fits in one piece, and when the queue holds [s] batches,
   a batch takes one piece in [s] (see [deal]). Libraries next to each
   other in the queue go to different batches, and a batch parses about
   one table per library it holds, where a stride of jobs had each table
   parsed by as many workers as its library has checks (about 28 on the
   whole r160 tree). A worker that stops early puts the jobs it did not
   do back at the front, in order, so they are dealt again first.

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
(* Test only. ROCQCHK_WORKER_WINDOW=seconds replaces the one-second window,
   so that a test whose libraries are read in less than a second still has
   workers dealt while they are being read. *)
let window = ref (
    match Option.bind (Sys.getenv_opt "ROCQCHK_WORKER_WINDOW") float_of_string_opt with
    | Some w when w >= 0. && Float.is_finite w -> w
    | _ -> 1.0)

(* Test only: the unit tests open each window themselves ([end_window]),
   so that what is dealt does not depend on how fast the test runs. *)
let set_window w = window := w

(* Below this, a batch is not worth a fork while the libraries are being
   checked. A fork copies the page tables of the main process, whose heap
   holds every library read so far, and the opaque tables it read itself
   (it used to read all of them): on the whole r160 tree, 0.23 s a fork
   at the end of the walk, and 1,797 forks with this at 50. Larger
   batches mean fewer forks but a longer tail, since release on request
   fires only in [finish]. Measured on that tree, with the opaque tables
   in the main process's heap (speed-r3, 2026-10-25, -j 16 -worker-budget
   20, one timed run each): 200 took 385.6 s (579 forks, tail 116 s), 400
   took 404.4 s (430 forks, tail 145 s), 800 took 399.5 s (452 forks,
   tail 164 s). Forks of a heap without the tables cost less, so this is
   to be measured again. *)
let min_batch = 200

(* Deferred jobs not yet given to a worker, oldest first. *)
let queue : task Queue.t = Queue.create ()
let last_dispatch = ref 0.

(* Test only: the next [defer] deals, as once a window has passed. *)
let end_window () = last_dispatch := neg_infinity

(* The library whose jobs are being deferred: [defer_table], which every
   library's walk calls before its own checks, opens the next group. *)
let current_group = ref 0

(* The expected cost of each library's checks, by library name, from
   [set_cost_hints]; and the cost of each group, the one of the library that
   opened it. A group with no cost costs 0. Costs only decide which queued
   jobs are dealt first, and in which order a worker runs them: costly
   libraries first, so that a long proof neither waits behind the queue nor
   is given back for the cheaper ones before it in its batch. *)
let cost_hints : (string, float) Hashtbl.t = Hashtbl.create 0
let group_costs : (int, float) Hashtbl.t = Hashtbl.create 0

let set_cost_hints hints = List.iter (fun (lib, c) -> Hashtbl.replace cost_hints lib c) hints

let group_cost g = Option.default 0. (Hashtbl.find_opt group_costs g)

(* [tasks] costliest group first; tasks of the same cost keep their order. *)
let by_cost tasks =
  if Int.equal (Hashtbl.length group_costs) 0 then tasks
  else List.stable_sort (fun t1 t2 -> Float.compare (group_cost t2.group) (group_cost t1.group)) tasks

(* Running workers. *)
let running : worker list ref = ref []

(* Statistics, for the debug output. [checks_done] counts the checks that
   a process ended successfully after running, and [deferred] the checks
   handed to [defer]: with [-j] they are equal at the end, because every
   check runs exactly once. [tables_done] and [tables_deferred] are the
   same for the tasks that read a library's table, and [table_reads] and
   [table_bytes] count what this process read and parsed itself.
   [main_cooks] counts the opaque bodies that the main process cooked
   itself, wherever in the code that happened ([note_cook], called from
   the cook): with [-j] they are the bodies of sealed modules, whose
   cooked form the main process needs, and those of checks it ran itself
   because it could not fork. *)
let forks = ref 0
let early_stops = ref 0
let releases = ref 0
let checks_done = ref 0
let deferred = ref 0
let tables_done = ref 0
let tables_deferred = ref 0
let table_reads = ref 0
let table_bytes = ref 0
let main_cooks = ref 0
let note_table_read ~bytes =
  incr table_reads;
  table_bytes := !table_bytes + bytes

(* The tables that a process which ended successfully read: a worker,
   once its report says it completed that task, or the main process; and,
   once a run has failed, the tables that the worker of [validate_tables]
   read without error before it stopped ([validator_progress]). *)
let tables_read = ref DirPath.Set.empty
let table_checked dp = DirPath.Set.mem dp !tables_read

(* What a process ran, by kind of job. *)
let note_one = function
  | Proof _ -> incr checks_done
  | Table dp -> incr tables_done; tables_read := DirPath.Set.add dp !tables_read

(* The first [k] tasks of a batch, which its worker ran. *)
let note_done tasks k =
  for i = 0 to k - 1 do note_one tasks.(i).job done

(* Wall time since the first worker was forked, for the debug output. *)
let start_time = ref 0.
let elapsed () = if !start_time = 0. then 0. else Unix.gettimeofday () -. !start_time

let flush_output () =
  Format.pp_print_flush Format.std_formatter ();
  Format.pp_print_flush Format.err_formatter ();
  flush_all ()

(* Output held while the walk runs ahead of the intern. Stock prints every
   line of the intern before any line of the walk; when the walk starts
   before the intern ends, what the walk prints, in the main process and
   replayed from its workers, waits here in order until the intern ends.
   The main process prints through [Format.err_formatter] (the feedback
   listener) and [Format.std_formatter] (a malformed object, [Validate]),
   and replays its workers through [print_output]: those are the paths
   held. *)
type held_chunk = Out of string | Err of string

let held : held_chunk Queue.t option ref = ref None

(* The two formatters' own output functions while [hold_on] has replaced
   them. *)
let saved = ref None

let start_holding () = held := Some (Queue.create ())

let hold_on () =
  match !held, !saved with
  | Some q, None ->
    Format.pp_print_flush Format.std_formatter ();
    Format.pp_print_flush Format.err_formatter ();
    saved := Some (Format.pp_get_formatter_output_functions Format.std_formatter (),
                   Format.pp_get_formatter_output_functions Format.err_formatter ());
    Format.pp_set_formatter_output_functions Format.std_formatter
      (fun s pos len -> Queue.push (Out (String.sub s pos len)) q) ignore;
    Format.pp_set_formatter_output_functions Format.err_formatter
      (fun s pos len -> Queue.push (Err (String.sub s pos len)) q) ignore
  | _ -> ()

let restore_formatters () =
  match !saved with
  | None -> ()
  | Some ((out, out_flush), (err, err_flush)) ->
    saved := None;
    Format.pp_set_formatter_output_functions Format.std_formatter out out_flush;
    Format.pp_set_formatter_output_functions Format.err_formatter err err_flush

let hold_off () =
  if Option.has_some !saved then begin
    Format.pp_print_flush Format.std_formatter ();
    Format.pp_print_flush Format.err_formatter ();
    restore_formatters ()
  end

let print_chunk = function
  | Out s -> print_string s; flush stdout
  | Err s -> output_string stderr s; flush stderr

let release_held () =
  hold_off ();
  match !held with
  | None -> ()
  | Some q ->
    held := None;
    flush_output ();
    Queue.iter print_chunk q

let drop_held () =
  hold_off ();
  held := None

(* A worker forked while output is held prints to its own files, as any
   other worker. *)
let reset_held_in_child () =
  restore_formatters ();
  held := None

let rec waitpid_non_intr flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_non_intr flags pid

(* A worker only reads the heap it inherits, but the GC writes to the
   headers of the objects it marks, and each page written to is copied.
   A larger minor heap promotes fewer objects, so there is less work for
   the major GC, and compaction, which would copy everything, is turned
   off. A space overhead of 1000, against the default 120, makes the major
   GC mark about an eighth as much per word allocated (and sweep about 0.6
   as much), at the cost of a heap that holds more garbage. Measured on
   r160 (2026-10-26, this code against the same tree without the line): at
   -j 16 under a 124 GB cap, five interleaved pairs, the workers' user and
   system time fell in every pair (medians 328 s and 97 s), the median wall
   by 6.7% (faster in 4 of 5 pairs), and the peak by 15%, probably because
   fewer inherited pages are written. At -j 5 and -j 8 the peak rises
   instead (r160 -j 5: +25%; r190 and r187 -j 8: +34% and +15%; and,
   comparing two release builds, speed-3 against speed-4 which contains
   this setting, on six trees at -j 8 under 44 GB the worst worker grows
   from 4.1-4.7 to 6.8-11.8 GB), and a cap that the default fits can then
   kill a worker, which fails the run (r160 -j 8 under 22 GB). Production
   runs -j 16 for a final grade (124 GB) and -j 5 or -j 8 for a mid-run
   check, whose memory cap sets its width, so the lazier GC is used only
   when [!max_workers], which is -j minus 1, is at least
   [lazy_gc_min_max_workers] (-j 10 and wider): narrower runs keep the
   default space overhead, the setting their width was sized with; no
   width from -j 10 to -j 15 has been measured. In a wide run
   OCAMLRUNPARAM can raise the value but not lower it. The main process
   keeps its own setting: it is the one whose heap the workers inherit. *)
let lazy_gc_min_max_workers = 9

let tune_gc () =
  let gc = Gc.get () in
  let space_overhead =
    if !max_workers >= lazy_gc_min_max_workers then max gc.Gc.space_overhead 1000
    else gc.Gc.space_overhead in
  Gc.set { gc with
           Gc.minor_heap_size = max gc.Gc.minor_heap_size (4 * 1024 * 1024);
           space_overhead;
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

(* Set in the worker of [validate_tables], which never releases: other
   workers would run the tables it gives back and write to its progress
   file, which then would no longer say how far it got. *)
let never_release = ref false

(* Writes the one release message, for the handler and for [run_worker]'s
   entry alike. A worker always completes at least one check, as the
   budget stop does, so a request that arrives before the first check
   cannot give a whole batch back and make the main process fork again for
   nothing. *)
let write_release () =
  if not !release_written && not !never_release then begin
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

(* Counts an opaque body that is cooked outside a worker, so by the main
   process. The caller is the cook itself, so the count is where the cook
   ran, not which branch of the code called it. *)
let note_cook () = if not !in_worker then incr main_cooks

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
   that the checking always progresses.

   What a worker prints goes to [output], a pair of files for its
   standard output and its standard error, and not to the terminal: the
   main process prints what a worker that ended successfully printed,
   and holds a failed worker's, which it prints only where stock reports
   that worker's error and not an earlier one (see
   [CheckLibrary.recheck_library]). The validation of a marshalled value
   prints to standard output before it raises, so the redirection is
   made before the first check, not when the error is caught. Without
   those files, which only a temporary directory that cannot be written
   to prevents, the worker prints where it always did. *)
let run_worker parent report output (tasks : task array) =
  let size = Array.length tasks in
  let current = ref tasks.(0).job in
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
  (match output with
   | Some (out, err) ->
     (try
        flush_output ();
        Unix.dup2 ~cloexec:false out Unix.stdout;
        Unix.dup2 ~cloexec:false err Unix.stderr
      with Unix.Unix_error _ -> ())
   | None -> ());
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
          let t = tasks.(i) in
          (* Nobody is waiting for the result any more. *)
          if Unix.getppid () <> parent then Unix._exit 1;
          current := t.job;
          release_test_at "check" i;
          t.run ();
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
  (try
     debug (fun () ->
         str "worker " ++ int (Unix.getpid ()) ++ str " parsed " ++
         int !table_reads ++ str " opaque " ++
         str (CString.plural !table_reads "table") ++ str ", " ++
         int !table_bytes ++ str " bytes read")
   with _ -> ());
  (try flush_output () with _ -> ());
  (* Not [exit]: the at_exit functions of the main process must not run
     here. So the worker prints its own VM counters, if they are on. *)
  (try Vmbinnum.print_stats () with _ -> ());
  Unix._exit code

let check_here t =
  try t.run ()
  with e ->
    let e, info = Exninfo.capture e in
    Exninfo.iraise (CheckError (t.job, e), info)

let batch_of_tasks tasks =
  let size = Array.length tasks in
  let proofs = Array.fold_right (fun t l ->
      match t.job with Proof c -> c :: l | Table _ -> l) tasks []
  in
  { size; first = tasks.(0).job; last = tasks.(size - 1).job;
    proofs = List.length proofs;
    first_proof = List.nth_opt proofs 0;
    last_proof = List.nth_opt (List.rev proofs) 0 }

let pr_job = function
  | Proof c -> Constant.print c
  | Table dp -> str "the opaque proofs of " ++ DirPath.print dp

let pr_doing = function
  | Proof c -> str "checking the opaque proof of" ++ spc () ++ Constant.print c
  | Table dp -> str "reading the opaque proofs of" ++ spc () ++ DirPath.print dp

(* Every job of a batch, for the debug output. *)
let pr_tasks b =
  str "a batch of " ++ int b.size ++ spc () ++
  str "(the first is " ++ pr_job b.first ++ str "," ++ spc () ++
  str "the last " ++ pr_job b.last ++ str ")"

(* Stock's words: the opaque proofs of the batch, the reads of tables left
   out. A batch has none only if it holds reads alone, and such a batch
   fails visibly only where reading the table again in the main process
   succeeds. *)
let pr_batch b =
  match b.first_proof, b.last_proof with
  | Some first, Some last ->
    int b.proofs ++ str " " ++ str (CString.plural b.proofs "opaque proof") ++ spc () ++
    str "(the first is " ++ Constant.print first ++ str "," ++ spc () ++
    str "the last " ++ Constant.print last ++ str ")"
  | _ -> pr_tasks b

(* An unnamed file for what a worker prints: created, opened, then
   removed. *)
let open_capture () =
  match Filename.temp_file "rocqchk" ".out" with
  | exception Sys_error _ -> None
  | name ->
    let fd =
      try Some (Unix.openfile name [Unix.O_RDWR; Unix.O_CLOEXEC] 0o600)
      with Unix.Unix_error _ -> None
    in
    (try Sys.remove name with Sys_error _ -> ());
    fd

let close_fd fd = try Unix.close fd with Unix.Unix_error _ -> ()

(* The two files a worker prints to, or neither of them. *)
let open_output () =
  match open_capture (), open_capture () with
  | Some out, Some err -> Some (out, err)
  | out, err -> Option.iter close_fd out; Option.iter close_fd err; None

(* Whether a worker can be given its two files now. *)
let capture_available () =
  match open_output () with
  | Some (out, err) -> close_fd out; close_fd err; true
  | None -> false

let close_output w =
  Option.iter (fun (out, err) -> close_fd out; close_fd err) w.output;
  w.output <- None

(* The descriptors [deal] has opened for batches it has not forked yet. *)
let prepared_fds : Unix.file_descr list ref = ref []

(* [prepared]: the report pipe and the two output files, already open
   ([deal], while output is held). *)
let spawn ?(releasable = true) ?prepared tasks =
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
        str "), checking here " ++ pr_tasks batch);
    Array.iter (fun t -> check_here t; note_one t.job) tasks
  in
  let pipe = match prepared with
    | Some (report, report_out, _) -> Ok (report, report_out)
    | None ->
      (try Ok (Unix.pipe ~cloexec:true ()) with Unix.Unix_error (err, _, _) -> Error err)
  in
  match pipe with
  | Error err -> check_here_instead (Unix.error_message err)
  | Ok (report, report_out) ->
    (* The main process never acts on a request; it sends them. A handler
       that ran here, for a signal from outside, set this flag, which the
       child would inherit and act on at entry, so it is dropped before the
       fork. A signal that the runtime has recorded but not yet handled is
       copied by the fork too, and is not dropped: then one child releases
       at entry, which is harmless, since the main process accepts any
       release whose count the final report matches. *)
    pending_request := false;
    let output = match prepared with
      | Some (_, _, output) -> Some output
      | None -> open_output ()
    in
    (* This worker's own descriptors are no longer another's to close. *)
    let mine = report :: report_out ::
               (match output with Some (out, err) -> [out; err] | None -> []) in
    prepared_fds := List.filter (fun fd -> not (List.mem fd mine)) !prepared_fds;
    match Unix.fork () with
    | 0 ->
      Unix.close report;
      List.iter (fun w ->
          close_fd w.report;
          Option.iter (fun (out, err) -> close_fd out; close_fd err) w.output)
        !running;
      (* Those [deal] opened for the batches it has not forked yet: a child
         holding the write end of another worker's report would keep that
         report from ever ending. *)
      List.iter close_fd !prepared_fds;
      (* The worker counts only what it runs and reads itself. *)
      Vmbinnum.reset_stats ();
      reset_held_in_child ();
      table_reads := 0;
      table_bytes := 0;
      run_worker parent report_out output tasks
    | pid ->
      Unix.close report_out;
      incr forks;
      debug (fun () -> str "worker " ++ int pid ++ str ": " ++ pr_tasks batch);
      running := { pid; batch; tasks; report; output;
                   asked = not releasable; released = None; buf = "" } :: !running;
      if !forks = 1 then release_test_at "main" 0
    | exception Unix.Unix_error (err, _, _) ->
      Unix.close report;
      Unix.close report_out;
      Option.iter (fun (out, e) -> close_fd out; close_fd e) output;
      check_here_instead (Unix.error_message err)

let close_report fd = try Unix.close fd with Unix.Unix_error _ -> ()

(* Running a function on items in forked processes, while the main process
   goes on with its own work ([Forked]).

   The main process hands the items out one at a time, in order, each to the
   first process that is free, on a pipe of that process's own: an item is 8
   bytes (big endian), and closing the pipe means there are no more. A process
   answers each item on a second pipe with 8 bytes, the length of what
   follows, then the item, its result and whether it stops, marshalled. A
   process prints nothing: its standard output and error are /dev/null, and it
   ends with [Unix._exit], so no [at_exit] function of the main process runs in
   it and nothing still buffered is written twice.

   A process inherits the whole heap of the main process, and every page it
   writes to is copied. Its GC is lazy ([forked_gc]): a major cycle would mark,
   and so copy, every inherited page that holds a live block. Its garbage is
   bounded instead: once its major heap has grown by more than the heap budget,
   it stops after the item it is on, and the main process forks a fresh process
   for the items that are left. So each process holds at most about the budget
   beyond what it shares.

   What a process does is optional: the caller computes whatever it does not
   answer. So no process may keep the main process waiting. The main process
   only looks at the processes when it asks to ([Forked.poll]), and then reads
   answers without waiting: their descriptors do not block, and the bytes of an
   answer are kept until it is whole. A process has a deadline for each item,
   counted from when it is given the item; a process whose answer is not whole
   when its deadline has passed is killed. A process that stops is waited for
   without blocking, and [Forked.stop] kills every process that is left before
   it waits for it, and a kill always lets the wait return.

   An answer counts as soon as it is whole, whatever its process does next.
   It is the result of [f i] computed in a process that the main process
   forked: the process holds the heap of the main process as it was at the
   fork, and [f] depends on nothing that changes after it is given to
   [Forked.start] (see there). So a later failure of that process, a kill at
   its deadline included, says nothing about an answer it has already sent:
   an answer is checked to be whole, of exactly the length it announced, for
   the item the process was given, and a partial answer never counts. *)
let item_size = 8

let forked_gc () =
  let gc = Gc.get () in
  Gc.set { gc with
           Gc.minor_heap_size = max gc.Gc.minor_heap_size (4 * 1024 * 1024);
           space_overhead = max gc.Gc.space_overhead 1000;
           max_overhead = 1000000 }

let write_all fd b =
  let rec go off =
    if off < Bytes.length b then
      match Unix.write fd b off (Bytes.length b - off) with
      | k -> go (off + k)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
  in
  go 0

(* Exactly [len] bytes, or [None] at end of file or on an error. *)
let read_exactly fd len =
  let b = Bytes.create len in
  let rec go off =
    if off = len then Some b
    else match Unix.read fd b off (len - off) with
      | 0 -> None
      | k -> go (off + k)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error _ -> None
  in
  go 0

let int_bytes i =
  let b = Bytes.create item_size in
  Bytes.set_int64_be b 0 (Int64.of_int i);
  b

(* What a process does to send an answer: its length, then the answer. *)
let default_answer_writer fd length answer =
  write_all fd length;
  write_all fd answer

let answer_writer = ref default_answer_writer
let set_answer_writer f = answer_writer := f

let run_forked ~heap_budget ~items ~results f =
  at_exit (fun () -> Unix._exit 2);
  let code =
    try
      let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
      Unix.dup2 null Unix.stdout;
      Unix.dup2 null Unix.stderr;
      Unix.close null;
      forked_gc ();
      let words0 = (Gc.quick_stat ()).Gc.major_words in
      let budget_words = float_of_int heap_budget /. float_of_int (Sys.word_size / 8) in
      (* What it has added to its major heap. The lazy GC frees little of it,
         so this bounds what the process holds beyond the pages it shares. *)
      let spent () = (Gc.quick_stat ()).Gc.major_words -. words0 >= budget_words in
      let rec loop () =
        match read_exactly items item_size with
        | None -> 0
        | Some b ->
          let i = Int64.to_int (Bytes.get_int64_be b 0) in
          let v = try Some (f i) with _ -> None in
          let last = spent () in
          let payload = Marshal.to_bytes (i, v, last) [] in
          !answer_writer results (int_bytes (Bytes.length payload)) payload;
          if last then 0 else loop ()
      in
      loop ()
    with _ -> 1
  in
  Unix._exit code

(* Reads into [b] from [off] what the descriptor [fd], which does not
   block, holds now: the new offset, or [None] at end of file or on an
   error. *)
let rec read_available fd b off =
  if off = Bytes.length b then Some off
  else match Unix.read fd b off (Bytes.length b - off) with
    | 0 -> None
    | k -> read_available fd b (off + k)
    | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EWOULDBLOCK), _, _) -> Some off
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> read_available fd b off
    | exception Unix.Unix_error _ -> None

type 'a progress =
  | Whole of 'a
  | Partial  (* bytes of it are still to come *)
  | Broken  (* the process ended, or wrote something else *)

module Forked = struct

  type proc = {
    fpid : int;
    items : Unix.file_descr;
    mutable items_open : bool;
    answers : Unix.file_descr;
    mutable frame : Bytes.t;  (* the length of the answer being read, then the answer *)
    mutable frame_got : int;  (* the bytes of [frame] read so far *)
    mutable in_answer : bool;  (* whether [frame] is the answer, not its length *)
    mutable current : int option;  (* the item it was given and has not answered *)
    mutable due : float;  (* when it must have answered [current] *)
    mutable answered : int;
  }

  type 'a t = {
    f : int -> 'a;
    k : int;
    n : int;
    heap_budget : int;
    item_timeout : float;
    mutable procs : proc list;  (* the processes that may still answer *)
    mutable exiting : proc list;  (* stopped or killed, not yet waited for *)
    mutable next : int;  (* the next item to hand out *)
    mutable stopped : bool;
    started : float;
    mutable forks : int;
    mutable fork_time : float;
    mutable polls : int;
    mutable poll_time : float;
    mutable delivered : int;
    mutable killed : int;
  }

  (* What [p] has sent of its answer, read without waiting: a length, then
     exactly one whole marshalled value of that length. *)
  let read_answer p =
    let rec go () =
      match read_available p.answers p.frame p.frame_got with
      | None -> Broken
      | Some got when got < Bytes.length p.frame -> p.frame_got <- got; Partial
      | Some _ when not p.in_answer ->
        let len = Int64.to_int (Bytes.get_int64_be p.frame 0) in
        if len < Marshal.header_size || len > Sys.max_string_length then Broken
        else begin
          p.frame <- Bytes.create len;
          p.frame_got <- 0;
          p.in_answer <- true;
          go ()
        end
      | Some _ ->
        let payload = p.frame in
        p.frame <- Bytes.create item_size;
        p.frame_got <- 0;
        p.in_answer <- false;
        match Marshal.total_size payload 0 with
        | total when Int.equal total (Bytes.length payload) ->
          (try Whole (Marshal.from_bytes payload 0) with _ -> Broken)
        | _ -> Broken
        | exception _ -> Broken
    in
    go ()

  (* Closed once only: a second close could close a descriptor reused since. *)
  let close_items p =
    if p.items_open then begin
      p.items_open <- false;
      close_report p.items
    end

  let kill p = try Unix.kill p.fpid Sys.sigkill with Unix.Unix_error _ -> ()

  let reaped p =
    debug (fun () -> str "forked process " ++ int p.fpid ++ str ": " ++ int p.answered ++ str " items")

  (* Its answers so far count, and it gets no more items. *)
  let retire s ~killed p =
    if killed then begin kill p; s.killed <- s.killed + 1 end;
    p.current <- None;
    close_items p;
    close_report p.answers;
    s.procs <- List.filter (fun q -> q != p) s.procs;
    s.exiting <- p :: s.exiting

  let spawn s =
    match Unix.pipe ~cloexec:true () with
    | exception Unix.Unix_error _ -> None
    | items_in, items ->
      match Unix.pipe ~cloexec:true () with
      | exception Unix.Unix_error _ -> close_report items_in; close_report items; None
      | answers, answers_out ->
        (* Everything that can fail is done before the fork, so a failure
           leaves no process behind: only this process's read end of the
           answers is made non-blocking, and the child closes its copy. *)
        match Unix.set_nonblock answers; Bytes.create item_size with
        | exception e when CErrors.noncritical e ->
          List.iter close_report [items_in; items; answers; answers_out];
          None
        | frame ->
          (* Otherwise a process would hold what is still buffered. *)
          flush_output ();
          let t0 = Unix.gettimeofday () in
          match Unix.fork () with
          | 0 ->
            (* A process that kept the item pipe of another one open would
               keep that one waiting for items after the last. *)
            List.iter (fun p -> close_items p; close_report p.answers) s.procs;
            close_report items;
            close_report answers;
            run_forked ~heap_budget:s.heap_budget ~items:items_in ~results:answers_out s.f
          | fpid ->
            s.forks <- s.forks + 1;
            s.fork_time <- s.fork_time +. (Unix.gettimeofday () -. t0);
            close_report items_in;
            close_report answers_out;
            (* Should anything still raise before the child is in [procs],
               where cleanup finds it, that child is killed and waited for
               here, so no process outlives the call untracked. *)
            (try
               let p = { fpid; items; items_open = true; answers;
                         frame; frame_got = 0; in_answer = false;
                         current = None; due = infinity; answered = 0 } in
               s.procs <- p :: s.procs;
               Some p
             with e ->
               (try Unix.kill fpid Sys.sigkill with Unix.Unix_error _ -> ());
               (try ignore (waitpid_non_intr [] fpid) with Unix.Unix_error _ -> ());
               close_report items;
               close_report answers;
               raise e)
          | exception Unix.Unix_error _ ->
            List.iter close_report [items_in; items; answers; answers_out];
            None

  (* A write to a process that has ended must fail, not kill this one; the
     main process keeps its own handling of SIGPIPE otherwise. *)
  let write_item p i =
    let sigpipe = Sys.signal Sys.sigpipe Sys.Signal_ignore in
    Fun.protect ~finally:(fun () -> Sys.set_signal Sys.sigpipe sigpipe)
      (fun () -> write_all p.items (int_bytes i))

  let give s p =
    if s.next < s.k then begin
      let i = s.next in
      s.next <- i + 1;
      match write_item p i with
      | () ->
        p.current <- Some i;
        p.due <- Unix.gettimeofday () +. s.item_timeout
      | exception Unix.Unix_error _ -> retire s ~killed:true p
    end
    else retire s ~killed:false p

  (* Up to [n] processes, while there are items to hand out. *)
  let rec refill s =
    if s.next < s.k && List.length s.procs < s.n then
      match spawn s with
      | Some p -> give s p; refill s
      | None -> ()

  (* The processes that stopped and have ended are waited for, without
     blocking. *)
  let reap_ended s =
    s.exiting <- List.filter (fun p ->
        match waitpid_non_intr [Unix.WNOHANG] p.fpid with
        | 0, _ -> true
        | _ -> reaped p; false
        | exception Unix.Unix_error _ -> false)
        s.exiting

  let stop s =
    if not s.stopped then begin
      s.stopped <- true;
      let live = s.procs in
      s.procs <- [];
      List.iter (fun p -> kill p; close_items p; close_report p.answers) live;
      (* All are killed first, so they end together. *)
      List.iter kill s.exiting;
      List.iter (fun p ->
          (try ignore (waitpid_non_intr [] p.fpid) with Unix.Unix_error _ -> ());
          reaped p)
        (live @ s.exiting);
      s.exiting <- [];
      debug (fun () ->
          str "forked processes: " ++ int s.delivered ++ str " answers of " ++ int s.next ++
          str " items handed out, of " ++ int s.k ++ str ", by " ++ int s.forks ++
          str " processes (" ++ int s.killed ++ str " killed; forks took " ++ real s.fork_time ++
          str " s), " ++ int s.polls ++ str " polls (" ++ real s.poll_time ++ str " s), in " ++
          real (Unix.gettimeofday () -. s.started) ++ str " s")
    end

  let start ?(heap_budget = max_int) ?(item_timeout = infinity) n f k =
    let s = { f; k; n = min n k; heap_budget; item_timeout; procs = []; exiting = [];
              next = 0; stopped = false; started = Unix.gettimeofday ();
              forks = 0; fork_time = 0.; polls = 0; poll_time = 0.; delivered = 0;
              killed = 0 } in
    (* After an error, no process keeps running. *)
    match refill s with
    | () -> s
    | exception e -> stop s; raise e

  let poll ?(wait = 0.) (s : 'a t) (deliver : int -> 'a -> unit) =
    if s.stopped then false
    else begin
      let t0 = Unix.gettimeofday () in
      s.polls <- s.polls + 1;
      let busy = List.filter (fun p -> Option.has_some p.current) s.procs in
      let ready =
        if CList.is_empty busy then []
        else
          let to_due = List.fold_left (fun w p -> Float.min w (p.due -. t0)) infinity busy in
          let timeout = Float.min wait to_due in
          let timeout = if Float.equal timeout infinity then -1. else Float.max 0. timeout in
          match Unix.select (List.map (fun p -> p.answers) busy) [] [] timeout with
          | ready, _, _ -> ready
          | exception Unix.Unix_error (Unix.EINTR, _, _) -> []
      in
      List.iter (fun p ->
          (* A process is late only if its answer is not whole when its
             deadline has passed: an answer that came in time and waited for
             the main process counts. *)
          let late = Unix.gettimeofday () >= p.due in
          if late || List.mem p.answers ready then
            match (read_answer p : (int * 'a option * bool) progress), p.current with
            | Whole (i, v, last), Some j when Int.equal i j ->
              p.answered <- p.answered + 1;
              (* With [last], it has spent its heap budget and exits. *)
              if last then retire s ~killed:false p else give s p;
              Option.iter (fun v -> s.delivered <- s.delivered + 1; deliver i v) v
            | Partial, _ when not late -> ()
            | (Whole _ | Partial | Broken), _ ->
              (* Late, ended, or wrong: its item is left to the caller. *)
              retire s ~killed:true p)
        busy;
      refill s;
      reap_ended s;
      s.poll_time <- s.poll_time +. (Unix.gettimeofday () -. t0);
      List.exists (fun p -> Option.has_some p.current) s.procs
    end

end

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
  List.iter (fun w ->
      try Unix.kill w.pid Sys.sigkill with Unix.Unix_error _ -> ())
    workers;
  List.iter (fun w ->
      (try ignore (waitpid_non_intr [] w.pid) with Unix.Unix_error _ -> ());
      close_report w.report;
      close_output w)
    workers

(* What the worker whose failure is being raised printed, standard output
   and standard error, until [print_held_output] or [drop_held_output]. *)
let held_output = ref ("", "")

let read_fd fd =
  let b = Buffer.create 1024 in
  let chunk = Bytes.create 65536 in
  let rec go () =
    match Unix.read fd chunk 0 (Bytes.length chunk) with
    | 0 -> ()
    | n -> Buffer.add_subbytes b chunk 0 n; go ()
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> go ()
  in
  (try ignore (Unix.lseek fd 0 Unix.SEEK_SET); go () with Unix.Unix_error _ -> ());
  Buffer.contents b

let read_output w =
  match w.output with
  | None -> ("", "")
  | Some (out, err) -> (read_fd out, read_fd err)

let print_output (out, err) =
  if out <> "" || err <> "" then begin
    flush_output ();
    match !held with
    | Some q ->
      if out <> "" then Queue.push (Out out) q;
      if err <> "" then Queue.push (Err err) q
    | None ->
      if out <> "" then print_chunk (Out out);
      if err <> "" then print_chunk (Err err)
  end

(* The worker [w] failed: every worker is stopped, and what it printed
   kept. *)
let fail w status =
  held_output := read_output w;
  close_output w;
  abort ();
  raise (WorkerFailed (w.pid, status, w.batch))

let print_held_output () =
  let s = !held_output in
  held_output := ("", "");
  print_output s

let drop_held_output () = held_output := ("", "")

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
  if w.released <> None || k < 1 || k > w.batch.size then
    fail w (Unix.WEXITED 0);
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
    | None -> fail w status
    | Some k ->
      (match w.released with
       | Some r when not (Int.equal r k) -> fail w status
       | Some _ | None -> ());
      (* It ended successfully, so what it printed is printed now. *)
      print_output (read_output w);
      close_output w;
      note_done w.tasks k;
      match w.released with
      | Some _ ->
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

(* One slot kept for the worker of [validate_tables] while the walk runs
   before it is started ([expect_validator]): from the start of the walk it
   holds a slot, as it does when it is started first. It is not waited for:
   the slots may all be held by checks that take long, or never end, while
   a table the validator would refuse is waiting to be read. *)
let validator_reserved = ref 0

let free_slots slots = slots - List.length !running - !validator_reserved

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

(* The runs of [l], in order: its maximal sequences of jobs that one
   library's walk deferred. A library's jobs make one run, unless jobs
   given back were put in front of the queue. *)
let runs l =
  let close acc cur = if CList.is_empty cur then acc else List.rev cur :: acc in
  let rec go acc cur = function
    | [] -> List.rev (close acc cur)
    | t :: l ->
      match cur with
      | t' :: _ when not (Int.equal t'.group t.group) -> go (close acc cur) [t] l
      | _ -> go acc (t :: cur) l
  in
  go [] [] l

let rec split_at n acc l =
  if Int.equal n 0 then List.rev acc, l
  else match l with
    | [] -> List.rev acc, []
    | t :: l -> split_at (n - 1) (t :: acc) l

(* A run cut into pieces of [size] jobs, the last one shorter, each with
   whether it may be dealt now. While the libraries are walked, [open_group]
   is the library whose walk is still deferring jobs: of its run only the
   whole pieces may be dealt, and the rest waits for the jobs still to come,
   so that a batch takes them together and one process parses its table. *)
let pieces ?open_group size r =
  let rec cut acc r =
    if CList.is_empty r then List.rev acc
    else let p, r = split_at size [] r in cut (p :: acc) r
  in
  let still_open = match open_group, r with
    | Some g, t :: _ -> Int.equal t.group g
    | _ -> false
  in
  List.map (fun p -> (not still_open || List.length p >= size), p) (cut [] r)

(* Deal up to [k] batches of about [size] jobs from the queue.

   The pieces that may be dealt are striped over [s] lanes, [s] being the
   number of batches of [size] they make: batch [j] takes pieces [j], [j +
   s], [j + 2s]... until it holds [size] jobs. So a batch holds whole
   libraries, and libraries next to each other in the queue go to different
   batches. A batch holds at most [2 * size - 1] jobs.

   While the libraries are walked ([walk]), the open library's last piece
   waits (see [pieces]), a batch is run newest first, and a batch whose lane
   ran short of [size / 2] jobs is not dealt: a fork is not worth it, and its
   jobs wait for the next deal. In [finish] every batch is dealt, oldest
   first, down to a single job. What is not dealt stays in the queue, in
   order. *)
let deal ?(walk = false) k size =
  let all = List.rev (Queue.fold (fun acc t -> t :: acc) [] queue) in
  let open_group = if walk then Some !current_group else None in
  let ps = Array.of_list (List.concat_map (pieces ?open_group size) (runs all)) in
  (* Costliest libraries first, so they take the first lanes and stay first
     in what is left; pieces of equal cost keep their order. The library
     still deferring jobs stays last, where its next jobs join it, so that
     its jobs stay together and its pieces fill up as before. *)
  if Hashtbl.length group_costs > 0 then begin
    let key (_, p) =
      let g = (List.hd p).group in
      match open_group with
      | Some og when Int.equal g og -> neg_infinity
      | _ -> group_cost g
    in
    Array.stable_sort (fun a b -> Float.compare (key b) (key a)) ps
  end;
  let n = Array.fold_left (fun n (ok, p) -> if ok then n + List.length p else n) 0 ps in
  let s = max k (n / size) in
  let filled = Array.make k 0 in
  let lane = Array.make (Array.length ps) (-1) in
  let next = ref 0 in
  Array.iteri (fun i (ok, p) ->
      if ok then begin
        let j = !next mod s in
        incr next;
        if j < k && filled.(j) < size then begin
          lane.(i) <- j;
          filled.(j) <- filled.(j) + List.length p
        end
      end)
    ps;
  let dealt j = filled.(j) > 0 && (not walk || 2 * filled.(j) >= size) in
  let batches = Array.make k [] in
  let left = ref [] in
  Array.iteri (fun i (_, p) ->
      let j = lane.(i) in
      if j >= 0 && dealt j then batches.(j) <- List.rev_append p batches.(j)
      else left := List.rev_append p !left)
    ps;
  (* While output is held, each worker is given its report pipe and its
     two output files before anything leaves the queue: a worker without
     them would print at once, among the lines still to come from the
     intern. If any is missing, nothing is dealt now; the jobs wait in the
     queue, as they were, for a deal after the output is printed. *)
  let prepare b =
    if CList.is_empty b then Ok None
    else match Unix.pipe ~cloexec:true () with
      | exception Unix.Unix_error _ -> Error ()
      | report, report_out ->
        match open_output () with
        | Some output -> Ok (Some (report, report_out, output))
        | None -> close_fd report; close_fd report_out; Error ()
  in
  let release_prepared = function
    | Some (report, report_out, (out, err)) ->
      close_fd report; close_fd report_out; close_fd out; close_fd err
    | None -> ()
  in
  let prepared =
    if Option.is_empty !held then Some (Array.map (fun _ -> None) batches)
    else
      let got = ref [] in
      let ok = Array.for_all (fun b ->
          match prepare b with
          | Ok p -> got := p :: !got; true
          | Error () -> false) batches
      in
      if ok then Some (Array.of_list (List.rev !got))
      else (List.iter release_prepared !got; None)
  in
  match prepared with
  | None -> ()
  | Some prepared ->
    Queue.clear queue;
    List.iter (fun t -> Queue.push t queue) (List.rev !left);
    prepared_fds := Array.fold_left (fun fds p -> match p with
        | Some (report, report_out, (out, err)) -> report :: report_out :: out :: err :: fds
        | None -> fds) [] prepared;
    (* Only once the queue holds what was not dealt: a worker inherits it by
       fork, and a batch whose fork fails is checked here. A batch is built
       newest first. *)
    Fun.protect ~finally:(fun () -> List.iter close_fd !prepared_fds; prepared_fds := [])
      (fun () ->
         Array.iteri (fun j b ->
             if not (CList.is_empty b) then
               spawn ?prepared:prepared.(j)
                 (Array.of_list (by_cost (if walk then b else List.rev b))))
           batches)

(* Hands out the batches a new job makes possible, at most once every
   [window] seconds. *)
let dispatch () =
  let now = Unix.gettimeofday () in
  if now -. !last_dispatch >= !window then begin
    last_dispatch := now;
    reap_finished ();
    let n = Queue.length queue in
    let size = max min_batch ((n + !max_workers) / (!max_workers + 1)) in
    let k = min (free_slots !max_workers) (n / size) in
    (* While the libraries are checked, a worker runs its batch newest
       first: costly proofs come late in a library, so one deferred last no
       longer waits for the rest of its batch and is not the one given back
       when the worker's budget runs out. The task that reads a library's
       table, when there is one, is the oldest job of its group, so it runs
       after the checks that already parsed the table. *)
    if k > 0 then deal ~walk:true k size
    (* No release is requested here: a request needs an empty queue,
       which the walk rarely leaves, and the walk reads a release message
       only when it reaps its worker, and deals only batches of at least
       [min_batch / 2] jobs; so a released tail would wait here anyway.
       [finish] asks, reads and deals at once. *)
  end

let defer kn check =
  incr deferred;
  if !max_workers = 0 then begin check (); incr checks_done end
  else begin
    Queue.push { job = Proof kn; group = !current_group; run = check } queue;
    dispatch ()
  end

(* Whether [validate_tables] handed every hashed table to a worker of its
   own: then the per-library table tasks are not needed. *)
let tables_validated = ref false

(* The validator's progress: an unnamed file in which, after each table
   it reads without error, it writes how many it has read, and the tables
   in its order. Only used when it fails: a successful worker's reads are
   counted from its report. *)
let validator = ref None

let write_progress fd k =
  let b = Bytes.create 8 in
  Bytes.set_int64_be b 0 (Int64.of_int k);
  try
    ignore (Unix.lseek fd 0 Unix.SEEK_SET);
    ignore (Unix.write fd b 0 8)
  with Unix.Unix_error _ -> ()

let validator_progress () =
  match !validator with
  | None -> ()
  | Some (fd, tables) ->
    validator := None;
    let b = Bytes.create 8 in
    let k =
      try
        ignore (Unix.lseek fd 0 Unix.SEEK_SET);
        if Unix.read fd b 0 8 = 8 then Int64.to_int (Bytes.get_int64_be b 0) else 0
      with Unix.Unix_error _ -> 0
    in
    close_fd fd;
    for i = 0 to min k (Array.length tables) - 1 do
      tables_read := DirPath.Set.add tables.(i) !tables_read
    done

let defer_table dp read =
  incr current_group;
  if Hashtbl.length cost_hints > 0 then
    (match Hashtbl.find_opt cost_hints (DirPath.to_string dp) with
     | Some c -> Hashtbl.replace group_costs !current_group c
     | None -> ());
  if !max_workers = 0 then begin incr tables_deferred; read (); incr tables_done end
  else if not !tables_validated then begin
    incr tables_deferred;
    Queue.push { job = Table dp; group = !current_group; run = read } queue;
    dispatch ()
  end

(* The walk is about to run before [validate_tables] is called, which will
   read every table: no per-library table task is queued meanwhile, so the
   queue holds the same tasks as when [validate_tables] runs first, and the
   validator's slot is kept free for it. *)
let expect_validator () =
  tables_validated := true;
  validator_reserved := 1

(* Stock parses every table while it interns the libraries, before it
   checks any, so a malformed table stops it there. The tables are read
   here, in that order, by one worker started before the walk, so that a
   malformed table stops the run near where it stops stock, instead of when
   the workers reach that library's checks, which on a whole tree is most of
   the way through. The checks still read the tables they need, in their own
   batches.

   The worker has no time budget. The budget exists because a worker's
   memory grows while it lives, as its garbage collector touches the heap it
   shares with the main process; a worker that stopped at the budget would
   give its tables back to the queue, where they wait behind the checks,
   which is the delay this worker removes. This one keeps no table it reads,
   so it holds at most one table beyond the heap it was forked with. For the
   same reason it is never asked to release the tables it has not read.

   If it fails, the tables it read without error before the one that failed
   are credited ([validator_progress]), so that the main process, which then
   looks for the first table that does not parse, starts where it stopped
   instead of reading them all again. *)
let validate_tables tables =
  validator_reserved := 0;
  if !max_workers > 0 && not (CList.is_empty tables) then begin
    let progress = open_capture () in
    let tasks = Array.of_list (List.mapi (fun i (dp, read) ->
        let run () =
          read ();
          Option.iter (fun fd -> write_progress fd (i + 1)) progress
        in
        { job = Table dp; group = 0; run }) tables) in
    Option.iter (fun fd ->
        validator := Some (fd, Array.of_list (List.map fst tables))) progress;
    tables_deferred := !tables_deferred + Array.length tasks;
    tables_validated := true;
    let b = !budget in
    budget := infinity;
    never_release := true;
    Fun.protect ~finally:(fun () -> budget := b; never_release := false)
      (fun () -> spawn ~releasable:false tasks)
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
        int !checks_done ++ str " checks run of " ++ int !deferred ++ str " deferred, " ++
        int !main_cooks ++ str " cooked in the main process");
    debug (fun () ->
        str "tables: " ++ int !tables_done ++ str " read of " ++
        int !tables_deferred ++ str " deferred, " ++
        int !table_reads ++ str " parsed in the main process, " ++
        int !table_bytes ++ str " bytes read there")
  end
