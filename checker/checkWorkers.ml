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
    else (try !report_writer report !completed; 0 with _ -> 3)
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
   writes to is copied. Its major GC does almost no work ([forked_gc]): a
   major cycle would mark, and so copy, every inherited page that holds a live
   block, and even a lazy one marks a share of them for each word allocated.
   Its garbage is bounded instead: once its major heap has grown by more than
   the heap budget, it stops after the item it is on, and the main process
   forks a fresh process for the items that are left. So each process holds
   about what it allocated beyond what it shares.

   What a process does is optional: the caller computes whatever it does not
   answer. So no process may keep the main process waiting. The main process
   only looks at the processes when it asks to ([Forked.poll]), and then reads
   answers without waiting: their descriptors do not block, and the bytes of an
   answer are kept until it is whole. A process has a deadline for each item,
   counted from when it is given the item; a process whose answer is not whole
   when its deadline has passed is killed. A process that stops, for its heap
   budget or for want of items, is killed at once, and waited for without
   blocking; until then it keeps its place in the pool, so the processes are
   never more than asked for. [Forked.stop] kills every process that is left
   before it waits for it, and a kill always lets the wait return.

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
           space_overhead = max gc.Gc.space_overhead 1_000_000;
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
      (* What it has added to its major heap. The lazy GC frees little of it,
         so this bounds what the process holds beyond the pages it shares.
         OCaml 5's counters may lag by what was allocated since the last minor
         collection, so there one runs first; OCaml 4's are exact as read. *)
      let major_words () =
        if Sys.ocaml_release.major >= 5 then Gc.minor ();
        (Gc.quick_stat ()).Gc.major_words
      in
      let words0 = major_words () in
      let budget_words = float_of_int heap_budget /. float_of_int (Sys.word_size / 8) in
      let spent () = major_words () -. words0 >= budget_words in
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
    mutable answers_open : bool;
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
    lazy_gc : bool;
    mutable saved_gc : Gc.control option;  (* this process's GC, while it is lazy *)
    mutable procs : proc list;  (* the processes that may still answer *)
    mutable exiting : proc list;  (* killed, not yet waited for *)
    mutable next : int;  (* the next item to hand out *)
    mutable stopping : bool;  (* [stop] was called: no more results *)
    mutable stopped : bool;  (* [stop] has waited for every process *)
    started : float;
    mutable forks : int;
    mutable fork_time : float;
    mutable polls : int;
    mutable poll_time : float;
    mutable read_time : float;  (* reading and unmarshalling answers *)
    mutable deliver_time : float;  (* in the caller's [deliver] *)
    mutable refill_time : float;  (* handing out items, forks included *)
    mutable received : int;  (* bytes of whole answers *)
    mutable delivered : int;
    mutable killed : int;  (* processes that failed *)
  }

  (* Bytes of the whole answers read so far, for the debug summary. *)
  let answer_bytes = ref 0

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
        answer_bytes := !answer_bytes + Bytes.length payload;
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

  let close_answers p =
    if p.answers_open then begin
      p.answers_open <- false;
      close_report p.answers
    end

  let kill p = try Unix.kill p.fpid Sys.sigkill with Unix.Unix_error _ -> ()

  let reaped p =
    debug (fun () -> str "forked process " ++ int p.fpid ++ str ": " ++ int p.answered ++ str " items")

  (* While processes share the heap of this one, a major collection here
     would mark, and so copy, every page of it that holds a live block. With
     [lazy_gc], this process collects as lazily as they do while one of them
     runs, and takes back its own setting as soon as none runs and no result
     can come, and at [stop]. *)
  let lazy_on s =
    match s.saved_gc with
    | Some _ -> ()
    | None when not s.lazy_gc || CList.is_empty s.procs -> ()
    | None ->
      let c = Gc.get () in
      s.saved_gc <- Some c;
      Gc.set { c with Gc.space_overhead = max c.Gc.space_overhead 1000 }

  let lazy_off s = match s.saved_gc with
    | None -> ()
    | Some c -> Gc.set c; s.saved_gc <- None

  (* Its answers so far count, and it gets no more items. It is killed at
     once: whatever it does next, nothing it could still send is used. It
     keeps its place in the pool until it has been waited for
     ([reap_ended]), so the processes, those not yet waited for included,
     are never more than [n]. It is in [exiting] before it leaves [procs],
     so cleanup always finds it. *)
  let retire s ~failed p =
    kill p;
    if failed then s.killed <- s.killed + 1;
    p.current <- None;
    close_items p;
    close_answers p;
    s.exiting <- p :: s.exiting;
    s.procs <- List.filter (fun q -> q != p) s.procs

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
        match Unix.set_nonblock answers; Bytes.create item_size, ref true, ref true with
        | exception e when CErrors.noncritical e ->
          List.iter close_report [items_in; items; answers; answers_out];
          None
        | frame, in_open, out_open ->
          (* Otherwise a process would hold what is still buffered. *)
          flush_output ();
          let t0 = Unix.gettimeofday () in
          match Unix.fork () with
          | 0 ->
            (* A process that kept the item pipe of another one open would
               keep that one waiting for items after the last. *)
            List.iter (fun p -> close_items p; close_answers p) s.procs;
            close_report items;
            close_report answers;
            run_forked ~heap_budget:s.heap_budget ~items:items_in ~results:answers_out s.f
          | fpid ->
            (* Until the child is in [procs], where cleanup finds it, anything
               that raises, the statistics included, kills and waits for this
               child here, so no process outlives the call untracked. The last
               step, adding it to [procs], allocates nothing. *)
            (try
               close_report items_in;
               in_open := false;
               close_report answers_out;
               out_open := false;
               let p = { fpid; items; items_open = true; answers; answers_open = true;
                         frame; frame_got = 0; in_answer = false;
                         current = None; due = infinity; answered = 0 } in
               s.forks <- s.forks + 1;
               s.fork_time <- s.fork_time +. (Unix.gettimeofday () -. t0);
               let result = Some p in
               let procs = p :: s.procs in
               s.procs <- procs;
               result
             with e ->
               (try Unix.kill fpid Sys.sigkill with Unix.Unix_error _ -> ());
               (try ignore (waitpid_non_intr [] fpid) with Unix.Unix_error _ -> ());
               if !in_open then close_report items_in;
               if !out_open then close_report answers_out;
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
      | exception Unix.Unix_error _ -> retire s ~failed:true p
    end
    else retire s ~failed:false p

  (* Up to [n] processes, those not yet waited for included, while there are
     items to hand out. *)
  let rec refill s =
    if s.next < s.k && List.length s.procs + List.length s.exiting < s.n then
      match spawn s with
      | Some p -> give s p; refill s
      | None -> ()

  (* The processes that were killed and have ended are waited for, without
     blocking, which frees their places in the pool. *)
  let reap_ended s =
    s.exiting <- List.filter (fun p ->
        match waitpid_non_intr [Unix.WNOHANG] p.fpid with
        | 0, _ -> true
        | _ -> reaped p; false
        | exception Unix.Unix_error _ -> false)
        s.exiting

  let stop ?(extra = fun () -> mt ()) s =
    if not s.stopped then begin
      s.stopping <- true;
      (* Neither taking back this process's GC nor stopping the processes can
         prevent the other. *)
      Fun.protect ~finally:(fun () -> lazy_off s) (fun () ->
          (* All are killed first, so they end together. A process leaves
             [procs] for [exiting], and [exiting] only once it has been waited
             for, so a stop that was interrupted does what is left of it when
             it is called again. Only the processes of [procs] are signalled:
             none of them has been waited for, so each id still names its
             process. Those of [exiting] were killed when they got there
             ([retire], or the line below), and one of them may have been
             waited for just before an interruption, its id free for another
             process to take: they are only waited for, never signalled. *)
          List.iter (fun p -> kill p; close_items p; close_answers p) s.procs;
          let exiting = List.filter (fun p -> not (List.memq p s.exiting)) s.procs @ s.exiting in
          s.exiting <- exiting;
          s.procs <- [];
          let rec wait_all () = match s.exiting with
            | [] -> ()
            | p :: rest ->
              (try ignore (waitpid_non_intr [] p.fpid) with Unix.Unix_error _ -> ());
              s.exiting <- rest;
              reaped p;
              wait_all ()
          in
          wait_all ());
      s.stopped <- true;
      debug (fun () ->
          str "forked processes: " ++ int s.delivered ++ str " answers of " ++ int s.next ++
          str " items handed out, of " ++ int s.k ++ str ", by " ++ int s.forks ++
          str " processes (" ++ int s.killed ++ str " killed; forks took " ++ real s.fork_time ++
          str " s), " ++ int s.polls ++ str " polls (" ++ real s.poll_time ++ str " s: reading " ++
          int s.received ++ str " bytes " ++ real s.read_time ++ str " s, delivering " ++
          real s.deliver_time ++ str " s, handing out " ++ real s.refill_time ++ str " s), in " ++
          real (Unix.gettimeofday () -. s.started) ++ str " s" ++ extra ())
    end

  let start ?(lazy_gc = false) ?(heap_budget = max_int) ?(item_timeout = infinity) n f k =
    let s = { f; k; n = min n k; heap_budget; item_timeout; lazy_gc; saved_gc = None;
              procs = []; exiting = []; next = 0; stopping = false; stopped = false;
              started = Unix.gettimeofday ();
              forks = 0; fork_time = 0.; polls = 0; poll_time = 0.; read_time = 0.;
              deliver_time = 0.; refill_time = 0.; received = 0; delivered = 0;
              killed = 0 } in
    (* After an error, no process keeps running. *)
    match refill s; lazy_on s with
    | () -> s
    | exception e -> stop s; raise e

  let poll ?(wait = 0.) (s : 'a t) (deliver : int -> 'a -> unit) =
    if s.stopping then false
    else begin
      let t0 = Unix.gettimeofday () in
      let bytes0 = !answer_bytes in
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
          if late || List.mem p.answers ready then begin
            let t1 = Unix.gettimeofday () in
            let answer = (read_answer p : (int * 'a option * bool) progress) in
            let t2 = Unix.gettimeofday () in
            s.read_time <- s.read_time +. (t2 -. t1);
            match answer, p.current with
            | Whole (i, v, last), Some j when Int.equal i j ->
              p.answered <- p.answered + 1;
              (* With [last], it has spent its heap budget. *)
              if last then retire s ~failed:false p else give s p;
              Option.iter (fun v ->
                  s.delivered <- s.delivered + 1;
                  deliver i v;
                  s.deliver_time <- s.deliver_time +. (Unix.gettimeofday () -. t2))
                v
            | Partial, _ when not late -> ()
            | (Whole _ | Partial | Broken), _ ->
              (* Late, ended, or wrong: its item is left to the caller. *)
              retire s ~failed:true p
          end)
        busy;
      reap_ended s;
      let t3 = Unix.gettimeofday () in
      refill s;
      s.refill_time <- s.refill_time +. (Unix.gettimeofday () -. t3);
      lazy_on s;
      s.received <- s.received + (!answer_bytes - bytes0);
      s.poll_time <- s.poll_time +. (Unix.gettimeofday () -. t0);
      (* A result may still come from a process that runs, or, while items
         are left, from one forked once a killed one has been waited for. *)
      let more =
        not (CList.is_empty s.procs) || (s.next < s.k && not (CList.is_empty s.exiting))
      in
      if not more then lazy_off s;
      more
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
    match completed_count ~size:w.batch.size status report with
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
      else if not (CList.is_empty !running) then begin
        let pid, status = waitpid_non_intr [] (-1) in
        reaped pid status
      end
    done;
    debug (fun () ->
        str "done: " ++ int !forks ++ str " workers forked, " ++
        int !early_stops ++ str " stopped early")
  end
