(* Deferred checks run by CheckWorkers in forked workers, with a time
   budget: a worker that stops early gives back the rest of its batch,
   and every check still runs exactly once. *)

open OUnit
open Utest
open Coq_checklib

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

(* Constant number [i]. *)
let constant i =
  let open Names in
  Constant.make2
    (ModPath.MPfile (DirPath.make [Id.of_string "CheckWorkersTest"]))
    (Id.of_string (Printf.sprintf "c%d" i))

(* Each check appends one line "pid index\n" to a file shared by all the
   processes: an append of one line is atomic, so the file says which
   process ran which check, and in which order. *)
let with_log f =
  let name = Filename.temp_file "checkworkers" ".log" in
  let fd = Unix.openfile name [Unix.O_WRONLY; Unix.O_APPEND] 0o600 in
  let finally () = Unix.close fd; Sys.remove name in
  Fun.protect ~finally (fun () ->
      let read () =
        let ic = open_in name in
        let rec lines acc =
          match input_line ic with
          | l -> Scanf.sscanf l "%d %d" (fun p i -> lines ((p, i) :: acc))
          | exception End_of_file -> close_in ic; List.rev acc
        in
        lines []
      in
      f fd read)

let record fd i =
  let line = Printf.sprintf "%d %d\n" (Unix.getpid ()) i in
  assert (Unix.write_substring fd line 0 (String.length line) = String.length line)

(* [n] deferred checks, [-j jobs], then [finish]. A check [refuse] raises;
   check [i] records itself, then runs [work i]. Returns the log, or the
   exception that [finish] raised (after [abort], as the checker does). *)
let run ?(jobs = 2) ?refuse ?(work = fun _ -> ()) ~budget n =
  with_log (fun fd read ->
      CheckWorkers.set_jobs ~profiling:false jobs;
      CheckWorkers.set_budget budget;
      Fun.protect
        ~finally:(fun () ->
            CheckWorkers.set_jobs ~profiling:false 1;
            CheckWorkers.set_budget CheckWorkers.default_budget)
        (fun () ->
           for i = 0 to n - 1 do
             CheckWorkers.defer (constant i) (fun () ->
                 if Some i = refuse then failwith "refused";
                 record fd i;
                 work i)
           done;
           let result =
             try CheckWorkers.finish (); None
             with e -> CheckWorkers.abort (); Some e
           in
           (* No worker is left behind. *)
           (match Unix.waitpid [Unix.WNOHANG] (-1) with
            | exception Unix.Unix_error (Unix.ECHILD, _, _) -> ()
            | _ -> assert_failure "a worker was left behind");
           result, read ()))

let me = Unix.getpid ()

let assert_exactly_once n log =
  let seen = Array.make n 0 in
  List.iter (fun (_, i) -> seen.(i) <- seen.(i) + 1) log;
  Array.iteri (fun i c ->
      if c <> 1 then
        assert_failure (Printf.sprintf "check %d ran %d times" i c))
    seen

let workers_of log = List.filter (fun (p, _) -> p <> me) log

let checks_of p log = List.filter_map (fun (q, i) -> if q = p then Some i else None) log

let pids_of log = List.sort_uniq compare (List.map fst (workers_of log))

(* The batches [finish] deals to [slots] workers from [0 .. n-1] when no
   worker stops early, in order: each has [ceil (r / (2 * slots))] checks
   taken one in [r / size] from the front of the [r] that remain, and the
   checks not taken stay in front, in order. *)
let expected_batches ~slots n =
  let rec go acc queue =
    match queue with
    | [] -> List.rev acc
    | _ ->
      let r = List.length queue in
      let size = (r + 2 * slots - 1) / (2 * slots) in
      let lanes = max 1 (r / size) in
      let taken = min r (lanes * size) in
      let batch = List.filteri (fun i _ -> i < taken && i mod lanes = 0) queue in
      let rest = List.filteri (fun i _ -> not (i < taken && i mod lanes = 0)) queue in
      go (batch :: acc) rest
  in
  go [] (List.init n Fun.id)

let n = 200

let assert_no_exception = function
  | None -> ()
  | Some e -> assert_failure ("unexpected " ^ Printexc.to_string e)

(* All the checks here are deferred within a fraction of a second, less
   than the dispatch window, and fewer than a batch of the library phase
   at a time, so all of them are dealt by [finish]. *)
let assert_main_checked_nothing log =
  if List.exists (fun (p, _) -> p = me) log then
    assert_failure "the main process checked a proof after the libraries"

let assert_batches_as_documented ~slots n log =
  let got = List.sort compare (List.map (fun p -> checks_of p log) (pids_of log)) in
  let expected = List.sort compare (expected_batches ~slots n) in
  let pr l = String.concat "; " (List.map (fun b -> String.concat "," (List.map string_of_int b)) l) in
  assert_equal ~printer:pr expected got

let () = add_test "no early stop: every check runs once" (fun () ->
    let result, log = run ~budget:CheckWorkers.default_budget n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log;
    assert_batches_as_documented ~slots:2 n log)

(* Fewer than 2N x 10 checks left: they are still dealt to workers, down
   to batches of one check. *)
let () = add_test "few checks left: all dealt, in batches as documented" (fun () ->
    let result, log = run ~jobs:4 ~budget:CheckWorkers.default_budget 30 in
    assert_no_exception result;
    assert_exactly_once 30 log;
    assert_main_checked_nothing log;
    assert_batches_as_documented ~slots:4 30 log;
    assert_bool "batches of one check" (List.exists (fun p -> List.length (checks_of p log) = 1) (pids_of log)))

(* With -j 2, two workers run at once after the libraries: each of the
   two checks waits until the other one has started. *)
let () = add_test "after the libraries, N workers run at once" (fun () ->
    let dir = Filename.temp_file "checkworkers" ".meet" in
    Sys.remove dir;
    Unix.mkdir dir 0o700;
    let meet i =
      close_out (open_out (Filename.concat dir (string_of_int i)));
      let deadline = Unix.gettimeofday () +. 10. in
      while Array.length (Sys.readdir dir) < 2 do
        if Unix.gettimeofday () > deadline then failwith "checked alone";
        Unix.sleepf 0.01
      done
    in
    let finally () = Array.iter (fun f -> Sys.remove (Filename.concat dir f)) (Sys.readdir dir); Sys.rmdir dir in
    Fun.protect ~finally (fun () ->
        let result, log = run ~jobs:2 ~budget:CheckWorkers.default_budget ~work:meet 2 in
        assert_no_exception result;
        assert_exactly_once 2 log;
        assert_main_checked_nothing log;
        assert_equal ~printer:string_of_int 2 (List.length (pids_of log))))

(* Budget 0: a worker completes one check and stops, so the checking
   progresses and ends, and what the workers did not do is checked again
   exactly once, by a later worker. *)
let () = add_test "budget 0: each worker completes one check, all run once" (fun () ->
    let result, log = run ~budget:0. n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log;
    let pids = pids_of log in
    assert_bool "workers ran" (pids <> []);
    List.iter (fun p -> assert_equal ~printer:string_of_int 1 (List.length (checks_of p log))) pids)

(* A budget that expires while a worker is in its batch. *)
let () = add_test "short budget: every check runs once" (fun () ->
    let result, log = run ~budget:0.05 ~work:(fun _ -> Unix.sleepf 0.02) n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log;
    List.iter (fun p ->
        let k = List.length (checks_of p log) in
        assert_bool "a worker that stops has completed at least one check" (k >= 1);
        assert_bool "a worker stops once its budget has passed" (k < 50))
      (pids_of log))

(* The first worker overruns its budget on its first check and gives the
   rest of its batch back while many checks are still queued behind it
   (each takes some time, so the other worker cannot drain them first).
   The next check [a] of that batch is long: it lasts until the check [b]
   after it has started. So [b] must not wait behind [a], in the same
   batch or for a slot: it heads another batch, checked by another worker
   at the same time. *)
let () = add_test "re-queued tail with a long head: the check after it does not wait" (fun () ->
    let n = 400 in
    let first = List.hd (expected_batches ~slots:2 n) in
    let a = List.nth first 1 and b = List.nth first 2 in
    let started = Filename.temp_file "checkworkers" ".started" in
    Sys.remove started;
    let work i =
      if i = 0 then Unix.sleepf 0.1
      else if i = b then close_out (open_out started)
      else if i = a then begin
        let deadline = Unix.gettimeofday () +. 10. in
        while not (Sys.file_exists started) do
          if Unix.gettimeofday () > deadline then failwith "waited behind the long check";
          Unix.sleepf 0.01
        done
      end
      else Unix.sleepf 0.005
    in
    let finally () = if Sys.file_exists started then Sys.remove started in
    Fun.protect ~finally (fun () ->
        let result, log = run ~budget:0.05 ~work n in
        assert_no_exception result;
        assert_exactly_once n log;
        assert_main_checked_nothing log;
        let by i = fst (List.find (fun (_, j) -> j = i) log) in
        assert_bool "the overrun worker stopped after its first check" (checks_of (by 0) log = [0]);
        assert_bool "the long check and the one after it went to different workers" (by a <> by b);
        List.iter (fun i ->
            assert_equal ~printer:string_of_int i (List.hd (checks_of (by i) log)))
          [a; b]))

let () = add_test "several workers, budget 0: every check runs once" (fun () ->
    let result, log = run ~jobs:4 ~budget:0. n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log)

(* A refusal behaves as with a worker that is not stopped: the worker that
   checks the proof exits with its error code and the main process raises
   WorkerFailed, or the main process checks it and raises CheckError. *)
let assert_refusal = function
  | Some (CheckWorkers.CheckError (kn, Failure _)) ->
    assert_bool "constant is the refused one" (Names.Constant.CanOrd.equal kn (constant 150))
  | Some (CheckWorkers.WorkerFailed (_, Unix.WEXITED c, b)) ->
    assert_bool "exit code of the error" (c <> 0);
    assert_bool "batch size" (b.CheckWorkers.size >= 1)
  | Some e -> assert_failure ("unexpected " ^ Printexc.to_string e)
  | None -> assert_failure "the refusal was lost"

let () = add_test "refusal in the re-queued tail surfaces" (fun () ->
    (* With budget 0 the proof, deep in a batch, is only reached once the
       batch has been given back. *)
    let result, log = run ~budget:0. ~refuse:150 n in
    assert_refusal result;
    assert_bool "the refused check did not record itself"
      (not (List.exists (fun (_, i) -> i = 150) log)))

let () = add_test "refusal surfaces without early stop" (fun () ->
    let result, _ = run ~budget:CheckWorkers.default_budget ~refuse:150 n in
    assert_refusal result)

let () = add_test "refusal surfaces, several workers" (fun () ->
    let result, _ = run ~jobs:4 ~budget:0. ~refuse:150 n in
    assert_refusal result)

(* The report is the one thing the main process believes about what a
   worker did not do: anything but a well-formed count in [1, size],
   together with a normal exit, fails the batch. *)
let with_writer w f =
  CheckWorkers.set_report_writer w;
  Fun.protect ~finally:(fun () ->
      CheckWorkers.set_report_writer CheckWorkers.default_report_writer) f

let assert_worker_failed ?status writer =
  with_writer writer (fun () ->
      let result, _ = run ~budget:CheckWorkers.default_budget n in
      match result, status with
      | Some (CheckWorkers.WorkerFailed (_, s, b)), expected ->
        assert_bool "batch is not empty" (b.CheckWorkers.size >= 1);
        Option.iter (fun e -> assert_bool "status" (e = s)) expected
      | Some e, _ -> assert_failure ("unexpected " ^ Printexc.to_string e)
      | None, _ -> assert_failure "no failure")

let write_raw fd s = ignore (Unix.write_substring fd s 0 (String.length s))

let count_bytes k =
  let b = Bytes.create 8 in
  Bytes.set_int64_be b 0 k;
  Bytes.to_string b

let () = add_test "no report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun _ _ -> ()))

let () = add_test "short report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd "abcd"))

let () = add_test "long report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd c -> write_raw fd (count_bytes (Int64.of_int c) ^ "x")))

let () = add_test "report of 0 fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd (count_bytes 0L)))

let () = add_test "negative report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd (count_bytes (-1L))))

let () = add_test "report above the batch size fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0)
      (fun fd _ -> write_raw fd (count_bytes (Int64.of_int 1_000_000))))

let () = add_test "huge report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd (count_bytes Int64.max_int)))

let () = add_test "report off by one above the batch size fails the worker" (fun () ->
    (* The batch is [n / stride] = 50 checks. *)
    assert_worker_failed ~status:(Unix.WEXITED 0)
      (fun fd c -> write_raw fd (count_bytes (Int64.of_int (c + 1)))))

let () = add_test "exit code 7 after a good report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 7)
      (fun fd c -> CheckWorkers.default_report_writer fd c; Unix._exit 7))

let () = add_test "kill after a good report fails the worker" (fun () ->
    assert_worker_failed
      (fun fd c -> CheckWorkers.default_report_writer fd c; Unix.kill (Unix.getpid ()) Sys.sigkill))

let () = add_test "raise while reporting fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 3) (fun _ _ -> failwith "no report"))

let () = add_test "a good report is accepted" (fun () ->
    with_writer CheckWorkers.default_report_writer (fun () ->
        let result, log = run ~budget:CheckWorkers.default_budget n in
        assert_no_exception result;
        assert_exactly_once n log))

let () = add_test "negative budget is refused" (fun () ->
    assert_raises (Invalid_argument "CheckWorkers.set_budget") (fun () -> CheckWorkers.set_budget (-1.));
    assert_raises (Invalid_argument "CheckWorkers.set_budget") (fun () -> CheckWorkers.set_budget nan))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
