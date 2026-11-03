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

(* Library number [l]. *)
let library l =
  let open Names in
  DirPath.make [Id.of_string (Printf.sprintf "L%d" l)]

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
   exception that [defer] or [finish] raised (after [abort], as the
   checker does).

   No batch is dealt while the checks are deferred, unless [windows] is
   given: the checks are then cut into [windows] equal parts, and the
   last check of each part is deferred once a window has passed
   ([CheckWorkers.end_window]), so that deferring it deals batches as
   while the libraries are checked. The window itself never passes, so
   what is dealt does not depend on how fast the test runs. [before_finish]
   is given the log reader after the last [defer].

   With [libs], the list of the sizes of the libraries, the checks are
   deferred as those libraries would defer them, one after the other, each
   preceded by the task that reads its table of opaque proofs, which
   records itself as [- (library + 1)]. *)
let run ?(jobs = 2) ?refuse ?(work = fun _ -> ()) ?(windows = 0) ?(libs = [])
    ?(before_finish = fun _ -> ()) ~budget n =
  with_log (fun fd read ->
      CheckWorkers.set_jobs ~profiling:false jobs;
      CheckWorkers.set_budget budget;
      CheckWorkers.set_window infinity;
      Fun.protect
        ~finally:(fun () ->
            CheckWorkers.set_jobs ~profiling:false 1;
            CheckWorkers.set_budget CheckWorkers.default_budget;
            CheckWorkers.set_window 1.0)
        (fun () ->
           let part = if windows = 0 then 0 else n / windows in
           (* [starts.(i)] is the library that starts at check [i], if any. *)
           let starts = Array.make (n + 1) (-1) in
           ignore (List.fold_left (fun (l, i) s -> starts.(i) <- l; (l + 1, i + s)) (0, 0) libs);
           let result =
             try
               for i = 0 to n - 1 do
                 if part > 0 && i mod part = part - 1 then CheckWorkers.end_window ();
                 let l = starts.(i) in
                 if l >= 0 then
                   CheckWorkers.defer_table (library l) (fun () -> record fd (- (l + 1)));
                 CheckWorkers.defer (constant i) (fun () ->
                     if Some i = refuse then failwith "refused";
                     record fd i;
                     work i)
               done;
               before_finish read;
               CheckWorkers.finish (); None
             with e -> CheckWorkers.abort (); Some e
           in
           (* No worker is left behind. *)
           (match Unix.waitpid [Unix.WNOHANG] (-1) with
            | exception Unix.Unix_error (Unix.ECHILD, _, _) -> ()
            | _ -> assert_failure "a worker was left behind");
           result, read ()))

let me = Unix.getpid ()

(* Every check ran once. The tasks that read a table, which record a
   negative number, are counted by [assert_tables_once]. *)
let assert_exactly_once n log =
  let seen = Array.make n 0 in
  List.iter (fun (_, i) -> if i >= 0 then seen.(i) <- seen.(i) + 1) log;
  Array.iteri (fun i c ->
      if c <> 1 then
        assert_failure (Printf.sprintf "check %d ran %d times" i c))
    seen

let assert_tables_once libs log =
  let seen = Array.make libs 0 in
  List.iter (fun (_, i) -> if i < 0 then seen.(- i - 1) <- seen.(- i - 1) + 1) log;
  Array.iteri (fun l c ->
      if c <> 1 then
        assert_failure (Printf.sprintf "the table of library %d was read %d times" l c))
    seen

let workers_of log = List.filter (fun (p, _) -> p <> me) log

let checks_of p log = List.filter_map (fun (q, i) -> if q = p then Some i else None) log

let pids_of log = List.sort_uniq compare (List.map fst (workers_of log))

(* [deal ~group ?open_group k size queue]: the batches, and what stays
   queued, as CheckWorkers.deal makes them. The runs of one group are cut
   into pieces of [size] jobs; with [s] the number of batches of [size] the
   pieces make, batch [j] takes pieces [j], [j + s]... until it holds
   [size] jobs. [open_group] is given while the libraries are walked: it
   is the library whose walk is still deferring jobs, of which only the
   whole pieces are dealt; a batch is then run newest first, and one of
   fewer than [size / 2] jobs is not dealt. *)
let deal ?(group = fun _ -> 0) ?open_group k size queue =
  let walk = Option.has_some open_group in
  let rec runs acc cur = function
    | [] -> List.rev (if cur = [] then acc else List.rev cur :: acc)
    | x :: l ->
      (match cur with
       | y :: _ when group y <> group x -> runs (List.rev cur :: acc) [x] l
       | _ -> runs acc (x :: cur) l)
  in
  let rec cut r =
    if r = [] then []
    else List.filteri (fun i _ -> i < size) r :: cut (List.filteri (fun i _ -> i >= size) r)
  in
  let pieces = List.concat_map (fun r ->
      let still_open = Option.equal Int.equal open_group (Some (group (List.hd r))) in
      List.map (fun p -> (not still_open || List.length p >= size), p) (cut r))
      (runs [] [] queue)
  in
  let n = List.fold_left (fun n (ok, p) -> if ok then n + List.length p else n) 0 pieces in
  let s = max k (n / size) in
  let filled = Array.make k 0 in
  let next = ref 0 in
  let lanes = List.map (fun (ok, p) ->
      if not ok then -1
      else begin
        let j = !next mod s in
        incr next;
        if j < k && filled.(j) < size then (filled.(j) <- filled.(j) + List.length p; j) else -1
      end) pieces
  in
  let dealt j = j >= 0 && filled.(j) > 0 && (not walk || 2 * filled.(j) >= size) in
  let batch j = List.concat (List.filteri (fun i _ -> List.nth lanes i = j) (List.map snd pieces)) in
  let batches = List.filter (fun b -> b <> [])
      (List.init k (fun j -> if dealt j then batch j else [])) in
  let rest = List.concat (List.filteri (fun i _ -> not (dealt (List.nth lanes i))) (List.map snd pieces)) in
  (if walk then List.map List.rev batches else batches), rest

(* The batches [finish] deals to [slots] workers from [queue] when no
   worker stops early, in order: one at a time, of [ceil (r / (2 *
   slots))] jobs when [r] remain. *)
let finish_batches ?group ~slots queue =
  let rec go acc queue =
    match queue with
    | [] -> List.rev acc
    | _ ->
      let r = List.length queue in
      let batches, rest = deal ?group 1 ((r + 2 * slots - 1) / (2 * slots)) queue in
      go (List.rev_append batches acc) rest
  in
  go [] queue

let expected_batches ~slots n = finish_batches ~slots (List.init n Fun.id)

(* The [k] batches of [size] jobs dealt from [queue] of one library,
   still open, while the libraries are checked, and what stays queued. *)
let library_batches ~k ~size queue = deal ~open_group:0 k size queue

let n = 200

let assert_no_exception = function
  | None -> ()
  | Some e -> assert_failure ("unexpected " ^ Printexc.to_string e)

(* The main process only queues and deals checks, and waits for workers:
   it checks a proof itself only when it cannot fork. *)
let assert_main_checked_nothing log =
  if List.exists (fun (p, _) -> p = me) log then
    assert_failure "the main process checked a proof"

let pr_batches l = String.concat "; " (List.map (fun b -> String.concat "," (List.map string_of_int b)) l)

(* Each worker checked exactly one of [expected], in its order. *)
let assert_batches expected log =
  let got = List.sort compare (List.map (fun p -> checks_of p log) (pids_of log)) in
  assert_equal ~printer:pr_batches (List.sort compare expected) got

let assert_batches_as_documented ~slots n log = assert_batches (expected_batches ~slots n) log

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

(* [k] checks that each wait until all [k] have started, so [k] workers
   run at once and end at about the same time. *)
let meeting k f =
  let dir = Filename.temp_file "checkworkers" ".meet" in
  Sys.remove dir;
  Unix.mkdir dir 0o700;
  let meet i =
    close_out (open_out (Filename.concat dir (string_of_int i)));
    let deadline = Unix.gettimeofday () +. 10. in
    while Array.length (Sys.readdir dir) < k do
      if Unix.gettimeofday () > deadline then failwith "checked alone";
      Unix.sleepf 0.01
    done
  in
  let clear () = Array.iter (fun f -> Sys.remove (Filename.concat dir f)) (Sys.readdir dir) in
  Fun.protect ~finally:(fun () -> clear (); Sys.rmdir dir) (fun () -> f meet clear)

(* With -j 2, two workers run at once after the libraries. *)
let () = add_test "after the libraries, N workers run at once" (fun () ->
    meeting 2 (fun meet _ ->
        let result, log = run ~jobs:2 ~budget:CheckWorkers.default_budget ~work:meet 2 in
        assert_no_exception result;
        assert_exactly_once 2 log;
        assert_main_checked_nothing log;
        assert_equal ~printer:string_of_int 2 (List.length (pids_of log))))

(* Workers dealt by [finish] that end together are all reaped, whichever
   way the main process sees them end, and it then stops waiting. *)
let () = add_test "workers dealt by finish that end together are all reaped" (fun () ->
    meeting 4 (fun meet clear ->
        for _ = 1 to 30 do
          clear ();
          let result, log = run ~jobs:4 ~budget:CheckWorkers.default_budget ~work:meet 4 in
          assert_no_exception result;
          assert_exactly_once 4 log;
          assert_main_checked_nothing log
        done))

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

(* Libraries of the given sizes, as [run ~libs] defers them: each library's
   table task, recorded as [- (l + 1)], then its checks, numbered from 0
   across all of them; and the library of each job. *)
let lib_jobs sizes =
  let _, _, jobs = List.fold_left (fun (l, i, acc) s ->
      (l + 1, i + s, List.rev_append ((- (l + 1)) :: List.init s (fun k -> i + k)) acc))
      (0, 0, []) sizes
  in
  let jobs = List.rev jobs in
  let group =
    let lib = Hashtbl.create 17 in
    List.iteri (fun l s -> ignore s; Hashtbl.replace lib (- (l + 1)) l) sizes;
    let _ = List.fold_left (fun (l, i) s ->
        for k = i to i + s - 1 do Hashtbl.replace lib k l done; (l + 1, i + s)) (0, 0) sizes in
    Hashtbl.find lib
  in
  jobs, group

(* What [defer] deals at -j [jobs] when the last of [sizes] is deferred,
   past the window, with no worker running: the batches, and what stays
   queued for [finish]. The last library is still open. *)
let walk_batches ~jobs sizes =
  let all, group = lib_jobs sizes in
  let q = List.length all and w = jobs - 1 in
  let size = max CheckWorkers.min_batch ((q + w) / (w + 1)) in
  let k = min w (q / size) in
  deal ~group ~open_group:(List.length sizes - 1) k size all, group

(* Batches stripe whole libraries. Twelve libraries of [m / 4] checks each,
   with the task that reads each one's table before its checks, are dealt
   while the libraries are checked, the last one still open, so its jobs
   wait for the rest of it. The eleven others are pieces of [m / 4 + 1]
   jobs, and batch [j] of the three takes pieces [j], [j + 3], [j + 6]...
   until it holds [m] jobs: libraries 0, 3, 6 and 9; 1, 4, 7 and 10; 2, 5
   and 8. No library's jobs are split, and libraries next to each other go
   to different workers. *)
let () = add_test "libraries: batches stripe whole libraries" (fun () ->
    let per = CheckWorkers.min_batch / 4 in
    let sizes = List.init 12 (fun _ -> per) in
    let n = 12 * per in
    let result, log = run ~jobs:4 ~windows:1 ~libs:sizes ~budget:CheckWorkers.default_budget n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_tables_once 12 log;
    assert_main_checked_nothing log;
    let (walk, rest), group = walk_batches ~jobs:4 sizes in
    let lib l = (- (l + 1)) :: List.init per (fun i -> l * per + i) in
    let libs_of ls = List.rev (List.concat_map lib ls) in
    assert_equal ~printer:pr_batches
      [libs_of [0; 3; 6; 9]; libs_of [1; 4; 7; 10]; libs_of [2; 5; 8]] walk;
    assert_batches (walk @ finish_batches ~group ~slots:4 rest) log)

(* The checks of one library are not spread over as many workers as it
   has checks: the worker of a batch runs the whole library. With six
   libraries of [m / 4] checks, one batch is dealt while the libraries are
   checked, and it holds libraries 0 to 3. *)
let () = add_test "libraries: one library's checks stay in one batch" (fun () ->
    let per = CheckWorkers.min_batch / 4 in
    let sizes = List.init 6 (fun _ -> per) in
    let n = 6 * per in
    let result, log = run ~jobs:4 ~windows:1 ~libs:sizes ~budget:CheckWorkers.default_budget n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_tables_once 6 log;
    assert_main_checked_nothing log;
    let by i = fst (List.find (fun (_, j) -> j = i) log) in
    List.iter (fun l ->
        let w = by (l * per) in
        for i = 1 to per - 1 do
          assert_equal ~printer:string_of_int w (by (l * per + i))
        done;
        assert_equal ~printer:string_of_int w (by (- (l + 1))))
      [0; 1; 2; 3])

(* While the libraries are checked, a batch whose lane is short of half
   the size wanted is not dealt. Libraries of [m], [m], 10 and 10 checks at
   -j 4, the last one open: two batches of [m] are wanted, and the pieces
   are [m], 1, [m], 1 and 11 jobs. Lane 0 takes the first piece, and lane 1
   would take the two pieces of one job: that batch is not dealt, and its
   jobs wait for [finish]. *)
let () = add_test "libraries: no small batch while the libraries are checked" (fun () ->
    let m = CheckWorkers.min_batch in
    let sizes = [m; m; 10; 10] in
    let n = 2 * m + 20 in
    let result, log = run ~jobs:4 ~windows:1 ~libs:sizes ~budget:CheckWorkers.default_budget n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_tables_once 4 log;
    assert_main_checked_nothing log;
    let (walk, rest), group = walk_batches ~jobs:4 sizes in
    assert_equal ~printer:string_of_int 1 (List.length walk);
    assert_equal ~printer:string_of_int m (List.length (List.hd walk));
    assert_batches (walk @ finish_batches ~group ~slots:4 rest) log)

let () = add_test "several workers, budget 0: every check runs once" (fun () ->
    let result, log = run ~jobs:4 ~budget:0. n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log)

(* A refusal behaves as with a worker that is not stopped: the worker that
   checks the proof exits with its error code and the main process raises
   WorkerFailed. The main process checks no proof itself, so it never
   raises CheckError here. *)
let assert_refusal = function
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

(* Batches dealt by [defer] while the libraries are checked (see the
   [windows] argument of [run]): a batch is a stripe of pieces of the
   queue that its worker checks newest first, and what the worker does not
   check goes back to the front in the order it would have checked it.

   [defer] deals while the libraries are checked only batches of [size =
   max min_batch ((q + w) / (w + 1))] jobs, of [q] queued jobs with [w]
   worker slots, [min free (q / size)] of them (or fewer, for one whose
   lane runs short of [size / 2]). The checks of these tests all belong to
   the library being walked, so only whole pieces of [size] are dealt, and
   batch [j] is piece [j]. So the fixtures are sized from [min_batch]
   ([m]): with [lib_n = 4 m + 1] checks, -j 2 deals one batch of [size2 =
   2 m + 1] and -j 4 three batches of [size4 = m + 1]; [9 m] and [12 m]
   checks in three windows deal three batches of [m] in the first window;
   [2 m] checks at -j 3 are two batches of [m] and nothing more. *)

let m = CheckWorkers.min_batch
let lib_n = 4 * m + 1
let size2 = (lib_n + 1) / 2
let size4 = (lib_n + 3) / 4

(* The log once it holds [k] records, while the main process waits
   before [finish], so that only the batches dealt by [defer] run. *)
let wait_records read k =
  let deadline = Unix.gettimeofday () +. 10. in
  let rec go () =
    let log = read () in
    if List.length log >= k then log
    else if Unix.gettimeofday () > deadline then
      assert_failure (Printf.sprintf "%d checks recorded, %d expected" (List.length log) k)
    else (Unix.sleepf 0.01; go ())
  in
  go ()

let heads read k = List.sort compare (List.map snd (wait_records read k))

(* -j 2: [lib_n] checks, one batch of [size2] dealt while the libraries are
   checked (positions 0 to [size2 - 1]), the others by [finish]. *)
let () = add_test "libraries, no early stop: one batch, newest first, then finish" (fun () ->
    let result, log = run ~jobs:2 ~windows:1 ~budget:CheckWorkers.default_budget lib_n in
    assert_no_exception result;
    assert_exactly_once lib_n log;
    assert_main_checked_nothing log;
    let lib, rest = library_batches ~k:1 ~size:size2 (List.init lib_n Fun.id) in
    assert_equal ~printer:pr_batches [List.init size2 (fun i -> size2 - 1 - i)] lib;
    assert_batches (lib @ finish_batches ~slots:2 rest) log)

(* -j 4: three batches of [size4], the runs at positions [0], [size4] and
   [2 size4], headed by [size4 - 1], [2 size4 - 1] and [3 size4 - 1], then
   [finish] deals the others. *)
let () = add_test "libraries, no early stop: three batches, newest first, then finish" (fun () ->
    let result, log = run ~jobs:4 ~windows:1 ~budget:CheckWorkers.default_budget lib_n in
    assert_no_exception result;
    assert_exactly_once lib_n log;
    assert_main_checked_nothing log;
    let lib, rest = library_batches ~k:3 ~size:size4 (List.init lib_n Fun.id) in
    assert_equal ~printer:pr_batches
      (List.init 3 (fun j -> List.init size4 (fun i -> size4 * (j + 1) - 1 - i))) lib;
    assert_batches (lib @ finish_batches ~slots:4 rest) log)

(* Budget 0: the worker of each batch dealt while the libraries are
   checked completes only the newest check of its batch, then gives the
   others back, and they are all still checked exactly once. *)
let () = add_test "libraries, budget 0: the newest check heads its batch, -j 2" (fun () ->
    let before_finish read =
      assert_equal ~printer:pr_batches [[size2 - 1]] [heads read 1] in
    let result, log = run ~jobs:2 ~windows:1 ~before_finish ~budget:0. lib_n in
    assert_no_exception result;
    assert_exactly_once lib_n log;
    assert_main_checked_nothing log)

let () = add_test "libraries, budget 0: the newest checks head the three batches, -j 4" (fun () ->
    let before_finish read =
      assert_equal ~printer:pr_batches [[size4 - 1; 2 * size4 - 1; 3 * size4 - 1]]
        [heads read 3] in
    let result, log = run ~jobs:4 ~windows:1 ~before_finish ~budget:0. lib_n in
    assert_no_exception result;
    assert_exactly_once lib_n log;
    assert_main_checked_nothing log)

(* Batches dealt in three windows, while the workers of earlier ones may
   still run or have given checks back. *)
let () = add_test "libraries, budget 0, three windows: every check runs once" (fun () ->
    let result, log = run ~jobs:3 ~windows:3 ~budget:0. (9 * m) in
    assert_no_exception result;
    assert_exactly_once (9 * m) log;
    assert_main_checked_nothing log;
    List.iter (fun p -> assert_equal ~printer:string_of_int 1 (List.length (checks_of p log))) (pids_of log))

let () = add_test "libraries, short budget, three windows: every check runs once" (fun () ->
    let result, log =
      run ~jobs:4 ~windows:3 ~budget:0.05 ~work:(fun _ -> Unix.sleepf 0.01) (12 * m) in
    assert_no_exception result;
    assert_exactly_once (12 * m) log;
    assert_main_checked_nothing log;
    List.iter (fun p ->
        let k = List.length (checks_of p log) in
        assert_bool "a worker that stops has completed at least one check" (k >= 1);
        assert_bool "a worker stops once its budget has passed" (k < 50))
      (pids_of log))

(* Check [size4 - 1] heads the first batch dealt at -j 4: its worker fails
   on it, and the batch it reports is that one. *)
let () = add_test "libraries: refusal in a batch surfaces" (fun () ->
    let h = size4 - 1 in
    let result, log =
      run ~jobs:4 ~windows:1 ~budget:CheckWorkers.default_budget ~refuse:h lib_n in
    assert_refusal result;
    (match result with
     | Some (CheckWorkers.WorkerFailed (_, _, b)) ->
       assert_bool "the batch is the one headed by the refused check"
         (b.CheckWorkers.first = CheckWorkers.Proof (constant h)
          && b.CheckWorkers.size = size4)
     | _ -> ());
    assert_bool "the refused check did not record itself"
      (not (List.exists (fun (_, i) -> i = h) log)))

(* Check [3 (m - 10)] is deep in the third batch dealt while the libraries
   are checked (positions [2 m] to [3 m - 1], newest first): with budget 0
   it is only reached from checks given back. *)
let () = add_test "libraries, budget 0, three windows: refusal surfaces" (fun () ->
    let r = 3 * (m - 10) in
    let result, log = run ~jobs:4 ~windows:3 ~budget:0. ~refuse:r (9 * m) in
    assert_refusal result;
    assert_bool "the refused check did not record itself"
      (not (List.exists (fun (_, i) -> i = r) log)))

(* A worker that has ended and not been reaped. *)
let zombie pid =
  let ic = open_in (Printf.sprintf "/proc/%d/stat" pid) in
  let l = Fun.protect ~finally:(fun () -> close_in ic) (fun () -> input_line ic) in
  l.[String.rindex l ')' + 2] = 'Z'

(* Workers that end together are all reaped, and then [finish] stops
   waiting. At -j 3, [2 m] checks are dealt in two batches of [m] while the
   libraries are checked, and none is left for [finish] to deal. Both
   workers have ended when [finish] starts, so its first look at them
   reaps the last one. *)
let () = add_test "workers that end together are all reaped" (fun () ->
    let before_finish read =
      let log = wait_records read (2 * m) in
      assert_equal ~printer:string_of_int 2 (List.length (pids_of log));
      let deadline = Unix.gettimeofday () +. 10. in
      while not (List.for_all zombie (pids_of log)) do
        if Unix.gettimeofday () > deadline then assert_failure "a worker did not end";
        Unix.sleepf 0.01
      done
    in
    let result, log =
      run ~jobs:3 ~windows:1 ~before_finish ~budget:CheckWorkers.default_budget (2 * m) in
    assert_no_exception result;
    assert_exactly_once (2 * m) log;
    assert_main_checked_nothing log)

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
    (* The first batch [finish] deals of 200 checks is 50 of them. *)
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

(* [CheckWorkers.Forked]: functions run in forked processes while the main
   process goes on; a result counts as soon as it has come whole. *)
let pr_results a =
  String.concat "," (Array.to_list (Array.map (function None -> "-" | Some v -> string_of_int v) a))

(* Every result of [f] on [0 .. k-1], polling until no item is left. *)
let run_all ?heap_budget ?item_timeout n f k =
  let out = Array.make k None in
  let s = CheckWorkers.Forked.start ?heap_budget ?item_timeout n f k in
  Fun.protect ~finally:(fun () -> CheckWorkers.Forked.stop s) (fun () ->
      while CheckWorkers.Forked.poll ~wait:0.1 s (fun i v -> out.(i) <- Some v) do () done);
  out

(* Every child has been waited for. *)
let assert_no_child_left () =
  match Unix.waitpid [Unix.WNOHANG] (-1) with
  | exception Unix.Unix_error (Unix.ECHILD, _, _) -> ()
  | pid, _ -> assert_failure (Printf.sprintf "child %d was left" pid)

let () = add_test "Forked: every item, in its place" (fun () ->
    let check n k =
      let expected = Array.init k (fun i -> Some (i * i)) in
      assert_equal ~printer:pr_results expected (run_all n (fun i -> i * i) k)
    in
    List.iter (fun n -> check n 300) [1; 2; 4; 16];
    (* More processes than items. *)
    check 50 10;
    assert_no_child_left ())

(* A heap budget of one byte, and an item that allocates in the major heap:
   every process stops after its first item, and a fresh process takes the
   next, so each item is answered, in place, by a process of its own, and
   every process has been waited for. *)
let () = add_test "Forked: a spent heap budget replaces the process" (fun () ->
    let k = 40 in
    let f i = Unix.getpid (), Array.length (Array.make 100_000 i) + i in
    let out = run_all ~heap_budget:1 4 f k in
    let pids = Array.to_list (Array.mapi (fun i v -> match v with
        | Some (pid, r) -> assert_equal ~printer:string_of_int (100_000 + i) r; pid
        | None -> assert_failure (Printf.sprintf "item %d has no answer" i)) out)
    in
    assert_bool "an item ran in the main process" (not (List.mem me pids));
    assert_equal ~printer:string_of_int k (List.length (List.sort_uniq compare pids));
    assert_no_child_left ())

(* Item 0 never ends (or, below, its process stops partway through an answer):
   with an item deadline of 1 s, the processes are done all the same, item 0
   has no result, every other item has its own, and no process is left. *)
let assert_item_0_dropped f =
  let k = 20 in
  let t0 = Unix.gettimeofday () in
  let out = run_all ~item_timeout:1. 4 f k in
  let took = Unix.gettimeofday () -. t0 in
  assert_bool (Printf.sprintf "it took %.1f s" took) (took < 30.);
  assert_equal None out.(0);
  Array.iteri (fun i v -> if i > 0 then
                  assert_equal ~printer:pr_results [| Some (i + 1) |] [| v |]) out;
  assert_no_child_left ()

let () = add_test "Forked: an item that never ends is dropped" (fun () ->
    assert_item_0_dropped (fun i -> if i = 0 then Unix.sleep 3600; i + 1))

let () = add_test "Forked: a process that stops is dropped" (fun () ->
    assert_item_0_dropped (fun i -> if i = 0 then Unix.kill (Unix.getpid ()) Sys.sigstop; i + 1))

(* A test answer writer, for item 0 only: [stall] decides what it does after
   it has written [part] of the answer. *)
let with_answer_writer ~part ~stall f =
  let writer fd length answer =
    let (i, _, _) : int * int option * bool = Marshal.from_bytes answer 0 in
    if i <> 0 then CheckWorkers.default_answer_writer fd length answer
    else begin
      ignore (Unix.write fd length 0 (Bytes.length length));
      ignore (Unix.write fd answer 0 (part (Bytes.length answer)));
      stall ()
    end
  in
  CheckWorkers.set_answer_writer writer;
  Fun.protect ~finally:(fun () -> CheckWorkers.set_answer_writer CheckWorkers.default_answer_writer) f

let () = add_test "Forked: a process stalled in the middle of an answer is dropped" (fun () ->
    with_answer_writer ~part:(fun n -> n / 2) ~stall:(fun () -> Unix.sleep 3600)
      (fun () -> assert_item_0_dropped (fun i -> i + 1)))

(* The process sends its whole last answer (heap budget of one byte), then
   stops instead of exiting: its answer counts, nothing waits for it, and
   [stop] kills it. *)
let () = add_test "Forked: a process that stops instead of exiting is killed" (fun () ->
    with_answer_writer ~part:Fun.id ~stall:(fun () -> Unix.kill (Unix.getpid ()) Sys.sigstop)
      (fun () ->
         let k = 20 in
         let t0 = Unix.gettimeofday () in
         let out = run_all ~heap_budget:1 4 (fun i -> Array.length (Array.make 1000 i) + i - 999) k in
         let took = Unix.gettimeofday () -. t0 in
         assert_bool (Printf.sprintf "it took %.1f s" took) (took < 30.);
         assert_equal ~printer:pr_results (Array.init k (fun i -> Some (i + 1))) out;
         assert_no_child_left ()))

(* The children of this process, those not yet waited for included, as
   /proc shows them (0 where there is no /proc). *)
let children () =
  let ppid_of pid =
    match open_in (Printf.sprintf "/proc/%s/stat" pid) with
    | exception Sys_error _ -> None
    | ch ->
      let l = try Some (input_line ch) with End_of_file -> None in
      close_in ch;
      (* "pid (comm) state ppid ...", where comm may hold spaces. *)
      match Option.bind l (fun l -> Option.map (fun i -> l, i) (String.rindex_opt l ')')) with
      | None -> None
      | Some (l, i) ->
        match String.split_on_char ' ' (String.sub l (i + 2) (String.length l - i - 2)) with
        | _state :: ppid :: _ -> int_of_string_opt ppid
        | _ -> None
  in
  match Sys.readdir "/proc" with
  | exception Sys_error _ -> 0
  | entries ->
    Array.fold_left (fun count e ->
        match int_of_string_opt e with
        | None -> count
        | Some _ -> if ppid_of e = Some (Unix.getpid ()) then count + 1 else count)
      0 entries

(* A heap budget of one byte, and every process stops itself (SIGSTOP) right
   after it has sent its last answer, instead of exiting. Each is killed as it
   retires and keeps its place until it has been waited for, so the
   processes, those not yet waited for included, are never more than [n]
   while the items are handed out; every item still has its result, and no
   process is left after [stop]. *)
let () = add_test "Forked: retired processes stay within the pool" (fun () ->
    let writer fd length answer =
      let (_, _, last) : int * int option * bool = Marshal.from_bytes answer 0 in
      CheckWorkers.default_answer_writer fd length answer;
      if last then Unix.kill (Unix.getpid ()) Sys.sigstop
    in
    CheckWorkers.set_answer_writer writer;
    Fun.protect ~finally:(fun () -> CheckWorkers.set_answer_writer CheckWorkers.default_answer_writer)
      (fun () ->
         let n = 3 and k = 60 in
         let out = Array.make k None in
         let most = ref 0 in
         let count () = most := max !most (children ()) in
         let f i = Array.length (Array.make 1000 i) + i - 999 in
         let s = CheckWorkers.Forked.start ~heap_budget:1 n f k in
         Fun.protect ~finally:(fun () -> CheckWorkers.Forked.stop s) (fun () ->
             count ();
             while CheckWorkers.Forked.poll ~wait:0.05 s (fun i v -> out.(i) <- Some v) do
               count ()
             done;
             count ());
         assert_bool (Printf.sprintf "%d processes at once, more than %d" !most n) (!most <= n);
         if Sys.file_exists "/proc/self/stat" then assert_bool "no process was seen" (!most > 0);
         assert_equal ~printer:pr_results (Array.init k (fun i -> Some (i + 1))) out;
         assert_no_child_left ()))

(* This process's GC is lazy only while processes run: never changed when
   there is no item or no process, taken back as soon as no result can come,
   and at [stop]. *)
let () = add_test "Forked: the lazy GC lasts only while processes run" (fun () ->
    let before = Gc.get () in
    let unchanged what = assert_bool what (Gc.get () = before) in
    List.iter (fun (n, k) ->
        let s = CheckWorkers.Forked.start ~lazy_gc:true n (fun i -> i) k in
        unchanged (Printf.sprintf "after a start of %d processes for %d items" n k);
        assert_bool "a result may come" (not (CheckWorkers.Forked.poll s (fun _ _ -> ())));
        unchanged "after poll";
        CheckWorkers.Forked.stop s;
        unchanged "after stop")
      [(4, 0); (0, 10)];
    let s = CheckWorkers.Forked.start ~lazy_gc:true 2 (fun i -> i) 10 in
    Fun.protect ~finally:(fun () -> CheckWorkers.Forked.stop s) (fun () ->
        assert_bool "lazy while processes run" ((Gc.get ()).Gc.space_overhead >= 1000);
        while CheckWorkers.Forked.poll ~wait:0.05 s (fun _ _ -> ()) do () done;
        unchanged "once no result can come");
    unchanged "after stop";
    let s = CheckWorkers.Forked.start ~lazy_gc:true 2 (fun i -> Unix.sleep 3600; i) 4 in
    assert_bool "lazy while processes run" ((Gc.get ()).Gc.space_overhead >= 1000);
    CheckWorkers.Forked.stop s;
    unchanged "after a stop with processes running";
    assert_no_child_left ())

let () = add_test "Forked: no item, no process" (fun () ->
    assert_equal 0 (Array.length (run_all 4 (fun _ -> assert false) 0));
    assert_no_child_left ())

let () = add_test "Forked: an item that raises has no result, the others are kept" (fun () ->
    let k = 100 in
    let f i = if i mod 7 = 3 then failwith "no" else i + 1 in
    let expected = Array.init k (fun i -> if i mod 7 = 3 then None else Some (i + 1)) in
    assert_equal ~printer:pr_results expected (run_all 4 f k))

(* A process that ends with another code, or is killed, keeps the results it
   sent: only the item it was on has none, and a fresh process takes the
   items that are left. *)
let assert_dying_process_keeps die =
  let k = 200 in
  let out = run_all 4 (fun i -> if i = 120 then die () else i) k in
  let expected = Array.init k (fun i -> if i = 120 then None else Some i) in
  assert_equal ~printer:pr_results expected out;
  assert_no_child_left ()

let () = add_test "Forked: a process that exits with code 3 keeps its results" (fun () ->
    assert_dying_process_keeps (fun () -> Unix._exit 3))

let () = add_test "Forked: a process that is killed keeps its results" (fun () ->
    assert_dying_process_keeps (fun () -> Unix.kill (Unix.getpid ()) Sys.sigkill; 0))

(* A result counts as soon as it has come, while its process works on, and
   [poll] waits for no process: item 1 never ends, yet item 0 is delivered,
   [poll] comes back at once, and [stop] kills the process. *)
let () = add_test "Forked: a result comes before its process ends, and poll waits for nothing" (fun () ->
    let s = CheckWorkers.Forked.start 1 (fun i -> if i = 1 then Unix.sleep 3600; i + 1) 2 in
    let got = ref None in
    let deadline = Unix.gettimeofday () +. 20. in
    while !got = None && Unix.gettimeofday () < deadline do
      ignore (CheckWorkers.Forked.poll ~wait:0.1 s (fun i v -> got := Some (i, v)))
    done;
    assert_equal (Some (0, 1)) !got;
    let t0 = Unix.gettimeofday () in
    let busy = CheckWorkers.Forked.poll s (fun _ _ -> assert_failure "item 1 has no result") in
    assert_bool "poll waited" (Unix.gettimeofday () -. t0 < 0.5);
    assert_bool "item 1 is still being computed" busy;
    let t0 = Unix.gettimeofday () in
    CheckWorkers.Forked.stop s;
    assert_bool "stop waited" (Unix.gettimeofday () -. t0 < 5.);
    assert_bool "poll after stop" (not (CheckWorkers.Forked.poll s (fun _ _ -> assert_failure "after stop")));
    assert_no_child_left ())

(* A process prints nothing on standard output or error, and leaves nothing
   buffered behind it. *)
let () = add_test "Forked: a process prints nothing" (fun () ->
    Format.pp_print_flush Format.std_formatter ();
    Format.pp_print_flush Format.err_formatter ();
    flush stdout;
    flush stderr;
    let out, out_w = Unix.pipe () in
    let saved_out = Unix.dup Unix.stdout in
    let saved_err = Unix.dup Unix.stderr in
    Unix.dup2 out_w Unix.stdout;
    Unix.dup2 out_w Unix.stderr;
    Unix.close out_w;
    let result =
      Fun.protect
        ~finally:(fun () ->
            Unix.dup2 saved_out Unix.stdout;
            Unix.dup2 saved_err Unix.stderr;
            Unix.close saved_out;
            Unix.close saved_err)
        (fun () -> run_all 2 (fun i -> print_string "noise"; prerr_string "noise"; i) 10)
    in
    let b = Bytes.create 16 in
    Unix.set_nonblock out;
    let got =
      try Unix.read out b 0 16
      with Unix.Unix_error ((Unix.EAGAIN | Unix.EWOULDBLOCK), _, _) -> 0
    in
    Unix.close out;
    assert_equal ~printer:string_of_int 0 got;
    assert_equal ~printer:pr_results (Array.init 10 (fun i -> Some i)) result)

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
