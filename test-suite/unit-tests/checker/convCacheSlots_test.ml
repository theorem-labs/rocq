(* The compile slots of the checker's native conversion
   (kernel/nativelib.ml, "Compile slots").

   What the tests check:
   - a slot's owner record that is incomplete or unreadable counts as
     held: a second taker does not take the slot;
   - two live processes never hold one slot, and a slot whose holder has
     exited without starting a compiler is taken over;
   - a holder that releases its slot while a taker reads the record
     still leaves one holder at a time;
   - an error on the slot files other than contention ends the wait at
     once, rather than retrying for ever;
   - a compile dies with the process that started it, and its slot frees;
   - a compile interrupted by an exception is killed by its holder, with
     its supervisor unable to do it, and its slot released;
   - a compile ends even when its supervisor never gets the compiler's
     SIGCHLD.

   The compiler is a shell script standing in for [ocamlfind]: it writes
   its pid to a file, sleeps, and marks that it was not killed. *)

open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let temp_dir = Filename.concat (Filename.get_temp_dir_name ()) "convCacheSlots_test"

let rec remove_tree f =
  if Sys.file_exists f then
    if Sys.is_directory f then begin
      (try Unix.chmod f 0o700 with Unix.Unix_error _ -> ());
      Array.iter (fun g -> remove_tree (Filename.concat f g)) (Sys.readdir f);
      Unix.rmdir f
    end else Sys.remove f

let () =
  remove_tree temp_dir;
  Unix.mkdir temp_dir 0o700;
  let me = Unix.getpid () in
  at_exit (fun () -> if Unix.getpid () = me then try remove_tree temp_dir with _ -> ());
  (* The stand-in compiler ignores its arguments; the flags only need an
     include directory to exist. *)
  Nativelib.include_dirs := [temp_dir];
  Nativelib.get_load_paths := (fun () -> [])

let fresh_dir name =
  let d = Filename.concat temp_dir name in
  Unix.mkdir d 0o700;
  d

let with_slots dir cap f =
  let saved = !Nativelib.slots in
  Nativelib.slots := Some (dir, cap);
  Fun.protect ~finally:(fun () -> Nativelib.slots := saved) f

(* The slot files of a directory: [slot.<k>.<g>], not the private files
   nor the child records. *)
let slot_files dir =
  List.filter (fun f ->
      String.length f > 5 && String.equal (String.sub f 0 5) "slot."
      && not (Filename.check_suffix f ".child")
      && List.length (String.split_on_char '.' f) = 3)
    (Array.to_list (Sys.readdir dir))

exception Gave_up

(* Try to take a slot, giving up after [polls] waits. *)
let acquire_within polls =
  let n = ref 0 in
  match Nativelib.acquire_slot ~poll:(fun () -> incr n; if !n > polls then raise Gave_up) () with
  | s -> `Acquired s
  | exception Gave_up -> `Waited

let pid_alive pid = match Unix.kill pid 0 with
  | () -> true
  | exception Unix.Unix_error (Unix.ESRCH, _, _) -> false
  | exception Unix.Unix_error _ -> true

let write_file f s = let ch = open_out_bin f in output_string ch s; close_out ch

let read_int f =
  match open_in f with
  | exception Sys_error _ -> None
  | ch -> let s = (try input_line ch with End_of_file -> "") in close_in ch; int_of_string_opt (String.trim s)

(* A stand-in for [ocamlfind]: writes its pid to $SLOT_TEST_PIDFILE, sleeps
   [seconds], writes $SLOT_TEST_PIDFILE.done, then exits with [code]. A
   [.done] file says that nothing killed it. *)
let slow_compiler name ~seconds ~code =
  let f = Filename.concat temp_dir name in
  write_file f (Printf.sprintf
                  "#!/bin/sh\necho $$ > \"$SLOT_TEST_PIDFILE\"\nsleep %d\ntouch \"$SLOT_TEST_PIDFILE.done\"\nexit %d\n"
                  seconds code);
  Unix.chmod f 0o755;
  f

let wait_for_file f ~seconds =
  let t0 = Unix.gettimeofday () in
  while not (Sys.file_exists f) && Unix.gettimeofday () -. t0 < seconds do Unix.sleepf 0.02 done;
  Sys.file_exists f

let wait_until_dead pid ~seconds =
  let t0 = Unix.gettimeofday () in
  while pid_alive pid && Unix.gettimeofday () -. t0 < seconds do Unix.sleepf 0.05 done;
  not (pid_alive pid)

(* Reap the child [pid], killing it if it has not exited after [seconds]. *)
let reap_within pid ~seconds =
  let t0 = Unix.gettimeofday () in
  let rec go () =
    match Unix.waitpid [Unix.WNOHANG] pid with
    | 0, _ ->
      if Unix.gettimeofday () -. t0 < seconds then (Unix.sleepf 0.02; go ())
      else begin
        (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
        (try ignore (Unix.waitpid [] pid) with Unix.Unix_error _ -> ());
        false
      end
    | _ -> true
    | exception Unix.Unix_error _ -> true
  in
  go ()

(* Open the write end of a fifo once a reader is there: [ENXIO] until
   then. This is how a test meets a process that is inside the [open] of
   a slot file. *)
let open_fifo_write f ~seconds =
  let t0 = Unix.gettimeofday () in
  let rec go () =
    match Unix.openfile f Unix.[O_WRONLY; O_NONBLOCK] 0 with
    | fd -> Some fd
    | exception Unix.Unix_error ((Unix.ENXIO | Unix.ENOENT), _, _) ->
      if Unix.gettimeofday () -. t0 > seconds then None
      else (Unix.sleepf 0.01; go ())
  in
  go ()

(* What a process writes on [fd], or [None] after [seconds]. *)
let read_within fd ~seconds =
  match Unix.select [fd] [] [] seconds with
  | exception Unix.Unix_error _ -> None
  | [], _, _ -> None
  | _ ->
    let b = Bytes.create 64 in
    match Unix.read fd b 0 64 with
    | 0 -> None
    | n -> Some (String.trim (Bytes.sub_string b 0 n))
    | exception Unix.Unix_error _ -> None

(** {6 Records} *)

let () = add_test "a slot whose owner record is incomplete or unreadable is held" (fun () ->
  let dir = fresh_dir "incomplete" in
  with_slots dir 1 (fun () ->
      List.iter (fun (what, content) ->
          (* What a holder leaves while it has created its slot file and
             not yet written its pid, or a garbled record. *)
          write_file (Filename.concat dir "slot.0.0") content;
          (match acquire_within 25 with
           | `Acquired s -> Nativelib.release_slot s;
             assert_failure ("a slot whose record is " ^ what ^ " was taken")
           | `Waited -> ());
          Sys.remove (Filename.concat dir "slot.0.0"))
        ["empty", ""; "garbled", "not a pid"];
      (* With the record gone, the slot is free. *)
      match acquire_within 25 with
      | `Acquired s -> Nativelib.release_slot s
      | `Waited -> assert_failure "a free slot was not taken"))

let () = add_test "two live processes never hold one slot; an exited holder's slot is taken over" (fun () ->
  let dir = fresh_dir "two" in
  with_slots dir 1 (fun () ->
      let r, w = Unix.pipe () in
      match Unix.fork () with
      | 0 ->
        Unix.close r;
        let code = match Nativelib.acquire_slot () with
          | Some _ -> ignore (Unix.write_substring w "x" 0 1); Unix.sleepf 1.5; 0
          | None -> 1
        in
        Unix._exit code      (* exits holding the slot, as a killed worker would *)
      | pid ->
        Unix.close w;
        let b = Bytes.create 1 in
        assert_equal ~msg:"the first holder took its slot" 1 (Unix.read r b 0 1);
        Unix.close r;
        (match acquire_within 10 with
         | `Acquired s -> Nativelib.release_slot s; assert_failure "a held slot was taken"
         | `Waited -> ());
        ignore (Unix.waitpid [] pid);
        (match acquire_within 50 with
         | `Acquired s -> Nativelib.release_slot s
         | `Waited -> assert_failure "the slot of an exited holder was not taken over");
        assert_bool "this process still holds a slot" (CList.is_empty !Nativelib.held_slots)))

(* The release that races a taker's read of the record, driven step by
   step: the slot file is a fifo, so the taker's own [open] of it inside
   the record's read is the meeting point. This process opens the write
   end (the taker is now inside the read), removes the file as a holder
   that releases does, and only then writes a record naming a process
   that is gone.

   A taker that counts the slot free here takes generation 1 while
   generation 0 is missing, and the next taker takes generation 0: two
   live holders of one slot with a cap of one. *)
let () = add_test "a release while a taker reads the record never gives one slot two holders" (fun () ->
  let dir = fresh_dir "release-race" in
  let fifo = Filename.concat dir "slot.0.0" in
  Unix.mkfifo fifo 0o600;
  let gone = match Unix.fork () with
    | 0 -> Unix._exit 0
    | p -> ignore (Unix.waitpid [] p); p                     (* a pid that is dead *)
  in
  let name_r, name_w = Unix.pipe () in
  let go_r, go_w = Unix.pipe () in
  match Unix.fork () with
  | 0 ->
    Unix.close name_r; Unix.close go_w;
    let code =
      with_slots dir 1 (fun () ->
          match acquire_within 300 with
          | `Acquired (Some s) ->
            let n = Filename.basename s in
            ignore (Unix.write_substring name_w (n ^ "\n") 0 (String.length n + 1) : int);
            let b = Bytes.create 1 in
            ignore (Unix.read go_r b 0 1 : int);        (* hold it until told *)
            Nativelib.release_slot (Some s); 0
          | `Acquired None -> 2
          | `Waited -> 1
          | exception _ -> 3)
    in
    Unix._exit code
  | taker ->
    Unix.close name_w; Unix.close go_r;
    let finish () =
      (try ignore (Unix.write_substring go_w "x" 0 1 : int) with Unix.Unix_error _ -> ());
      (try Unix.close go_w with Unix.Unix_error _ -> ());
      (* A taker that came to the fifo too late is still blocked in its
         [open]: it is killed rather than waited for. *)
      ignore (reap_within taker ~seconds:10. : bool)
    in
    Fun.protect ~finally:finish (fun () ->
        (match open_fifo_write fifo ~seconds:30. with
         | None -> assert_failure "the taker never read the slot's record"
         | Some w ->
           Unix.unlink fifo;                            (* the holder releases *)
           let s = string_of_int gone in
           ignore (Unix.write_substring w s 0 (String.length s) : int);
           Unix.close w);
        let got = read_within name_r ~seconds:30. in
        Unix.close name_r;
        assert_equal ~msg:"the slot the taker took" ~printer:(fun s -> s)
          "slot.0.0" (Option.default "none" got);
        (* The taker holds its slot; with a cap of one, nobody else may. *)
        with_slots dir 1 (fun () ->
            match acquire_within 10 with
            | `Acquired s -> Nativelib.release_slot s;
              assert_failure "a second process took a slot while the first held one"
            | `Waited -> ())))

(** {6 Errors} *)

let () = add_test "an error on the slot files other than contention ends the wait" (fun () ->
  let expect_error what dir =
    with_slots dir 1 (fun () ->
        match acquire_within 25 with
        | exception Unix.Unix_error _ -> ()
        | `Waited -> assert_failure ("the wait for a slot in " ^ what ^ " retried instead of failing")
        | `Acquired _ -> assert_failure ("a slot was taken in " ^ what))
  in
  expect_error "a missing directory" (Filename.concat temp_dir "missing");
  let ro = fresh_dir "readonly" in
  Unix.chmod ro 0o500;
  expect_error "a read-only directory" ro)

(** {6 Compilers} *)

(* A compile belongs to the process that started it: coqchk, or the
   worker that holds the slot. When that process dies, the compile and
   everything it started die with it, so that no compiler keeps a core
   and coqchk's output busy after the check is gone (a terminal's
   Ctrl-C, [timeout], or [CheckWorkers.abort]). The slot frees with
   them. *)
let () = add_test "a killed holder's compile dies with it, and its slot frees" (fun () ->
  let dir = fresh_dir "killed" in
  let pidfile = Filename.concat dir "compiler.pid" in
  let compiler = slow_compiler "slow30.sh" ~seconds:30 ~code:1 in
  match Unix.fork () with
  | 0 ->
    Unix.putenv "OCAMLFIND" compiler;
    Unix.putenv "SLOT_TEST_PIDFILE" pidfile;
    with_slots dir 1 (fun () ->
        try ignore (Nativelib.compile_part_files ~base:(Filename.concat dir "Killed") [| "", "" |])
        with _ -> ());
    Unix._exit 0
  | holder ->
    assert_bool "the compiler did not start" (wait_for_file pidfile ~seconds:10.);
    let compiler_pid = Option.get (read_int pidfile) in
    Unix.kill holder Sys.sigkill;
    ignore (Unix.waitpid [] holder);
    let died = wait_until_dead compiler_pid ~seconds:1. in
    (* Do not leave a 30 s compiler behind if it did not. *)
    if not died then
      (try Unix.kill (- compiler_pid) Sys.sigkill
       with Unix.Unix_error _ -> (try Unix.kill compiler_pid Sys.sigkill with Unix.Unix_error _ -> ()));
    assert_bool "the compile outlived the holder that started it" died;
    with_slots dir 1 (fun () ->
        match acquire_within 100 with
        | `Acquired s -> Nativelib.release_slot s
        | `Waited -> assert_failure "the slot of the dead holder was not freed"))

(* The interrupted compile must be stopped by the process that ran it
   ([kill_compiler] in [run_command]), not by its supervisor. Closing the
   gate would also stop it (the test above), so the alarm handler first
   forks a keeper that holds a copy of the gate's write end, as any child
   would: the supervisor then never sees end-of-file, and only the
   holder's own kill can end the compile before its 20 s are up. *)
let () = add_test "an interrupted compile is killed by its holder, and its slot released" (fun () ->
  let dir = fresh_dir "interrupted" in
  let pidfile = Filename.concat dir "compiler.pid" in
  let keeperfile = Filename.concat dir "keeper.pid" in
  let compiler = slow_compiler "slow20.sh" ~seconds:20 ~code:1 in
  match Unix.fork () with
  | 0 ->
    Unix.putenv "OCAMLFIND" compiler;
    Unix.putenv "SLOT_TEST_PIDFILE" pidfile;
    let code =
      with_slots dir 1 (fun () ->
          Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ ->
              (match Unix.fork () with
               | 0 -> (try Unix.sleepf 60. with _ -> ()); Unix._exit 0
               | keeper -> write_file keeperfile (string_of_int keeper));
              raise Exit));
          ignore (Unix.alarm 1);
          match Nativelib.compile_part_files ~base:(Filename.concat dir "Interrupted") [| "", "" |] with
          | _ -> 1                                  (* not interrupted *)
          | exception Exit ->
            ignore (Unix.alarm 0);
            match read_int pidfile with
            | None -> 5
            | Some p ->
              (* The compiler is the supervisor's child, so the process
                 that reaps it is init; it dies with the group the kill
                 reaches, and goes in the moment after. *)
              if not (wait_until_dead p ~seconds:5.) then 2
              else if Sys.file_exists (pidfile ^ ".done") then 8
              else if not (CList.is_empty !Nativelib.held_slots) then 3
              else if not (CList.is_empty (slot_files dir)) then 4
              else 0
          | exception _ -> 6)
    in
    Unix._exit code
  | child ->
    let code = match snd (Unix.waitpid [] child) with
      | Unix.WEXITED n -> n
      | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 7
    in
    (* Do not leave the keeper or the stand-in running if the test failed. *)
    let kill p = try Unix.kill (- p) Sys.sigkill with _ -> (try Unix.kill p Sys.sigkill with _ -> ()) in
    Option.iter kill (read_int keeperfile);
    Option.iter kill (read_int pidfile);
    assert_bool "the keeper of the gate was not started" (Sys.file_exists keeperfile);
    assert_equal ~printer:(function
        | 0 -> "killed and released" | 1 -> "the compile was not interrupted"
        | 2 -> "the compiler was alive after its slot was released" | 3 -> "a slot was still held"
        | 4 -> "a slot file was left" | 5 -> "the compiler never started" | 6 -> "another exception"
        | 8 -> "the compiler ran to its end: its holder did not kill it"
        | n -> "child status " ^ string_of_int n)
      0 code)

(* OCaml runs a signal handler only at a safe point, so a SIGCHLD that
   lands just before the supervisor's [select] enters the kernel writes
   its wake-up byte only after [select] returns. A holder with SIGCHLD
   blocked makes that happen on every compile: its supervisors inherit the
   mask, and no handler runs at all. The compiles must still end, through
   the supervisor's own periodic look at its child. *)
let () = add_test "a compile ends when its supervisor misses the compiler's SIGCHLD" (fun () ->
  let dir = fresh_dir "nosigchld" in
  let pidfile = Filename.concat dir "compiler.pid" in
  let compiler = slow_compiler "quick0.sh" ~seconds:0 ~code:0 in
  match Unix.fork () with
  | 0 ->
    Unix.putenv "OCAMLFIND" compiler;
    Unix.putenv "SLOT_TEST_PIDFILE" pidfile;
    ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigchld] : int list);
    let code =
      with_slots dir 1 (fun () ->
          (* The interfaces, one part and the link: three compiles. *)
          match Nativelib.compile_part_files ~base:(Filename.concat dir "NoSigchld") [| "", "" |] with
          | _ -> 0
          | exception _ -> 1)
    in
    Unix._exit code
  | holder ->
    (* If the supervisor waits for a wake-up that never comes, the holder
       never ends: it is killed, which also ends its supervisors (the
       gate closes). *)
    let ended = reap_within holder ~seconds:20. in
    assert_bool "the compiles never ended: a supervisor waited for a SIGCHLD it missed" ended)

let () = add_test "a compiler named without a directory is found on the PATH" (fun () ->
  let dir = fresh_dir "bare" in
  let pidfile = Filename.concat dir "compiler.pid" in
  let compiler = slow_compiler "quick.sh" ~seconds:0 ~code:0 in
  match Unix.fork () with
  | 0 ->
    Unix.putenv "PATH" (Filename.dirname compiler ^ ":" ^ Option.default "" (Sys.getenv_opt "PATH"));
    Unix.putenv "OCAMLFIND" (Filename.basename compiler);
    Unix.putenv "SLOT_TEST_PIDFILE" pidfile;
    let code =
      with_slots dir 1 (fun () ->
          match Nativelib.compile_part_files ~base:(Filename.concat dir "Bare") [| "", "" |] with
          | _ -> 0
          | exception _ -> 1)
    in
    Unix._exit code
  | child ->
    let code = match snd (Unix.waitpid [] child) with
      | Unix.WEXITED n -> n
      | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 7
    in
    assert_bool "the compiler did not run" (Sys.file_exists pidfile);
    assert_equal ~printer:(function
        | 0 -> "compiled" | 1 -> "the compile failed" | n -> "child status " ^ string_of_int n)
      0 code)

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
