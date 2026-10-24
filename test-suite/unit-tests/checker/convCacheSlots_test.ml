(* The compile slots of the checker's native conversion
   (kernel/nativelib.ml, "Compile slots").

   What the tests check:
   - a slot's owner record that is incomplete or unreadable counts as
     held: a second taker does not take the slot;
   - two live processes never hold one slot, and a slot whose holder has
     exited without starting a compiler is taken over;
   - an error on the slot files other than contention ends the wait at
     once, rather than retrying for ever;
   - a slot stays held while the compile of a holder that was killed still
     runs, and frees when that compile ends;
   - a compile interrupted by an exception is killed and reaped before its
     slot is released, for the interface and link compiles too.

   The compiler is a shell script standing in for [ocamlfind]: it writes
   its pid to a file and sleeps. *)

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
   [seconds], then exits with [code]. *)
let slow_compiler name ~seconds ~code =
  let f = Filename.concat temp_dir name in
  write_file f (Printf.sprintf "#!/bin/sh\necho $$ > \"$SLOT_TEST_PIDFILE\"\nsleep %d\nexit %d\n" seconds code);
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

let () = add_test "a slot stays held while the compile of a killed holder runs" (fun () ->
  let dir = fresh_dir "killed" in
  let pidfile = Filename.concat dir "compiler.pid" in
  let compiler = slow_compiler "slow3.sh" ~seconds:3 ~code:1 in
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
    assert_bool "the compiler died with its holder" (pid_alive compiler_pid);
    with_slots dir 1 (fun () ->
        (match acquire_within 10 with
         | `Acquired s -> Nativelib.release_slot s;
           assert_failure "the slot of a killed holder was taken while its compiler ran"
         | `Waited -> ());
        assert_bool "the compiler did not end" (wait_until_dead compiler_pid ~seconds:10.);
        match acquire_within 100 with
        | `Acquired s -> Nativelib.release_slot s
        | `Waited -> assert_failure "the slot was not freed when the compiler ended"))

let () = add_test "an interrupted compile is killed and reaped before its slot is released" (fun () ->
  let dir = fresh_dir "interrupted" in
  let pidfile = Filename.concat dir "compiler.pid" in
  let compiler = slow_compiler "slow20.sh" ~seconds:20 ~code:1 in
  match Unix.fork () with
  | 0 ->
    Unix.putenv "OCAMLFIND" compiler;
    Unix.putenv "SLOT_TEST_PIDFILE" pidfile;
    let code =
      with_slots dir 1 (fun () ->
          Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit));
          ignore (Unix.alarm 1);
          match Nativelib.compile_part_files ~base:(Filename.concat dir "Interrupted") [| "", "" |] with
          | _ -> 1                                  (* not interrupted *)
          | exception Exit ->
            ignore (Unix.alarm 0);
            match read_int pidfile with
            | None -> 5
            | Some p ->
              if pid_alive p then 2                   (* the compiler outlived its slot *)
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
    (* Do not leave the stand-in running if the test failed. *)
    Option.iter (fun p -> try Unix.kill (- p) Sys.sigkill with _ -> (try Unix.kill p Sys.sigkill with _ -> ()))
      (read_int pidfile);
    assert_equal ~printer:(function
        | 0 -> "killed, reaped and released" | 1 -> "the compile was not interrupted"
        | 2 -> "the compiler was alive after its slot was released" | 3 -> "a slot was still held"
        | 4 -> "a slot file was left" | 5 -> "the compiler never started" | 6 -> "another exception"
        | n -> "child status " ^ string_of_int n)
      0 code)

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
