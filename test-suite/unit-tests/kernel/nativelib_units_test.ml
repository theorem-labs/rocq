(* coqchk's -j workers are forked from one process, write their units in
   its directory of generated code ([Nativelib.force_temp_dir]), and
   inherit one copy of [Filename]'s random state. While native conversion
   is on, the names of their units must still differ: a worker forked
   after another one made many units must get a fresh name. *)

open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

(* Runs [f] in a child process, and tells whether it returned. The child
   ends with [Unix._exit], as a worker does, so that it does not remove the
   shared directory. *)
let in_child f =
  match Unix.fork () with
  | 0 -> Unix._exit (try f (); 0 with _ -> 1)
  | pid ->
    match snd (Unix.waitpid [] pid) with
    | Unix.WEXITED 0 -> true
    | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> false

let () = add_test "workers forked from one process get different unit names" (fun () ->
  Nativecode.set_native_vm_conversion true;
  Nativelib.force_temp_dir ();
  (* The main process of coqchk draws from [Filename]'s random state
     before it forks, when it decides a cast itself. *)
  Sys.remove (Filename.temp_file "nativelib_units_test" "");
  assert_bool "the first worker could not name its units"
    (in_child (fun () -> for _ = 1 to 1100 do ignore (Nativelib.get_ml_filename ()) done));
  assert_bool "a worker forked after it could not name its unit"
    (in_child (fun () -> ignore (Nativelib.get_ml_filename ()))))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
