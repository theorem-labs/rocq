(* The GC policy that [Coqinit.init_ocaml] installs (sysinit/coqinit.ml).

   A proof check allocates tens of gigabytes of short-lived terms and then ends, so what the policy
   costs is major-collector work -- lane R2's fast set pays about 1.7 s of marking and sweeping per
   file at [space_overhead = 200] -- and how much of that allocation the minor heap promotes and
   how much of the shared cache each process takes for itself. The constants below are the ones the
   lane measured (reports/lever9a.md), with [space_overhead] held down to what a compile process can
   answer under the address-space ceilings misc/print-assumptions-memo-limits.sh pins: a change of
   either is a change of the lane's wall or of what that test allows, so the test pins them.

   The policy changes no result: OCaml's collector decides when values move and are freed, not what
   any function computes. The second test pins the other half of [init_gc]: when the user sets
   OCAMLRUNPARAM, rocq installs nothing and the user's values stand.

   Both measurements are taken here, before the tests run, because the environment must not change
   while a test runs and the first one needs OCAMLRUNPARAM unset. *)
open OUnit
open Utest

(* The values of sysinit/coqinit.ml's [set_gc_policy] and [set_gc_best_fit]. *)
let lane_minor_heap_size = 2 * 1024 * 1024
let lane_space_overhead = 1600
let best_fit = 2

(* OCAMLRUNPARAM is not set when the test-suite runs a unit test; if it were, [init_gc] would install
   nothing and the first test would fail with a value that looks like a wrong policy, so the test says
   which of the two it is. *)
let runparam_set = Sys.getenv_opt "OCAMLRUNPARAM" <> None

let installed =
  let () = Coqinit.init_ocaml () in
  Gc.get ()

let user_space_overhead = 137
let user_minor_heap_size = 1 lsl 18

let kept =
  let () = Gc.set {(Gc.get ()) with Gc.space_overhead = user_space_overhead
                                  ; Gc.minor_heap_size = user_minor_heap_size} in
  let () = Unix.putenv "OCAMLRUNPARAM" "v=0" in
  let () = Coqinit.init_ocaml () in
  Gc.get ()

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let () = add_test "init_ocaml installs the lane's GC policy" (fun () ->
  assert_equal ~printer:string_of_int ~msg:"minor_heap_size"
    lane_minor_heap_size installed.Gc.minor_heap_size;
  assert_equal ~printer:string_of_int ~msg:"space_overhead"
    lane_space_overhead installed.Gc.space_overhead;
  assert_equal ~printer:string_of_int ~msg:"allocation_policy"
    best_fit installed.Gc.allocation_policy)

let () = add_test "the first test ran with OCAMLRUNPARAM unset" (fun () ->
  assert_bool "OCAMLRUNPARAM was set, so init_gc installed nothing" (not runparam_set))

let () = add_test "OCAMLRUNPARAM keeps the user's values" (fun () ->
  assert_equal ~printer:string_of_int ~msg:"space_overhead"
    user_space_overhead kept.Gc.space_overhead;
  assert_equal ~printer:string_of_int ~msg:"minor_heap_size"
    user_minor_heap_size kept.Gc.minor_heap_size)

let () = run_tests __FILE__ (open_log_out_ch __FILE__) !tests
