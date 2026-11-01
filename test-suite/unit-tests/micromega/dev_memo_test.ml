(* [lia] and [nlia] develop each constraint with [dev_form z_spec], which they answer from a memo
   across calls (plugins/micromega/certificate.ml, "Memo of [dev_form z_spec]"). The developed
   system must be the one a call with an empty memo gives. The test develops many problems that
   share constraints, each constraint in several problems, with the memo kept from problem to
   problem, and then each problem again from an empty memo, and compares them. The constraints
   have the same few shapes with other variables, constants and operators, so many of them share
   a bucket of the memo's table; each problem has at most one constraint of each shape. It also
   checks that a constraint asked again adds nothing to the memo and that the memo stays within its
   capacity. A memo that returns another constraint's polynomial, ignores part of the key, or grows
   without bound is caught here. *)
open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin
module Mc = Micromega

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests
let var i = Mc.PEX (Mutils.CamlToCoq.positive i)
let cst n = Mc.PEc (Mutils.CamlToCoq.z n)

(* five shapes, each instantiated with variables [i], [j] and constant [k] *)
let shape s i j k =
  match s with
  | 0 -> (Mc.PEsub (Mc.PEadd (var i, Mc.PEmul (cst 2, var j)), cst k), Mc.NonStrict)
  | 1 -> (Mc.PEadd (Mc.PEsub (var i, var j), cst k), Mc.Equal)
  | 2 -> (Mc.PEsub (Mc.PEopp (var i), Mc.PEmul (cst k, var j)), Mc.Strict)
  | 3 -> (Mc.PEadd (Mc.PEpow (var i, Mc.Npos Mc.XH), Mc.PEmul (cst (-k), var j)), Mc.NonStrict)
  | _ -> (Mc.PEsub (Mc.PEmul (var i, var j), cst k), Mc.NonStrict)

(* problem [p]: one constraint of each shape, from a pool that consecutive problems share *)
let problem p =
  List.init 5 (fun s ->
      let n = (p + s) mod 37 in
      shape s (1 + (n mod 7)) (2 + (n mod 5)) (n - 11))

let depth = 10
let nproblems = 300

let () = add_test "the memo gives the system that an empty memo gives" (fun () ->
  Certificate.dev_memo_clear ();
  let warm = List.init nproblems (fun p -> Certificate.develop_z_constraints depth (problem p)) in
  assert_bool "the memo holds the constraints" (Certificate.dev_memo_size () > 0);
  List.iteri
    (fun p w ->
      Certificate.dev_memo_clear ();
      let cold = Certificate.develop_z_constraints depth (problem p) in
      assert_bool (Printf.sprintf "problem %d: the same system" p) (w = cold))
    warm)

let () = add_test "a constraint asked again adds nothing to the memo" (fun () ->
  Certificate.dev_memo_clear ();
  ignore (Certificate.develop_z_constraints depth (problem 0));
  let n = Certificate.dev_memo_size () in
  assert_equal ~msg:"one entry per distinct constraint" 5 n;
  ignore (Certificate.develop_z_constraints depth (problem 0 @ problem 0));
  assert_equal ~msg:"no new entry" n (Certificate.dev_memo_size ()))

let () = add_test "past its capacity the memo starts again" (fun () ->
  Certificate.dev_memo_clear ();
  for k = 0 to Certificate.dev_memo_capacity + 8 do
    ignore (Certificate.develop_z_constraints depth [shape 0 1 2 k])
  done;
  assert_bool "the memo holds at most its capacity"
    (Certificate.dev_memo_size () <= Certificate.dev_memo_capacity);
  let cold = (Certificate.dev_memo_clear (); Certificate.develop_z_constraints depth [shape 0 1 2 3]) in
  for k = 0 to Certificate.dev_memo_capacity + 8 do
    ignore (Certificate.develop_z_constraints depth [shape 0 1 2 k])
  done;
  assert_bool "an old constraint gets its system" (cold = Certificate.develop_z_constraints depth [shape 0 1 2 3]))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
