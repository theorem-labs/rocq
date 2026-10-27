(* [Certificate.lia] and [Certificate.nlia] answer a problem they solved before from a memo
   (plugins/micromega/certificate.ml), with what the search gave then.

   The search is a function of its depth and its problem (each call starts from an empty monomial
   table and resets the simplex's counters), so the memo returns what a new search would. The test
   checks that:
   - a problem asked again, also one built again from scratch, gets the result of its first search,
     and is answered by the memo;
   - the depth is part of the key, and so is the prover: [nlia] does not answer from [lia]'s
     results;
   - the simplex's profile ([Show Lia Profile]) counts an answer from the memo as the search it
     replaces;
   - past its capacity, the memo starts again and keeps answering right.
   A memo that ignores the depth, returns another problem's result, skips the profile, or grows
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

(* [ge e k] is e - k >= 0 *)
let ge e k = (Mc.PEsub (e, cst k), Mc.NonStrict)
let le e k = (Mc.PEsub (cst k, e), Mc.NonStrict)
let eq e k = (Mc.PEsub (e, cst k), Mc.Equal)
let add a b = Mc.PEadd (a, b)
let mul k e = Mc.PEmul (cst k, e)

(* unsatisfiable: x >= 1, x <= 0 *)
let unsat () = [ge (var 1) 1; le (var 1) 0]

(* unsatisfiable only over the integers: 2x = 2y + 1 *)
let parity () = [eq (add (mul 2 (var 1)) (mul (-2) (var 2))) 1]

(* satisfiable: x + y >= 3, x <= 1 *)
let sat () = [ge (add (var 1) (var 2)) 3; le (var 1) 1]

let depth = 10

let () = add_test "a problem asked again gets its first result from the memo" (fun () ->
  List.iter
    (fun (name, pb) ->
      let r1 = Certificate.lia depth (pb ()) in
      let h = Certificate.memo_hits () in
      let r2 = Certificate.lia depth (pb ()) in
      assert_equal ~msg:(name ^ ": the same result") r1 r2;
      assert_equal ~msg:(name ^ ": answered by the memo") (h + 1) (Certificate.memo_hits ()))
    [("unsat", unsat); ("parity", parity); ("sat", sat)])

let () = add_test "the depth and the prover are part of the key" (fun () ->
  let pb = [ge (var 7) 2; le (var 7) 1] in
  let r = Certificate.lia depth pb in
  let h = Certificate.memo_hits () in
  let r' = Certificate.lia (depth + 1) pb in
  assert_equal ~msg:"another depth is searched" h (Certificate.memo_hits ());
  assert_equal ~msg:"it finds the same certificate here" r r';
  let n = Certificate.nlia depth pb in
  assert_equal ~msg:"nlia searches" h (Certificate.memo_hits ());
  let n' = Certificate.nlia depth pb in
  assert_equal ~msg:"nlia asked again is answered by the memo" (h + 1) (Certificate.memo_hits ());
  assert_equal ~msg:"nlia's result" n n')

let counts p =
  Simplex.(p.number_of_successes, p.number_of_failures, p.success_pivots, p.failure_pivots)

let () = add_test "the profile counts an answer from the memo as a search" (fun () ->
  (* problems no other test asks, so that the first call searches *)
  let pbs () = [[ge (var 20) 5; le (add (var 20) (var 21)) 4; ge (var 21) 0]; [ge (var 22) 1; ge (var 23) 1]] in
  ignore (Simplex.get_profile_info ());
  let h = Certificate.memo_hits () in
  List.iter (fun pb -> ignore (Certificate.lia depth pb)) (pbs ());
  assert_equal ~msg:"the first calls search" h (Certificate.memo_hits ());
  let s1, f1, sp1, fp1 = counts (Simplex.get_profile_info ()) in
  assert_bool "the searches ran the integer solver" (s1 + f1 > 0);
  List.iter (fun pb -> ignore (Certificate.lia depth pb)) (pbs () @ pbs ());
  assert_equal ~msg:"the next calls are answered by the memo" (h + 4) (Certificate.memo_hits ());
  assert_equal ~msg:"twice the counts of one round of searches" (2 * s1, 2 * f1, 2 * sp1, 2 * fp1)
    (counts (Simplex.get_profile_info ())))

let () = add_test "past its capacity the memo starts again and answers right" (fun () ->
  let pb k = [ge (var 30) k; le (var 30) (k - 1)] in
  let first = Certificate.lia depth (pb 0) in
  for k = 1 to Certificate.memo_capacity + 8 do
    ignore (Certificate.lia depth (pb k))
  done;
  assert_bool "the memo holds at most its capacity" (Certificate.memo_size () <= Certificate.memo_capacity);
  let h = Certificate.memo_hits () in
  assert_equal ~msg:"an old problem gets its result" first (Certificate.lia depth (pb 0));
  assert_equal ~msg:"searched again: the memo started again" h (Certificate.memo_hits ());
  let last = Certificate.memo_capacity + 8 in
  ignore (Certificate.lia depth (pb last));
  assert_equal ~msg:"a recent problem is still in the memo" (h + 1) (Certificate.memo_hits ()))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
