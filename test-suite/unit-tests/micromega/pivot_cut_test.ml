(* [WithProof.simple_pivot_cut] (plugins/micromega/polynomial.ml), which [fourier_small] uses, must
   be stock's [simple_pivot] followed by [cutting_plane]: the same constraint and the same proof,
   or [None] for both, or the same [Failure] (a strict constraint has no cut). The test compares
   them on random pairs of constraints, inequalities (strict ones too) and equalities, with
   coefficients of both signs and constants that make cuts, each constraint with
   its own hypothesis as proof, so that a proof built from the wrong multipliers is seen. *)
open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin
open Polynomial

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests
let q = NumCompat.Q.of_int

let random_cstr st i =
  let v =
    List.fold_left
      (fun v x ->
        let c = Random.State.int st 7 - 3 in
        if c = 0 then v else Vect.set x (q c) v)
      Vect.null [1; 2; 3]
  in
  let v = Vect.set 0 (q (Random.State.int st 9 - 4)) v in
  let op = match Random.State.int st 8 with 0 | 1 -> Eq | 2 -> Gt | _ -> Ge in
  WithProof.mkhyp v op i

let () = add_test "simple_pivot_cut is simple_pivot then cutting_plane" (fun () ->
  let st = Random.State.make [|8|] in
  let cuts = ref 0 and fails = ref 0 in
  for i = 0 to 20000 do
    let p1 = random_cstr st (2 * i) and p2 = random_cstr st ((2 * i) + 1) in
    let x = 1 + Random.State.int st 3 in
    let q1 = Vect.get x (WithProof.polynomial p1) in
    if NumCompat.Q.sign q1 <> 0 then begin
      (* a strict cut raises [Failure] in both: compare the exceptions too *)
      let run f = match f () with r -> Ok r | exception Failure m -> Error m in
      let stock = run (fun () -> Option.bind (WithProof.simple_pivot (q1, x) p1 p2) WithProof.cutting_plane) in
      let r = run (fun () -> WithProof.simple_pivot_cut (q1, x) p1 p2) in
      (match r with Ok (Some _) -> incr cuts | Error _ -> incr fails | Ok None -> ());
      assert_bool (Printf.sprintf "pair %d: the same result" i) (stock = r)
    end
  done;
  assert_bool "some pairs make cuts" (!cuts > 100);
  assert_bool "some pairs make strict cuts, which fail" (!fails > 10))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
