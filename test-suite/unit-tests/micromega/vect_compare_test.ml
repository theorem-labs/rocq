(* [Vect.compare] (plugins/micromega/vect.ml) is written without closures; it must return the
   integers that stock's definition returns, since the sets and maps of vectors, [WithProof.compare]
   and the sorts of the preprocessing read them. The reference below is stock's definition. The
   vectors are random, with prefixes in common, equal coefficients at other variables, equal
   variables with other coefficients, and different lengths. *)
open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let entries v = List.rev (Vect.fold (fun acc x c -> (x, c) :: acc) [] v)

(* stock's [Vect.compare], on the entries in [Vect.fold]'s order *)
let stock_compare : Vect.t -> Vect.t -> int =
  Mutils.Cmp.compare_list (fun (x1, c1) (x2, c2) ->
      Mutils.Cmp.compare_lexical
        [(fun () -> Int.compare x1 x2); (fun () -> NumCompat.Q.compare c1 c2)])
  |> fun cmp v1 v2 -> cmp (entries v1) (entries v2)

let random_vect st =
  let n = Random.State.int st 4 in
  let rec build acc x k =
    if k = 0 then List.rev acc
    else
      let x = x + 1 + Random.State.int st 2 in
      let c = NumCompat.Q.of_int (Random.State.int st 5 - 2) in
      if NumCompat.Q.sign c = 0 then build acc x (k - 1) else build ((x, c) :: acc) x (k - 1)
  in
  List.fold_left (fun v (x, c) -> Vect.set x c v) Vect.null (build [] (-1) n)

let () = add_test "compare returns stock's integers" (fun () ->
  let st = Random.State.make [|8|] in
  let vs = List.init 200 (fun _ -> random_vect st) in
  List.iter
    (fun v1 ->
      List.iter
        (fun v2 ->
          assert_equal ~printer:string_of_int ~msg:"the same integer" (stock_compare v1 v2)
            (Vect.compare v1 v2))
        vs)
    vs)

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
