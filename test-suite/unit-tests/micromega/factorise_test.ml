(* Unit test for [Polynomial.LinPoly.factorise]
   (plugins/micromega/polynomial.ml), in particular its linear fast path.
   It checks the defining equation  [p = x * a + b]  with [b] independent of
   [x], for the factored pair  [(a, b) = factorise x p],  on hand-written and
   on randomly generated vectors (linear and non-linear). A wrong fast path
   breaks the reconstruction and is caught here. *)

open Utest

let log_out_ch = open_log_out_ch __FILE__

module Poly = Micromega_plugin.Polynomial
module Vect = Micromega_plugin.Vect
module NC = Micromega_core_plugin.NumCompat
module Q = NC.Q
module LinPoly = Poly.LinPoly

let () = LinPoly.MonT.clear ()

let q = Q.of_int

(* [reconstruct x (a, b) = x * a + b] in LinPoly (monomial) arithmetic. *)
let reconstruct x (a, b) =
  Vect.add (LinPoly.product (LinPoly.var x) a) b

(* A factorisation is correct when it rebuilds [p] and the remainder [b] is
   free of [x] (factorising [b] again by [x] yields a null quotient). *)
let ok x p =
  let (a, b) = LinPoly.factorise x p in
  let (a', _) = LinPoly.factorise x b in
  Vect.equal (reconstruct x (a, b)) p && Vect.is_null a'

(* Build the linear polynomial  c0 + sum_i ci * y_i  from an assoc list. *)
let linear cst terms =
  List.fold_left
    (fun acc (y, c) ->
      Vect.add (LinPoly.product (LinPoly.var y) (LinPoly.constant (q c))) acc)
    (LinPoly.constant (q cst)) terms

let p1 = linear 3 [ (1, 5); (2, -2); (3, 7) ] (* 3 + 5x1 - 2x2 + 7x3 *)
let p2 = linear 0 [ (1, 1) ]                   (* x1 *)
let p3 = LinPoly.constant (q 4)                (* a constant, no variable *)
let p4 = linear 2 [ (2, 9); (4, -3) ]          (* independent of x1 *)

(* non-linear: (x1 + x2) * (x1 + 1) + x3 *)
let nl =
  Vect.add
    (LinPoly.product (linear 0 [ (1, 1); (2, 1) ]) (linear 1 [ (1, 1) ]))
    (linear 0 [ (3, 1) ])

let fixed =
  mk_bool_test "micromega-factorise-fixed"
    "factorise reconstructs fixed linear and non-linear vectors"
    (ok 1 p1 && ok 2 p1 && ok 3 p1 && ok 9 p1 (* x9 is absent from p1 *)
    && ok 1 p2 && ok 1 p3 && ok 1 p4 && ok 1 nl && ok 2 nl && ok 3 nl)

let () = Random.init 0x9e3779b9

let rand_linear () =
  let n = Random.int 8 in
  let terms = List.init n (fun _ -> (1 + Random.int 12, Random.int 21 - 10)) in
  linear (Random.int 11 - 5) terms

let rand_ok () =
  let p = rand_linear () in
  let x = 1 + Random.int 14 in
  ok x p

let random =
  mk_bool_test "micromega-factorise-random"
    "factorise reconstructs 2000 random linear vectors"
    (let rec loop i = i >= 2000 || (rand_ok () && loop (i + 1)) in
     loop 0)

let tests = [ fixed; random ]

let _ = run_tests __FILE__ log_out_ch tests
