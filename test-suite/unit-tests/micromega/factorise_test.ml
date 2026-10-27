(* Unit test for the factorisation of a linearised polynomial by a variable
   (plugins/micromega/polynomial.ml). [LinPoly.factorise] and its linear fast
   path are gone: the indexed layer computes the quotient [a] of
   [p = x * a + b] from cached monomial entries, as [LinPoly.quotient]
   ([quotient_entries], then [of_entries]). On hand-written and on randomly
   generated vectors, linear and non-linear, the test checks that:
   - [quotient x p] is the vector that stock's general path gives, that is
     [linpol_of_pol] of the quotient of [Poly.factorise x (pol_of_linpol p)],
     rebuilt here from the monomials of [p];
   - from an empty monomial table, the two register the new monomials of the
     quotient at the same indexes, and leave the same next free index;
   - the remainder [b = p - x * a] is free of [x];
   - [is_linear_for x p] holds exactly when stock's quotient is constant.
   A wrong quotient, a monomial registered in another order, or a wrong
   linearity verdict is caught here. *)

open Utest

let log_out_ch = open_log_out_ch __FILE__

module Pol = Micromega_plugin.Polynomial
module Vect = Micromega_plugin.Vect
module NC = Micromega_core_plugin.NumCompat
module Q = NC.Q
module Monomial = Pol.Monomial
module P = Pol.Poly
module LinPoly = Pol.LinPoly

let q = Q.of_int

(* [mono_quotient x m] is the polynomial [m / x], for a monomial [m] in which
   [x] occurs. *)
let mono_quotient x m =
  Monomial.fold
    (fun y d acc ->
      let d = if Int.equal x y then d - 1 else d in
      let rec pow k acc = if k = 0 then acc else pow (k - 1) (P.product (P.variable y) acc) in
      pow d acc)
    m (P.constant Q.one)

let occurs x m = Monomial.fold (fun y _ b -> b || Int.equal x y) m false

(* Stock's general path: the quotient of [Poly.factorise x (pol_of_linpol p)],
   linearised by [linpol_of_pol]. *)
let stock_quotient x p =
  LinPoly.linpol_of_pol
    (Vect.fold
       (fun acc i c ->
         let m = LinPoly.MonT.retrieve i in
         if Q.sign c <> 0 && occurs x m then
           P.addition (P.product (P.constant c) (mono_quotient x m)) acc
         else acc)
       (P.constant Q.zero) p)

(* The vectors of the test, built by LinPoly arithmetic. *)
type shape =
  | Lin of int * (int * int) list  (** [Lin (c0, [(y, c); ...])] is [c0 + sum c * y] *)
  | Mul of shape * shape
  | Add of shape * shape

let linear cst terms =
  List.fold_left
    (fun acc (y, c) ->
      Vect.add (LinPoly.product (LinPoly.var y) (LinPoly.constant (q c))) acc)
    (LinPoly.constant (q cst)) terms

let rec build = function
  | Lin (c, terms) -> linear c terms
  | Mul (s1, s2) ->
    let p1 = build s1 in
    let p2 = build s2 in
    LinPoly.product p1 p2
  | Add (s1, s2) ->
    let p1 = build s1 in
    let p2 = build s2 in
    Vect.add p1 p2

(* [from_empty f s]: from an empty monomial table, [f] on the vector of [s],
   and the next free index after it *)
let from_empty f s =
  LinPoly.MonT.clear ();
  let a = f (build s) in
  (a, LinPoly.MonT.get_fresh ())

let ok x s =
  let a, n = from_empty (LinPoly.quotient x) s in
  let a', n' = from_empty (stock_quotient x) s in
  Vect.equal a a' && Int.equal n n'
  &&
  (LinPoly.MonT.clear ();
   let p = build s in
   let a = LinPoly.quotient x p in
   let b = Vect.add p (Vect.uminus (LinPoly.product (LinPoly.var x) a)) in
   Vect.equal a (stock_quotient x p)
   && Vect.is_null (LinPoly.quotient x b)
   && Bool.equal (LinPoly.is_linear_for x p) (Vect.is_constant (stock_quotient x p)))

let p1 = Lin (3, [ (1, 5); (2, -2); (3, 7) ]) (* 3 + 5x1 - 2x2 + 7x3 *)
let p2 = Lin (0, [ (1, 1) ])                  (* x1 *)
let p3 = Lin (4, [])                          (* a constant, no variable *)
let p4 = Lin (2, [ (2, 9); (4, -3) ])         (* independent of x1 *)

(* (x1 + x2) * (x1 + 1) + x3 *)
let nl = Add (Mul (Lin (0, [ (1, 1); (2, 1) ]), Lin (1, [ (1, 1) ])), Lin (0, [ (3, 1) ]))

(* x1^2 x2 + 2 x1 x3 - x3: the quotient by x1, x1 x2 + 2 x3, has the monomial
   x1 x2, which nothing registered before *)
let nl2 =
  Add
    ( Mul (Mul (Lin (0, [ (1, 1) ]), Lin (0, [ (1, 1) ])), Lin (0, [ (2, 1) ]))
    , Add (Mul (Lin (0, [ (1, 2) ]), Lin (0, [ (3, 1) ])), Lin (0, [ (3, -1) ])) )

(* 2 x1 - 2 x1 + x2: the x1 terms cancel *)
let cancel = Add (Lin (0, [ (1, 2) ]), Lin (0, [ (1, -2); (2, 1) ]))

let fixed =
  mk_bool_test "micromega-quotient-fixed"
    "quotient is stock's on fixed linear and non-linear vectors"
    (ok 1 p1 && ok 2 p1 && ok 3 p1 && ok 9 p1 (* x9 is absent from p1 *)
    && ok 1 p2 && ok 1 p3 && ok 1 p4 && ok 1 nl && ok 2 nl && ok 3 nl
    && ok 1 nl2 && ok 2 nl2 && ok 3 nl2 && ok 1 cancel && ok 2 cancel)

let () = Random.init 0x9e3779b9

let rand_linear () =
  let n = Random.int 8 in
  let terms = List.init n (fun _ -> (1 + Random.int 12, Random.int 21 - 10)) in
  Lin (Random.int 11 - 5, terms)

let rand_ok shape =
  let s = shape () in
  let x = 1 + Random.int 14 in
  ok x s

let rand_nonlinear () =
  match Random.int 3 with
  | 0 -> Mul (rand_linear (), rand_linear ())
  | 1 -> Add (Mul (rand_linear (), rand_linear ()), rand_linear ())
  | _ -> Mul (Mul (rand_linear (), rand_linear ()), rand_linear ())

let repeat n f =
  let rec loop i = i >= n || (f () && loop (i + 1)) in
  loop 0

let random =
  mk_bool_test "micromega-quotient-random"
    "quotient is stock's on 2000 random linear vectors"
    (repeat 2000 (fun () -> rand_ok rand_linear))

let random_nonlinear =
  mk_bool_test "micromega-quotient-random-nonlinear"
    "quotient is stock's on 500 random non-linear vectors"
    (repeat 500 (fun () -> rand_ok rand_nonlinear))

let tests = [ fixed; random; random_nonlinear ]

let _ = run_tests __FILE__ log_out_ch tests
