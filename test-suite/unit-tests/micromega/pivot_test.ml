(* The elimination of linear equalities in lia's preprocessing (plugins/micromega/polynomial.ml,
   [WithProof.subst] and [WithProof.subst_constant]) gives stock's result.

   Stock eliminates with [iterate_pivot]: at each round it takes the first substitution of the
   system, pivots every other constraint with it ([WithProof.linear_pivot]) and simplifies the
   proof of each ([ProofFormat.simplify_prf_rule]), until no substitution is left. It is copied
   below ([stock_iterate_pivot]) over the exported [linear_pivot]. The test checks, on hand-written
   and on random systems (linear and non-linear, with proofs that are and are not simplified):
   - [subst] and [subst_constant] return stock's constraints, in stock's order, with stock's
     proofs;
   - from the same monomial table, they register the same monomials: the next free index after
     them is stock's;
   - [simplify_prf_rule] is idempotent, and its second application registers no monomial (the new
     elimination skips it on a proof it already simplified).
   A constraint pivoted with a wrong quotient, a proof left unsimplified, a constraint dropped or
   reordered, or a monomial registered in another order is caught here. *)

open Utest

let log_out_ch = open_log_out_ch __FILE__

module Pol = Micromega_plugin.Polynomial
module Vect = Micromega_plugin.Vect
module Mutils = Micromega_core_plugin.Mutils
module NC = Micromega_core_plugin.NumCompat
module Q = NC.Q
module LinPoly = Pol.LinPoly
module WP = Pol.WithProof
module PF = Pol.ProofFormat

let q = Q.of_int

(* Stock's elimination, from polynomial.ml before the change *)
let min_list = function [] -> None | e :: l -> Some (List.fold_left min e l)

let is_substitution strict wp =
  let (p, o), _ = WP.repr wp in
  let pred v = if strict then Q.compare v Q.one = 0 || Q.compare v Q.minus_one = 0 else true in
  match o with Pol.Eq -> min_list (LinPoly.search_all_linear pred p) | _ -> None

let is_constant is_int wp =
  let (c, o), _ = WP.repr wp in
  let is_integer q = Q.compare q (Q.floor q) = 0 in
  match o with
  | Pol.Ge | Pol.Gt -> None
  | Pol.Eq -> (
    match Vect.Bound.of_vect c with
    | None -> None
    | Some b ->
      if (not is_int) || is_integer Q.Notations.(b.Vect.Bound.cst // b.Vect.Bound.coeff) then
        (* [Monomial.get_var] of the registered monomial, through [LinPoly.is_variable] of its
           vector (registering it again registers nothing) *)
        LinPoly.is_variable (LinPoly.of_monomial (LinPoly.MonT.retrieve b.Vect.Bound.var))
      else None )

let stock_iterate_pivot p sys0 =
  let elim sys =
    let oeq, sys' = Mutils.extract p sys in
    match oeq with
    | None -> None
    | Some (v, pc) -> Mutils.simplify (WP.linear_pivot sys0 pc v) sys'
  in
  Mutils.iterate_until_stable elim (List.map snd (WP.sort sys0))

let stock_subst sys = stock_iterate_pivot (is_substitution true) sys
let stock_subst_constant b sys = stock_iterate_pivot (is_constant b) sys

(* Systems. A constraint is [Hyp (i, c0, [(c, x); ...], op)]: hypothesis [i], [c0 + sum c x op 0];
   [Sum], [Scale] and [Prod] combine constraints with WithProof's arithmetic, so their proofs are
   sums, products and scalings of hypotheses, which [simplify_prf_rule] rewrites. *)
type cstr =
  | Hyp of int * int * (int * int) list * Pol.op
  | Sum of cstr * cstr
  | Scale of int * cstr
  | Prod of cstr * cstr

let linear c0 terms =
  List.fold_left
    (fun v (c, x) -> Vect.add v (Vect.mul (q c) (LinPoly.var x)))
    (LinPoly.constant (q c0)) terms

let rec build = function
  | Hyp (i, c0, terms, op) -> WP.mkhyp (linear c0 terms) op i
  | Sum (a, b) -> WP.addition (build a) (build b)
  | Scale (c, a) -> WP.mul_cst (q c) (build a)
  | Prod (a, b) -> WP.product (build a) (build b)

(* [from_empty f sys]: from an empty monomial table, [f] on the constraints of [sys], and the next
   free index after it *)
let from_empty f sys =
  LinPoly.MonT.clear ();
  let r = f (List.map build sys) in
  (List.map WP.repr r, LinPoly.MonT.get_fresh ())

let same f g sys = from_empty f sys = from_empty g sys

let ok sys =
  same WP.subst stock_subst sys
  && same (WP.subst_constant true) (stock_subst_constant true) sys
  && same (WP.subst_constant false) (stock_subst_constant false) sys

(* x1 = x2 + 1, x2 = 2 x3 - 1, x1 + x3 >= 4, x4 >= 0 (no substitution touches it), 2 x2 - x4 >= 1 *)
let s1 =
  [ Hyp (0, -1, [(1, 1); (-1, 2)], Pol.Eq)
  ; Hyp (1, 1, [(1, 2); (-2, 3)], Pol.Eq)
  ; Hyp (2, -4, [(1, 1); (1, 3)], Pol.Ge)
  ; Hyp (3, 0, [(1, 4)], Pol.Ge)
  ; Hyp (4, -1, [(2, 2); (-1, 4)], Pol.Ge) ]

(* proofs that are sums and scalings, a constant equation (x5 = 3), and a constraint whose proof
   is a sum but that no substitution touches *)
let s2 =
  [ Sum (Hyp (0, -1, [(1, 1)], Pol.Eq), Hyp (1, 0, [(-1, 2)], Pol.Eq))
  ; Scale (3, Hyp (2, -6, [(1, 1); (1, 2)], Pol.Ge))
  ; Hyp (3, -3, [(1, 5)], Pol.Eq)
  ; Sum (Hyp (4, 0, [(1, 6)], Pol.Ge), Scale (2, Hyp (5, 1, [(1, 7)], Pol.Ge)))
  ; Hyp (6, 2, [(-1, 5); (1, 2)], Pol.Ge) ]

(* non-linear: (x1 - 1) * (x2 + 2) >= 0, with x1 = x3 and x2 = x4 - x3 *)
let s3 =
  [ Prod (Hyp (0, -1, [(1, 1)], Pol.Ge), Hyp (1, 2, [(1, 2)], Pol.Ge))
  ; Hyp (2, 0, [(1, 1); (-1, 3)], Pol.Eq)
  ; Hyp (3, 0, [(1, 2); (-1, 4); (1, 3)], Pol.Eq)
  ; Hyp (4, 0, [(1, 3)], Pol.Ge) ]

(* no substitution at all *)
let s4 = [ Hyp (0, 1, [(2, 1)], Pol.Ge); Hyp (1, 0, [(3, 2); (1, 1)], Pol.Eq) ]

let fixed = mk_bool_test "subst_fixed" "subst and subst_constant give stock's result" (List.for_all ok [s1; s2; s3; s4; []])

let () = Random.init 0x2545f491

let rand_terms nvars =
  List.init (1 + Random.int 3) (fun _ -> (Random.int 7 - 3, 1 + Random.int nvars))

let rec rand_cstr nvars i depth =
  match if depth = 0 then 0 else Random.int 6 with
  | 0 | 1 | 2 ->
    let op = match Random.int 3 with 0 -> Pol.Eq | 1 -> Pol.Ge | _ -> Pol.Gt in
    (* an equation is often a substitution: a variable with coefficient 1 or -1 *)
    let terms =
      if op = Pol.Eq && Random.bool () then ((if Random.bool () then 1 else -1), 1 + Random.int nvars) :: rand_terms nvars
      else rand_terms nvars
    in
    Hyp (i, Random.int 9 - 4, terms, op)
  | 3 -> Sum (rand_cstr nvars i (depth - 1), rand_cstr nvars (i + 100) (depth - 1))
  | 4 -> Scale (1 + Random.int 3, rand_cstr nvars i (depth - 1))
  | _ ->
    (* a product of two inequalities: [WithProof.product] multiplies two [Ge] or [Gt] *)
    let ge j = Hyp (j, Random.int 5 - 2, rand_terms nvars, Pol.Ge) in
    Prod (ge i, ge (i + 200))

let rand_sys nonlinear =
  let nvars = 3 + Random.int 6 in
  List.init (2 + Random.int 14) (fun i -> rand_cstr nvars i (if nonlinear then 2 else 1))

(* [WithProof] raises [InvalidProof] (or [Failure]) on some combinations: both sides must then
   raise *)
let raised = ref 0 and ran = ref 0 and pivoted = ref 0

(* the constraints of [sys] in [sort]'s order, without elimination *)
let unchanged sys = List.map snd (WP.sort sys)

let ok_or_raise sys =
  let run f = try Ok (from_empty f sys) with e -> Error (Printexc.to_string e) in
  incr ran;
  (match run stock_subst with
   | Error _ -> incr raised
   | Ok (r, _) -> if r <> fst (from_empty unchanged sys) then incr pivoted);
  run WP.subst = run stock_subst
  && run (WP.subst_constant true) = run (stock_subst_constant true)
  && run (WP.subst_constant false) = run (stock_subst_constant false)

let repeat n f =
  let rec loop i = i >= n || (f () && loop (i + 1)) in
  loop 0

let random = mk_bool_test "subst_random" "subst and subst_constant give stock's result on random linear systems"
    (repeat 3000 (fun () -> ok_or_raise (rand_sys false)))

let random_nonlinear = mk_bool_test "subst_random_nonlinear" "subst and subst_constant give stock's result on random non-linear systems"
    (repeat 1000 (fun () -> ok_or_raise (rand_sys true)))

(* Proof terms for the idempotence of [simplify_prf_rule]: every constructor, constants among 0,
   1, -1, 2 and 1/2, and vectors over registered monomials, constant and not, some with a zero
   coefficient ([Vect.mul_add] leaves one). *)
let rand_vect vars =
  let v () = Vect.mul (q (Random.int 5 - 2)) (List.nth vars (Random.int (List.length vars))) in
  match Random.int 5 with
  | 0 -> LinPoly.constant (q (Random.int 5 - 2))
  | 1 -> Vect.mul_add Q.zero (v ()) Q.one (v ())
  | _ -> Vect.add (v ()) (v ())

let rand_q () = match Random.int 5 with 0 -> Q.zero | 1 -> Q.one | 2 -> Q.minus_one | 3 -> q 2 | _ -> Q.Notations.(Q.one // q 2)

let rec rand_prf vars depth =
  let sub () = rand_prf vars (depth - 1) in
  match if depth = 0 then Random.int 6 else Random.int 13 with
  | 0 -> PF.Hyp (Random.int 4)
  | 1 -> PF.Def (Random.int 4)
  | 2 -> PF.Ref (Random.int 4)
  | 3 -> PF.Cst (rand_q ())
  | 4 -> PF.Zero
  | 5 -> PF.Square (rand_vect vars)
  | 6 -> PF.MulC (rand_vect vars, sub ())
  | 7 -> PF.Gcd (Q.to_bigint (q (2 + Random.int 3)), sub ())
  | 8 -> PF.MulPrf (sub (), sub ())
  | 9 | 10 -> PF.AddPrf (sub (), sub ())
  | 11 -> PF.CutPrf (sub ())
  | _ -> if Random.bool () then PF.LetPrf (sub (), sub ()) else PF.Annot ("a", sub ())

(* most random systems must not raise, or the comparisons above would test little *)
let mostly_ran = mk_bool_test "subst_random_ran" "most random systems do not raise, and many are changed by the elimination"
    (!raised * 10 < !ran && !pivoted * 3 > !ran)

let idempotent () =
  LinPoly.MonT.clear ();
  (* x1, x2, x3 and x1 * x2 *)
  let x i = LinPoly.var i in
  let vars = [x 1; x 2; x 3; LinPoly.product (x 1) (x 2); LinPoly.constant Q.one] in
  let p = rand_prf vars (1 + Random.int 4) in
  let s = PF.simplify_prf_rule p in
  let before = LinPoly.MonT.get_fresh () in
  let s' = PF.simplify_prf_rule s in
  let after = LinPoly.MonT.get_fresh () in
  s = s' && after = before + 1

let idempotence = mk_bool_test "simplify_idempotent" "simplify_prf_rule is idempotent and its second application registers nothing"
    (repeat 20000 idempotent)

let tests = [ fixed; random; random_nonlinear; mostly_ran; idempotence ]

let _ = run_tests __FILE__ log_out_ch tests
