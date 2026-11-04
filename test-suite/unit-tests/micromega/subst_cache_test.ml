(* [WithProof.subst] answers a system that differs from the previous call's in one inequality from
   that call's rounds (plugins/micromega/polynomial.ml, "[subst] from the previous call"). The
   result must be the one that a call without the previous call gives. The test runs families of
   systems through [subst], each after the previous one, and compares each result with [subst] of
   the same system after [subst_cache_clear ()]. The families:
   - an inequality replaced by another one, at the same place or at another place of the sorted
     system, or by one the substitutions do not touch, or that cannot be pivoted;
   - an equality replaced by an inequality, or by another equality (which changes the rounds);
   - the same system over other variables, whose vectors are equal but whose monomials are not;
   - a replaced inequality over a variable no other constraint has (which renumbers the monomials);
   - a non-linear replacement;
   - an inequality removed, down to the empty system, and added.
   It also checks that the families are answered from the previous call ([subst_cache_hits]), so
   that the comparison is not only between two full computations. *)
open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin
module Mc = Micromega

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests
let var i = Mc.PEX (Mutils.CamlToCoq.positive i)
let cst n = Mc.PEc (Mutils.CamlToCoq.z n)
let add a b = Mc.PEadd (a, b)
let sub a b = Mc.PEsub (a, b)
let mul k e = Mc.PEmul (cst k, e)

(* [ge e] is e >= 0, [eq e] is e = 0 *)
let ge e = (e, Mc.NonStrict)
let gt e = (e, Mc.Strict)
let eq e = (e, Mc.Equal)

let depth = 10

(* the system of [pb], as [lia] develops it, then [subst] of it *)
let subst pb =
  let sys = Certificate.develop_z_constraints depth pb in
  Polynomial.WithProof.subst sys

let cold pb =
  Polynomial.WithProof.subst_cache_clear ();
  subst pb

(* a chain of substitutions x1 = x2 + 1, x2 = x3 - 2, x3 = 2.x4 + x5, x5 = x6, around inequalities *)
let base o =
  [ ge (sub (var (o + 1)) (cst 3))
  ; eq (sub (var (o + 1)) (add (var (o + 2)) (cst 1)))
  ; ge (sub (add (var (o + 4)) (var (o + 6))) (cst 2))
  ; eq (sub (var (o + 2)) (sub (var (o + 3)) (cst 2)))
  ; ge (sub (cst 40) (add (var (o + 1)) (var (o + 5))))
  ; eq (sub (var (o + 3)) (add (mul 2 (var (o + 4))) (var (o + 5))))
  ; ge (sub (mul 3 (var (o + 6))) (var (o + 2)))
  ; eq (sub (var (o + 5)) (var (o + 6)))
  ; ge (sub (cst 7) (var (o + 4))) ]

(* [base] with its constraint [i] replaced by [c] *)
let replace i c l = List.mapi (fun j c' -> if j = i then c else c') l

let check_family name pbs =
  (* each problem after the previous one, then each one alone *)
  Polynomial.WithProof.subst_cache_clear ();
  let warm = List.map subst pbs in
  List.iteri
    (fun k (pb, w) -> assert_bool (Printf.sprintf "%s %d: the same result" name k) (w = cold pb))
    (List.combine pbs warm)

let () = add_test "an inequality replaced by another" (fun () ->
  let o = 0 in
  let h = Polynomial.WithProof.subst_cache_hits () in
  check_family "ineq"
    (base o
     :: List.map (fun c -> replace 6 c (base o))
          [ ge (sub (mul 3 (var (o + 6))) (var (o + 1)))
          ; ge (sub (var (o + 4)) (cst 1))
          ; ge (sub (cst 5) (add (var (o + 3)) (var (o + 1))))
          ; gt (sub (mul 5 (var (o + 2))) (var (o + 6)))
          ; ge (sub (add (var (o + 1)) (var (o + 2))) (add (var (o + 3)) (var (o + 4)))) ]);
  assert_bool "answered from the previous call" (Polynomial.WithProof.subst_cache_hits () > h))

let () = add_test "an equality replaced" (fun () ->
  let o = 0 in
  check_family "eq"
    (base o
     :: [ replace 3 (ge (sub (var (o + 2)) (var (o + 3)))) (base o)
        ; replace 3 (eq (sub (var (o + 2)) (add (var (o + 3)) (cst 5)))) (base o)
        ; replace 5 (eq (sub (var (o + 3)) (var (o + 4)))) (base o)
        ; base o ]))

let () = add_test "the same vectors over other variables" (fun () ->
  check_family "renamed"
    [ base 0
    ; replace 6 (ge (sub (mul 3 (var 6)) (var 1))) (base 0)
    ; base 10
    ; replace 6 (ge (sub (mul 3 (var 16)) (var 11))) (base 10)
    ; [eq (sub (var 2) (var 1)); ge (sub (var 1) (cst 3)); ge (sub (cst 1) (var 2))]
    ; [eq (sub (var 8) (var 7)); ge (sub (var 7) (cst 3)); ge (sub (cst 1) (var 8))]
    ; [eq (sub (var 2) (var 1)); ge (sub (var 1) (cst 3)); ge (sub (cst 1) (var 2))] ])

let () = add_test "a new variable, a non-linear constraint" (fun () ->
  check_family "new"
    [ base 0
    ; replace 0 (ge (sub (var 9) (cst 3))) (base 0)
    ; replace 6 (ge (sub (var 9) (var 2))) (base 0)
    ; replace 6 (ge (sub (Mc.PEmul (var 2, var 4)) (var 6))) (base 0)
    ; replace 6 (ge (sub (Mc.PEmul (var 1, var 1)) (cst 2))) (base 0)
    ; base 0 ])

let () = add_test "an inequality removed or added" (fun () ->
  check_family "removed"
    [ [ge (sub (var 1) (cst 3))]
    ; []
    ; [ge (sub (var 1) (cst 3))]
    ; [eq (sub (var 2) (var 1)); ge (sub (var 1) (cst 3))]
    ; [eq (sub (var 2) (var 1)); ge (sub (cst 5) (var 1))]
    ; [eq (sub (var 2) (var 1))]
    ; [eq (sub (var 2) (var 1)); ge (sub (cst 1) (var 2))] ])

let () = add_test "a replaced inequality, then another one removed, from the previous calls" (fun () ->
  (* the second and third systems differ from the one before in one inequality, at the same
     place (so with the same hypothesis numbers), so both are answered from the previous call:
     the third needs the counts of the inequality that the second added *)
  let e = eq (sub (var 2) (var 1)) in
  let a = ge (sub (var 1) (cst 3)) and b = ge (sub (cst 9) (var 2)) and c = ge (sub (cst 7) (var 1)) in
  Polynomial.WithProof.subst_cache_clear ();
  let pbs = [[e; a; b]; [e; c; b]; [e; c]] in
  let r0 = subst (List.nth pbs 0) in
  let h = Polynomial.WithProof.subst_cache_hits () in
  let r1 = subst (List.nth pbs 1) in
  let r2 = subst (List.nth pbs 2) in
  assert_equal ~msg:"both answered from the previous call" (h + 2) (Polynomial.WithProof.subst_cache_hits ());
  List.iteri
    (fun k (pb, w) -> assert_bool (Printf.sprintf "system %d: the same result" k) (w = cold pb))
    (List.combine pbs [r0; r1; r2]))

let () = add_test "a new inequality whose proof registers a monomial" (fun () ->
  (* [simplify_prf_rule] of [MulC (x2, MulC (x1, Hyp 7))] registers x1.x2. A call that registers
     it from [replay] must not leave a record that lets the same system skip that registration;
     the index the next monomial gets shows it. *)
  let pb = base 0 in
  let with_new () =
    let sys = Certificate.develop_z_constraints depth pb in
    let prf =
      Polynomial.ProofFormat.(AddPrf (Hyp 6, MulC (Polynomial.LinPoly.var 2, MulC (Polynomial.LinPoly.var 1, Hyp 7))))
    in
    let c =
      Polynomial.WithProof.of_cstr
        ({Polynomial.coeffs = Polynomial.LinPoly.var 1; op = Polynomial.Ge; cst = NumCompat.Q.of_int 2}, prf)
    in
    let r = Polynomial.WithProof.subst (List.mapi (fun i c' -> if i = 6 then c else c') sys) in
    (r, Polynomial.LinPoly.var 50)
  in
  Polynomial.WithProof.subst_cache_clear ();
  ignore (subst pb);
  let h = Polynomial.WithProof.subst_cache_hits () in
  let r2 = with_new () in
  assert_equal ~msg:"answered from the previous call" (h + 1) (Polynomial.WithProof.subst_cache_hits ());
  let r3 = with_new () in
  Polynomial.WithProof.subst_cache_clear ();
  let cold = with_new () in
  assert_bool "the second call: stock's result and table" (r2 = cold);
  assert_bool "the third call: stock's result and table" (r3 = cold))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
