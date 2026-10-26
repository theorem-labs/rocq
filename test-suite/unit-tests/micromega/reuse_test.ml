(* Certificate reuse across the clauses of one lia goal (flag Micromega Reuse).

   Each test runs lia's witness_list on hand-built clauses. A stub replaces the search of one
   clause: it answers from a table and records the clauses it was asked, in order. witness_list
   searches the clauses from the last one to the first, as without reuse. With reuse, a goal that
   succeeds gets the certificates of the search without reuse, and a goal fails exactly when it
   fails without reuse.

   In each test of reuse, reuse proves a clause that is not the last one visited, so the clauses
   are asked in another order with reuse off: with reuse, that clause is searched after the
   clauses visited after it, in the second pass, or not at all when a later search fails. A test
   of what keeps a certificate off a clause visits another clause after that one, so that a wrong
   reuse there changes the order too. *)

open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin

module Mc = Micromega

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

(* Formulas in the normal form that lia's CNF produces: [ge a b] is a - b >= 0. *)
let var i = Mc.PEX (Mutils.CamlToCoq.positive i)
let cst n = Mc.PEc (Mutils.CamlToCoq.z n)
let ge l r = Mc.xnnormalise { Mc.flhs = l; fop = Mc.OpGe; frhs = r }
let le l r = Mc.xnnormalise { Mc.flhs = l; fop = Mc.OpLe; frhs = r }

let x = var 1
let y = var 2
let w = var 3
let x_ge_1 = ge x (cst 1)
let x_le_0 = le x (cst 0)
let x_le_m5 = le x (cst (-5))
let y_ge_0 = ge y (cst 0)
let y_le_m1 = le y (cst (-1))
let w_ge_0 = ge w (cst 0)
let w_le_m1 = le w (cst (-1))

(* [refute i j]: hypotheses [i] and [j] of the clause add up to a negative constant. *)
let hyp i = Mc.PsatzIn (Mutils.CamlToCoq.nat i)
let refute i j = Mc.RatProof (Mc.PsatzAdd (hyp i, hyp j), Mc.DoneProof)

(* [wrong i] cites hypothesis [i] and proves nothing: a search never returns it. *)
let wrong i = Mc.RatProof (hyp i, Mc.DoneProof)

(* [ex_refute i j] is [refute i j] under an ExProof step. The checker of ExProof puts three
   hypotheses in front of the clause. *)
let ex_refute i j = Mc.ExProof (Mutils.CamlToCoq.positive 1, refute (i + 3) (j + 3))

let c_small = [x_ge_1; x_le_0]
let c_big = [y_ge_0; w_ge_0; x_ge_1; x_le_0]
let c_mid = [y_ge_0; x_ge_1; x_le_0]
(* contains x_ge_1, but not x_le_0 *)
let c_other = [x_ge_1; x_le_m5]
let c_y = [y_ge_0; y_le_m1]
let c_xy = [x_ge_1; x_le_0; y_ge_0; y_le_m1]
(* contains y_ge_0, but not y_le_m1, and no formula on x *)
let c_w = [w_ge_0; y_ge_0; w_le_m1]
(* [ind k]: a clause on variable [10 + k] alone, that [refute 0 1] proves; [inds n] is
   [ind 1; ...; ind n]. No certificate of another clause applies to it. *)
let ind k = [ge (var (10 + k)) (cst 0); le (var (10 + k)) (cst (-1))]
let inds n = List.init n (fun k -> ind (k + 1))

(* [run ~reuse answers cnf] runs witness_list with a clock that the test controls: each read
   of the clock is [tick] after the read before it, and a search takes 1 more. witness_list
   reads the clock after each visit of a clause in the first pass, and after each search there,
   so each visit adds [tick] to the time of the tries of stored certificates and each search
   adds [1 + tick] to the time of the searches. With the default [tick = 0.], the tries take no
   time, and the time budget of reuse never stops them. *)
let run ~reuse ?(tick = 0.) answers cnf =
  let now = ref 0. in
  let clock () = now := !now +. tick; !now in
  let asked = ref [] in
  let search fs =
    asked := fs :: !asked;
    now := !now +. 1.;
    match List.assoc_opt fs answers with
    | Some prf -> Certificate.Prf prf
    | None -> Certificate.Unknown
  in
  let clause fs = List.map (fun f -> (f, ())) fs in
  let res = Coq_micromega.lia_witness_list ~clock ~reuse search (List.map clause cnf) in
  (List.rev !asked, res)

(* [run ~reuse:true] and [run ~reuse:false] give the same result *)
let assert_as_search answers cnf res =
  assert_equal ~msg:"the result is the one without reuse" (snd (run ~reuse:false answers cnf)) res

let () = add_test "the hand-built certificates prove their clauses" (fun () ->
  List.iter (fun (name, cl, prf) -> assert_bool name (Mc.zChecker cl prf))
    [ ("c_small, refute 0 1", c_small, refute 0 1)
    ; ("c_big, refute 3 2", c_big, refute 3 2)
    ; ("c_big, refute 2 3", c_big, refute 2 3)
    ; ("c_mid, refute 2 1", c_mid, refute 2 1)
    ; ("c_mid, refute 1 2", c_mid, refute 1 2)
    ; ("c_other, refute 1 0", c_other, refute 1 0)
    ; ("c_other, refute 0 1", c_other, refute 0 1)
    ; ("c_y, refute 0 1", c_y, refute 0 1)
    ; ("c_xy, refute 0 1", c_xy, refute 0 1)
    ; ("c_w, refute 0 2", c_w, refute 0 2)
    ; ("c_small, ex_refute 0 1", c_small, ex_refute 0 1)
    ; ("c_big, ex_refute 2 3", c_big, ex_refute 2 3)
    ; ("ind 9, refute 0 1", ind 9, refute 0 1) ];
  assert_bool "c_small's certificate needs renumbering on c_big"
    (not (Mc.zChecker c_big (refute 0 1)));
  assert_bool "wrong 0 does not prove c_other" (not (Mc.zChecker c_other (wrong 0))))

let () = add_test "a goal proved with reuse gets the search's certificates" (fun () ->
  let answers = [(c_small, refute 0 1); (c_big, refute 3 2); (c_other, refute 1 0)] in
  let cnf = [c_other; c_big; c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"reuse proves c_big, c_other is searched, then c_big is searched"
    [c_small; c_other; c_big] asked;
  assert_equal ~msg:"c_big gets its search's certificate, not c_small's renumbered"
    (Certificate.Prf [refute 1 0; refute 3 2; refute 0 1]) res;
  assert_as_search answers cnf res)

let () = add_test "a certificate is not tried on a clause that lacks a formula it cites" (fun () ->
  let answers =
    [(c_small, refute 0 1); (c_big, refute 3 2); (c_other, refute 1 0); (c_w, refute 0 2)]
  in
  let cnf = [c_w; c_other; c_big; c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"reuse proves c_big; c_other, which lacks x_le_0, is searched before c_w"
    [c_small; c_other; c_w; c_big] asked;
  assert_equal ~msg:"every clause gets its search's certificate"
    (Certificate.Prf [refute 0 2; refute 1 0; refute 3 2; refute 0 1]) res;
  assert_as_search answers cnf res)

let () = add_test "a certificate the checker rejects on a clause is not used there" (fun () ->
  let answers =
    [ (c_small, wrong 0); (c_y, refute 0 1); (c_xy, refute 0 1); (c_other, refute 1 0)
    ; (c_w, refute 0 2) ]
  in
  let cnf = [c_w; c_other; c_xy; c_y; c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal
    ~msg:"reuse proves c_xy; the checker rejects wrong 0 on c_other, searched before c_w"
    [c_small; c_y; c_other; c_w; c_xy] asked;
  assert_equal ~msg:"every clause gets its search's certificate"
    (Certificate.Prf [refute 0 2; refute 1 0; refute 0 1; refute 0 1; wrong 0]) res;
  assert_as_search answers cnf res)

let () = add_test "a clause that reuse proves and its search fails on makes the goal fail" (fun () ->
  let answers = [(c_small, refute 0 1); (c_y, refute 0 1); (c_w, refute 0 2)] in
  let cnf = [c_w; c_xy; c_y; c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"reuse proves c_xy, c_w is searched, then the search of c_xy fails"
    [c_small; c_y; c_w; c_xy] asked;
  assert_equal ~msg:"the goal fails" Certificate.Unknown res;
  assert_as_search answers cnf res)

let () = add_test "a failing search ends a goal with reuse at once" (fun () ->
  let answers = [(c_small, refute 0 1)] in
  let asked, res = run ~reuse:true answers [c_other; c_big; c_small] in
  assert_equal ~msg:"reuse proves c_big, the search of c_other fails" [c_small; c_other] asked;
  assert_equal ~msg:"the goal fails" Certificate.Unknown res;
  let asked, res = run ~reuse:false answers [c_other; c_big; c_small] in
  assert_equal ~msg:"without reuse, the search of c_big fails" [c_small; c_big] asked;
  assert_equal ~msg:"the goal fails without reuse too" Certificate.Unknown res)

let () = add_test "a certificate with an ExProof step is stored, renumbered and reused" (fun () ->
  let answers = [(c_small, ex_refute 0 1); (c_big, refute 3 2); (c_other, refute 1 0)] in
  let cnf = [c_other; c_big; c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"ex_refute 2 3 proves c_big, c_other is searched, then c_big is searched"
    [c_small; c_other; c_big] asked;
  assert_equal ~msg:"every clause gets its search's certificate"
    (Certificate.Prf [refute 1 0; refute 3 2; ex_refute 0 1]) res;
  assert_as_search answers cnf res)

let () = add_test "the second pass searches only the clauses that reuse proved" (fun () ->
  let answers =
    [(c_small, refute 0 1); (c_big, refute 3 2); (c_other, refute 1 0); (c_mid, refute 2 1)]
  in
  let cnf = [c_mid; c_other; c_big; c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal
    ~msg:"reuse proves c_big and c_mid; the second pass searches them, in the order of the first"
    [c_small; c_other; c_big; c_mid] asked;
  assert_equal ~msg:"every clause gets its search's certificate"
    (Certificate.Prf [refute 2 1; refute 1 0; refute 3 2; refute 0 1]) res;
  assert_as_search answers cnf res)

let () = add_test "a clause tries at most eight stored certificates" (fun () ->
  let answers =
    [(c_small, refute 0 1); (c_big, refute 3 2); (c_y, refute 0 1)]
    @ List.map (fun c -> (c, refute 0 1)) (inds 8)
  in
  (* c_small's certificate, stored first, is the only one that applies to c_big *)
  let cnf = [c_y; c_big] @ List.rev (inds 7) @ [c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"as the eighth stored certificate, it proves c_big"
    ((c_small :: inds 7) @ [c_y; c_big]) asked;
  assert_as_search answers cnf res;
  let cnf = [c_y; c_big] @ List.rev (inds 8) @ [c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"as the ninth, it is not tried, and c_big is searched"
    ((c_small :: inds 8) @ [c_big; c_y]) asked;
  assert_as_search answers cnf res)

let () = add_test "the certificate that proves a clause moves to the front" (fun () ->
  let answers =
    [(c_small, refute 0 1); (c_mid, refute 2 1); (c_big, refute 3 2); (c_y, refute 0 1)]
    @ List.map (fun c -> (c, refute 0 1)) (inds 8)
  in
  (* c_small's certificate is the eighth stored when it proves c_mid, then ind 8 is searched *)
  let cnf = [c_y; c_big; ind 8; c_mid] @ List.rev (inds 7) @ [c_small] in
  let asked, res = run ~reuse:true answers cnf in
  assert_equal ~msg:"it is the second of nine on c_big, which it proves"
    ((c_small :: inds 8) @ [c_y; c_mid; c_big]) asked;
  assert_as_search answers cnf res)

let () = add_test "the tries of a goal take at most 1/16 of its search time" (fun () ->
  let answers =
    [(c_small, refute 0 1); (c_big, refute 3 2); (c_other, refute 1 0); (c_mid, refute 2 1)]
  in
  let cnf = [c_mid; c_other; c_big; c_small] in
  (* tick 0.05: before c_mid, the time outside the searches is 0.15 and the two searches took
     2.1. 0.15 is within 1/16 of the search time only with the mean search, 1.05, that c_big
     adds, as the second pass searches it. *)
  let asked, res = run ~reuse:true ~tick:0.05 answers cnf in
  assert_equal ~msg:"reuse proves c_big, then c_mid, as the clause that reuse proved counts"
    [c_small; c_other; c_big; c_mid] asked;
  assert_as_search answers cnf res;
  (* tick 0.1: after c_small, the time outside the searches is 0.1, more than 1.1 / 16, and it
     grows faster than the budget *)
  let asked, res = run ~reuse:true ~tick:0.1 answers cnf in
  assert_equal ~msg:"no clause tries reuse: each is searched once, as without reuse"
    [c_small; c_big; c_other; c_mid] asked;
  assert_as_search answers cnf res)

let () = add_test "with reuse off, every clause is searched" (fun () ->
  let answers = [(c_small, refute 0 1); (c_big, refute 3 2); (c_other, refute 1 0)] in
  let asked, res = run ~reuse:false answers [c_other; c_big; c_small] in
  assert_equal ~msg:"every clause is searched once, the last one first"
    [c_small; c_big; c_other] asked;
  assert_equal ~msg:"every clause gets its search's certificate"
    (Certificate.Prf [refute 1 0; refute 3 2; refute 0 1]) res)

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
