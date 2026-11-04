(* The budget of lia's early-failure check (witness_list) must not depend on how loaded the
   machine is.

   Load does not change the work a call does, only the processor seconds each step of it takes,
   and not by the same factor for every step (caches, frequency and sibling hyperthreads are
   shared with other processes). The test runs the same call on the same clauses twice: once with
   the prover's steps slowed, once with the check's steps slowed, by burning processor time in the
   stubs. The work each run does is the same; its result must be the same.

   A search raises on one clause, as the prover can (a stack overflow, say), and the budget
   decides whether the call gets to that clause or the check fails it first at a later clause.
   It failed on speed-7.5 (927fa93775), whose budget counted Sys.time. *)

open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin

module Mc = Micromega

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

exception Boom

(* [spin d] burns [d] seconds of processor time. *)
let spin d =
  let t = Sys.time () in
  while Sys.time () -. t < d do () done

let var i = Mc.PEX (Mutils.CamlToCoq.positive i)
let cst n = Mc.PEc (Mutils.CamlToCoq.z n)
let ge l r = Mc.xnnormalise { Mc.flhs = l; fop = Mc.OpGe; frhs = r }
let le l r = Mc.xnnormalise { Mc.flhs = l; fop = Mc.OpLe; frhs = r }
let clause fs = List.map (fun f -> (f, ())) fs

let outcome f =
  match f () with
  | Certificate.Prf _ -> "proved"
  | Certificate.Unknown -> "fails (Unknown)"
  | Certificate.Model _ -> "fails (Model)"
  | exception Boom -> "raises the search's exception, as stock does"

(* The early-failure check. Forty clauses that lia proves, then [r], whose search raises, then [m],
   which the check knows to fail. witness_list visits the clauses from the last one of its list
   to the first. Stock (search_witness_list) raises at [r]. The real prover searches the forty
   clauses, so the call does real work; [base] gives each run its own variables, so that the
   prover's memo answers neither run. *)
let early_run ~base ~prover_spin ~check_spin () =
  let ind k = [ge (var (base + k)) (cst 0); le (var (base + k)) (cst (-1))] in
  let cheap = List.init 40 (fun k -> ind (k + 1)) in
  let r = ind 100 in
  let m = [ge (var (base + 200)) (cst 0); le (var (base + 200)) (cst 5)] in
  let r0 = List.hd r and m0 = List.hd m in
  let search fs =
    if List.hd fs == r0 then raise Boom;
    let res = Certificate.lia 10 (List.map (fun (p, o) -> (Mc.denorm p, o)) fs) in
    spin prover_spin;
    res
  in
  let early affordable fs =
    if not (affordable 0.) then None
    else begin
      spin check_spin;
      Some (List.hd fs == m0)
    end
  in
  let cnf = List.rev_map clause (cheap @ [r; m]) in
  Coq_micromega.early_witness_list ~reuse:false ~early search cnf

let () = add_test "the early-failure check decides the same under any load" (fun () ->
  let prover_slowed = outcome (early_run ~base:1000 ~prover_spin:0.002 ~check_spin:0.) in
  let check_slowed = outcome (early_run ~base:2000 ~prover_spin:0. ~check_spin:0.02) in
  Printf.printf "prover's steps slowed: %s\ncheck's steps slowed: %s\n%!" prover_slowed
    check_slowed;
  assert_equal
    ~msg:
      (Printf.sprintf "prover's steps slowed: %s; check's steps slowed: %s" prover_slowed
         check_slowed)
    prover_slowed check_slowed)

(* Exceptions at the boundary of the speculative work ([speculate] in witness_list). The early
   check and the tries of reuse run on clauses the prover may never reach, so a noncritical
   exception or a stack overflow there counts as nothing known and the call goes on as without
   them; any other critical exception (an interrupt, an exhausted memory, a failed assertion, an
   anomaly) leaves the call. Each test injects one exception at every call of the stub and checks
   that the stub was reached, so that the budget did not keep the injection from running. *)

let anomaly = try CErrors.anomaly (Pp.str "injected") with e -> e

let recovered = [("Stack_overflow", Stack_overflow); ("Failure", Failure "injected"); ("Not_found", Not_found)]

let propagated =
  [ ("Sys.Break", Sys.Break)
  ; ("Control.Timeout", Control.Timeout)
  ; ("Out_of_memory", Out_of_memory)
  ; ("Assert_failure", Assert_failure ("injected", 1, 1))
  ; ("Match_failure", Match_failure ("injected", 1, 1))
  ; ("Anomaly", anomaly) ]

(* [work n]: [n] units of [Mutils.Work], what a prover's search of that size counts; the budgets
   let the check and reuse run only in proportion to the prover's counted work. *)
let work n = for _ = 1 to n do Mutils.Work.tick () done

(* [check_injected ~base e]: 200 clauses that lia proves, an early check that raises [e]; the
   number of times the check ran, and the call's result (or its exception). *)
let check_injected ~base e =
  let ind k = [ge (var (base + k)) (cst 0); le (var (base + k)) (cst (-1))] in
  let cnf = List.init 200 (fun k -> clause (ind (k + 1))) in
  let search fs =
    work 100;
    Certificate.lia 10 (List.map (fun (p, o) -> (Mc.denorm p, o)) fs)
  in
  let ran = ref 0 in
  let early _ _ = incr ran; raise e in
  let res =
    match Coq_micromega.early_witness_list ~reuse:false ~early search cnf with
    | r -> Ok r
    | exception e' -> Error e'
  in
  (!ran, res)

(* [reuse_injected e]: [c1], which the search proves with [refute01], then [c2], which holds
   [c1]'s two formulas, so that reuse tries [refute01] on it; the checker raises [e]. The number
   of times the checker ran, and the call's result (or its exception). *)
let refute01 =
  Mc.RatProof
    (Mc.PsatzAdd (Mc.PsatzIn (Mutils.CamlToCoq.nat 0), Mc.PsatzIn (Mutils.CamlToCoq.nat 1)),
     Mc.DoneProof)

let reuse_injected e =
  let f1 = ge (var 1) (cst 1) and f2 = le (var 1) (cst 0) in
  let c1 = [f1; f2] and c2 = [ge (var 2) (cst 0); f1; f2] in
  let search _ = work 1000; Certificate.Prf refute01 in
  let ran = ref 0 in
  let checker _ _ = incr ran; raise e in
  let res =
    match
      Coq_micromega.early_witness_list ~checker ~reuse:true
        ~early:(fun _ _ -> Some false)
        search
        (List.map clause [c2; c1])
    with
    | r -> Ok r
    | exception e' -> Error e'
  in
  (!ran, res)

let is_proved = function Ok (Certificate.Prf _) -> true | _ -> false
let raised e = function Error e' -> e' == e | Ok _ -> false

let () =
  List.iteri
    (fun i (name, e) ->
      add_test ("the early check recovers from " ^ name) (fun () ->
          let ran, res = check_injected ~base:(3000 + (1000 * i)) e in
          assert_bool "the check ran" (ran > 0);
          assert_bool "the call proves its clauses, as without the check" (is_proved res));
      add_test ("reuse recovers from " ^ name) (fun () ->
          let ran, res = reuse_injected e in
          assert_bool "the checker ran" (ran > 0);
          assert_bool "the call proves its clauses, as without reuse" (is_proved res)))
    recovered

let () =
  List.iteri
    (fun i (name, e) ->
      add_test ("the early check lets " ^ name ^ " leave the call") (fun () ->
          let ran, res = check_injected ~base:(10000 + (1000 * i)) e in
          assert_bool "the check ran" (ran > 0);
          assert_bool "the injected exception leaves the call" (raised e res));
      add_test ("reuse lets " ^ name ^ " leave the call") (fun () ->
          let ran, res = reuse_injected e in
          assert_bool "the checker ran" (ran > 0);
          assert_bool "the injected exception leaves the call" (raised e res)))
    propagated

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
