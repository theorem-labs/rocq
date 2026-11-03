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

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
