(* The CNF conversion with its pair checks computed once (Cnf_memo) gives the conversion's result.

   [Coq_micromega.cnfZ] and [Coq_micromega.cnfQ] must equal [Micromega.cnfZ] and [Micromega.cnfQ],
   CNF and trace, and [Zcheck_oracle.z_tauto_checker] must equal [Zchecker.zTautoChecker], on
   formulas that make the conversion distribute disjunctions: the same atoms occur many times, also
   negated and in an iff, and many pairs of literals add up to an unsatisfiable constraint, so the
   pair checks drop clauses. The formulas are random, from a fixed seed, over a few variables and
   small constants, so that pairs repeat. *)

open OUnit
open Utest
open Micromega_core_plugin
open Micromega_plugin

module Mc = Micromega
module Zc = Zchecker

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

(* Formulas built once and translated to each extraction. An atom is [sum c_i x_i op k]. *)
type op = Eq | Neq | Le | Ge | Lt | Gt
type atom = (int * int) list * op * int
type form =
  | Atom of atom
  | True
  | False
  | And of form * form
  | Or of form * form
  | Not of form
  | Impl of form * form
  | Iff of form * form

let ops = [| Eq; Neq; Le; Ge; Lt; Gt |]

let random_atom () : atom =
  let var () = 1 + Random.int 3 in
  let coef () = Random.int 5 - 2 in
  let terms = if Random.bool () then [(coef (), var ())] else [(coef (), var ()); (coef (), var ())] in
  (terms, ops.(Random.int 6), Random.int 7 - 3)

(* A pool of atoms that the formulas draw from, so that atoms recur. *)
let random_form pool =
  let rec go d =
    if d = 0 || Random.int 5 = 0 then
      match Random.int 12 with
      | 0 -> True
      | 1 -> False
      | _ -> Atom pool.(Random.int (Array.length pool))
    else
      match Random.int 6 with
      | 0 -> And (go (d - 1), go (d - 1))
      | 1 | 2 -> Or (go (d - 1), go (d - 1))
      | 3 -> Not (go (d - 1))
      | 4 -> Impl (go (d - 1), go (d - 1))
      | _ -> Iff (go (d - 1), go (d - 1))
  in
  go (2 + Random.int 3)

let random_case () =
  let pool = Array.init (2 + Random.int 5) (fun _ -> random_atom ()) in
  random_form pool

(* Translation to Micromega's formulas, with a tag per atom occurrence. *)
let mc_op = function
  | Eq -> Mc.OpEq | Neq -> Mc.OpNEq | Le -> Mc.OpLe | Ge -> Mc.OpGe | Lt -> Mc.OpLt | Gt -> Mc.OpGt

let mc_formula cst (terms, op, k) =
  let term (c, x) = Mc.PEmul (Mc.PEc (cst c), Mc.PEX (Mutils.CamlToCoq.positive x)) in
  let lhs = List.fold_left (fun acc t -> Mc.PEadd (acc, term t)) (term (List.hd terms)) (List.tl terms) in
  {Mc.flhs = lhs; fop = mc_op op; frhs = Mc.PEc (cst k)}

let mc_tform cst f =
  let tag = ref 0 in
  let rec go = function
    | Atom a -> incr tag; Mc.A (Mc.IsProp, mc_formula cst a, !tag)
    | True -> Mc.TT Mc.IsProp
    | False -> Mc.FF Mc.IsProp
    | And (a, b) -> Mc.AND (Mc.IsProp, go a, go b)
    | Or (a, b) -> Mc.OR (Mc.IsProp, go a, go b)
    | Not a -> Mc.NOT (Mc.IsProp, go a)
    | Impl (a, b) -> Mc.IMPL (Mc.IsProp, go a, None, go b)
    | Iff (a, b) -> Mc.IFF (Mc.IsProp, go a, go b)
  in
  go f

let mc_z = Mutils.CamlToCoq.z
let mc_q n = {Mc.qnum = Mutils.CamlToCoq.z n; qden = Mc.XH}

(* Translation to Zchecker's formulas and certificates. *)
let rec zc_pos n = if n = 1 then Zc.XH else if n land 1 = 0 then Zc.XO (zc_pos (n / 2)) else Zc.XI (zc_pos (n / 2))
let zc_z n = if n = 0 then Zc.Z0 else if n > 0 then Zc.Zpos (zc_pos n) else Zc.Zneg (zc_pos (-n))
let rec zc_nat n = if n = 0 then Zc.O else Zc.S (zc_nat (n - 1))

let zc_op = function
  | Eq -> Zc.OpEq | Neq -> Zc.OpNEq | Le -> Zc.OpLe | Ge -> Zc.OpGe | Lt -> Zc.OpLt | Gt -> Zc.OpGt

let zc_formula (terms, op, k) =
  let term (c, x) = Zc.PEmul (Zc.PEc (zc_z c), Zc.PEX (zc_pos x)) in
  let lhs = List.fold_left (fun acc t -> Zc.PEadd (acc, term t)) (term (List.hd terms)) (List.tl terms) in
  {Zc.flhs = lhs; fop = zc_op op; frhs = Zc.PEc (zc_z k)}

let rec zc_bform = function
  | Atom a -> Zc.A (Zc.IsProp, zc_formula a, Zc.Tt)
  | True -> Zc.TT Zc.IsProp
  | False -> Zc.FF Zc.IsProp
  | And (a, b) -> Zc.AND (Zc.IsProp, zc_bform a, zc_bform b)
  | Or (a, b) -> Zc.OR (Zc.IsProp, zc_bform a, zc_bform b)
  | Not a -> Zc.NOT (Zc.IsProp, zc_bform a)
  | Impl (a, b) -> Zc.IMPL (Zc.IsProp, zc_bform a, None, zc_bform b)
  | Iff (a, b) -> Zc.IFF (Zc.IsProp, zc_bform a, zc_bform b)

(* Certificates that refute a clause when two of its first four literals add up to a negative
   constant, or one literal is a negative constant; most random ones refute nothing. *)
let random_proof () =
  let hyp () = Zc.PsatzIn (zc_nat (Random.int 4)) in
  let w = if Random.bool () then Zc.PsatzAdd (hyp (), hyp ()) else hyp () in
  Zc.RatProof (w, Zc.DoneProof)

let random_proofs () = List.init (Random.int 4) (fun _ -> random_proof ())

let cases = 3000

let () = add_test "cnfZ is Micromega.cnfZ" (fun () ->
  Random.init 4217;
  for i = 1 to cases do
    let f = mc_tform mc_z (random_case ()) in
    if Coq_micromega.cnfZ Mc.IsProp f <> Mc.cnfZ Mc.IsProp f then
      assert_failure (Printf.sprintf "case %d: the CNF or its trace differ" i)
  done)

let () = add_test "cnfQ is Micromega.cnfQ" (fun () ->
  Random.init 4218;
  for i = 1 to cases do
    let f = mc_tform mc_q (random_case ()) in
    if Coq_micromega.cnfQ Mc.IsProp f <> Mc.cnfQ Mc.IsProp f then
      assert_failure (Printf.sprintf "case %d: the CNF or its trace differ" i)
  done)

(* The checker's result depends on its CNF: a clause it does not drop needs a certificate. Both
   results occur among the cases. *)
let () = add_test "z_tauto_checker is Zchecker.zTautoChecker" (fun () ->
  Random.init 4219;
  let accepted = ref 0 in
  for i = 1 to cases do
    let f = zc_bform (random_case ()) in
    let w = random_proofs () in
    let b = Zc.zTautoChecker f w in
    if b then incr accepted;
    if Zcheck_oracle.z_tauto_checker f w <> b then
      assert_failure (Printf.sprintf "case %d: the checkers disagree" i)
  done;
  assert_bool "some cases are accepted" (!accepted > cases / 20);
  assert_bool "some cases are refused" (!accepted < cases - cases / 20))

(* A case that needs the pair checks: x <= 0 <-> y >= 1 implies (x <= 0 /\ y >= 1) \/ (x >= 1 /\
   y <= 0), the formula of lia's proof of that goal. Every clause of its CNF has two literals that
   add up to a negative constant, so the empty list of certificates proves it. *)
let iff_case =
  let x_le_0 = Atom ([(1, 1)], Le, 0) and y_ge_1 = Atom ([(1, 2)], Ge, 1) in
  let x_ge_1 = Atom ([(1, 1)], Ge, 1) and y_le_0 = Atom ([(1, 2)], Le, 0) in
  Impl (Iff (x_le_0, y_ge_1), Or (And (x_le_0, y_ge_1), And (x_ge_1, y_le_0)))

(* A conjunction of 3000 disjunctions of distinct atoms: 6000 literals and two checks per
   disjunction. Rows long enough for every identifier would take about 9 MB; the memo stops
   storing past its budget (1 MB plus 64 bytes per check stored), and the CNF is the same. *)
let () = add_test "cnfZ is Micromega.cnfZ past the memory budget" (fun () ->
  let n = 3000 in
  let atom x op k = Atom ([(1, x)], op, k) in
  let rec conj i = let d = Or (atom i Ge 1, atom (i + n) Le 0) in if i = 1 then d else And (d, conj (i - 1)) in
  let f = mc_tform mc_z (conj n) in
  let cnf, tr = Coq_micromega.cnfZ Mc.IsProp f in
  assert_equal ~msg:"the clauses" (fst (Mc.cnfZ Mc.IsProp f)) cnf;
  assert_equal ~msg:"the trace" (snd (Mc.cnfZ Mc.IsProp f)) tr;
  assert_equal ~msg:"one clause per disjunction" n (List.length cnf);
  (* The same conversion through [Cnf_memo] directly, as [Coq_micromega.cnfZ] runs it, counting the
     checks the conversion asks for: the rows hold at most 1 MB plus 64 bytes per stored check, and
     the memo stored fewer checks than the conversion asked for (it refused some). *)
  let module M = Cnf_memo.Make (struct
    type t = Mc.z Mc.nFormula
    let incompatible f f' = match Mc.zdeduce f f' with Some u -> Mc.zunsat u | None -> false
  end) in
  let st = M.create () and asked = ref 0 in
  let cnf', _ =
    Mc.rxcnf M.unsat (fun l l' -> incr asked; M.deduce st l l')
      (fun x a -> M.tag st (Mc.normalise0 x a)) (fun x a -> M.tag st (Mc.negate x a)) true Mc.IsProp f
  in
  assert_equal ~msg:"the clauses, through Cnf_memo" cnf (M.strip_cnf cnf');
  assert_bool "the rows are within the budget" (M.bytes st <= (1 lsl 20) + 64 * M.stored st);
  assert_bool "the budget refused some checks" (M.stored st < !asked))

let () = add_test "the pair checks drop every clause of iff_case" (fun () ->
  let f = mc_tform mc_z iff_case in
  assert_equal ~msg:"cnfZ" (Mc.cnfZ Mc.IsProp f) (Coq_micromega.cnfZ Mc.IsProp f);
  assert_equal ~msg:"no clause is left" [] (fst (Coq_micromega.cnfZ Mc.IsProp f));
  assert_bool "the checker accepts it with no certificate"
    (Zcheck_oracle.z_tauto_checker (zc_bform iff_case) []))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
