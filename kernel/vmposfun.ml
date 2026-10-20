(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (c)   **************************************************************)
(*    \\//    *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(************************************************************************)

(** Kernel-owned reference terms for bytecode VM operations on [positive]. *)

open Names
open Constr
open Declarations
let enabled =
  match Sys.getenv_opt "ROCQ_VM_FASTBIN" with
  | None | Some "1" -> true
  | Some "0" -> false
  | Some value ->
    failwith ("ROCQ_VM_FASTBIN must be 0 or 1, got " ^ Printf.sprintf "%S" value)

let operation_id = function
  | Retroknowledge.Pos_compare_cont -> 0
  | Retroknowledge.Pos_eqb -> 1
  | Retroknowledge.Pos_add -> 2
  | Retroknowledge.Pos_succ -> 3
  | Retroknowledge.Pos_mul -> 4

let arity = function
  | Retroknowledge.Pos_compare_cont -> 3
  | Retroknowledge.Pos_eqb | Retroknowledge.Pos_add | Retroknowledge.Pos_mul -> 2
  | Retroknowledge.Pos_succ -> 1

external register_closure : Vmvalues.values -> int -> int -> unit = "rocq_vmposfun_register"

let bind env constant closure =
  if enabled then
    match List.find_map (fun (operation, registered) ->
        if Names.Constant.CanOrd.equal constant registered then Some operation else None)
      (Environ.retroknowledge env).Retroknowledge.retro_pos_functions with
    | None -> ()
    | Some operation -> register_closure closure (operation_id operation) (arity operation)


let error text = CErrors.user_err Pp.(str "Register positive function: " ++ str text)

let find_pos env =
  match (Environ.retroknowledge env).Retroknowledge.retro_pos with
  | Some constructors -> constructors
  | None -> error "positive is not registered"

let find_cmp env =
  match (Environ.retroknowledge env).Retroknowledge.retro_cmp with
  | Some constructors -> constructors
  | None -> error "comparison is not registered"

let find_bool env =
  match (Environ.retroknowledge env).Retroknowledge.retro_bool with
  | Some constructors -> constructors
  | None -> error "bool is not registered"

let type_of_constructor ((ind, _) : constructor) = UnsafeMonomorphic.mkInd ind
let term_of_constructor constructor = UnsafeMonomorphic.mkConstruct constructor

let case_info ind arities =
  { ci_ind = ind;
    ci_npar = 0;
    ci_cstr_ndecls = arities;
    ci_cstr_nargs = Array.copy arities;
    ci_pp_info = { style = MatchStyle }; }

let case ci result scrutinee branches =
  mkCase
    (ci, UVars.Instance.empty, [||], (([| Context.anonR |], result), Sorts.Relevant),
     NoInvert, scrutinee, branches)

let branch arity body = Array.make arity Context.anonR, body
let lambda domain body = mkLambda (Context.anonR, domain, body)
let product domains codomain =
  List.fold_right (fun domain codomain -> mkProd (Context.anonR, domain, codomain)) domains codomain

let fixpoint recursive_argument typ body =
  mkFix (([| recursive_argument |], 0), ([| Context.anonR |], [| typ |], [| body |]))

let reference_compare_cont env =
  let x_i_constructor, x_o_constructor, x_h_constructor = find_pos env in
  let eq_constructor, lt_constructor, gt_constructor = find_cmp env in
  let positive = type_of_constructor x_i_constructor in
  let comparison = type_of_constructor eq_constructor in
  let lt = term_of_constructor lt_constructor in
  let gt = term_of_constructor gt_constructor in
  let pos_case = case_info (fst x_i_constructor) [| 1; 1; 0 |] in
  let recursive f r p q = mkApp (mkRel f, [| r; mkRel p; mkRel q |]) in
  let body =
    lambda comparison (lambda positive (lambda positive
      (case pos_case comparison (mkRel 2)
        [| branch 1
             (case pos_case comparison (mkRel 2)
                [| branch 1 (recursive 6 (mkRel 5) 2 1);
                   branch 1 (recursive 6 gt 2 1);
                   branch 0 gt |]);
           branch 1
             (case pos_case comparison (mkRel 2)
                [| branch 1 (recursive 6 lt 2 1);
                   branch 1 (recursive 6 (mkRel 5) 2 1);
                   branch 0 gt |]);
           branch 0
             (case pos_case comparison (mkRel 1)
                [| branch 1 lt; branch 1 lt; branch 0 (mkRel 3) |]) |])))
  in
  let typ = product [comparison; positive; positive] comparison in
  ignore x_o_constructor;
  ignore x_h_constructor;
  fixpoint 2 typ body

let reference_eqb env =
  let x_i_constructor, x_o_constructor, x_h_constructor = find_pos env in
  let true_constructor, false_constructor = find_bool env in
  let positive = type_of_constructor x_i_constructor in
  let bool = type_of_constructor true_constructor in
  let true_ = term_of_constructor true_constructor in
  let false_ = term_of_constructor false_constructor in
  let pos_case = case_info (fst x_i_constructor) [| 1; 1; 0 |] in
  let recursive p q = mkApp (mkRel 5, [| mkRel p; mkRel q |]) in
  let body =
    lambda positive (lambda positive
      (case pos_case bool (mkRel 2)
        [| branch 1
             (case pos_case bool (mkRel 2)
                [| branch 1 (recursive 2 1); branch 1 false_; branch 0 false_ |]);
           branch 1
             (case pos_case bool (mkRel 2)
                [| branch 1 false_; branch 1 (recursive 2 1); branch 0 false_ |]);
           branch 0
             (case pos_case bool (mkRel 1)
                [| branch 1 false_; branch 1 false_; branch 0 true_ |]) |]))
  in
  let typ = product [positive; positive] bool in
  ignore x_o_constructor;
  ignore x_h_constructor;
  fixpoint 1 typ body

let find_registered env operation =
  match List.assoc_opt operation (Environ.retroknowledge env).Retroknowledge.retro_pos_functions with
  | Some constant -> UnsafeMonomorphic.mkConst constant
  | None ->
    error ("the prerequisite " ^ Retroknowledge.pos_function_to_string operation ^
           " is not registered")

let reference_succ env =
  let x_i_constructor, x_o_constructor, x_h_constructor = find_pos env in
  let positive = type_of_constructor x_i_constructor in
  let x_i = term_of_constructor x_i_constructor in
  let x_o = term_of_constructor x_o_constructor in
  let x_h = term_of_constructor x_h_constructor in
  let pos_case = case_info (fst x_i_constructor) [| 1; 1; 0 |] in
  let body =
    lambda positive
      (case pos_case positive (mkRel 1)
         [| branch 1 (mkApp (x_o, [| mkApp (mkRel 3, [| mkRel 1 |]) |]));
            branch 1 (mkApp (x_i, [| mkRel 1 |]));
            branch 0 (mkApp (x_o, [| x_h |])) |])
  in
  let typ = product [positive] positive in
  fixpoint 0 typ body

let reference_add env =
  let x_i_constructor, x_o_constructor, x_h_constructor = find_pos env in
  let positive = type_of_constructor x_i_constructor in
  let x_i = term_of_constructor x_i_constructor in
  let x_o = term_of_constructor x_o_constructor in
  let x_h = term_of_constructor x_h_constructor in
  let succ = find_registered env Retroknowledge.Pos_succ in
  let pos_case = case_info (fst x_i_constructor) [| 1; 1; 0 |] in
  let add f p q = mkApp (mkRel f, [| mkRel p; mkRel q |]) in
  let succ p = mkApp (succ, [| mkRel p |]) in
  let body_add =
    lambda positive (lambda positive
      (case pos_case positive (mkRel 2)
        [| branch 1
             (case pos_case positive (mkRel 2)
                [| branch 1 (mkApp (x_o, [| add 5 2 1 |]));
                   branch 1 (mkApp (x_i, [| add 6 2 1 |]));
                   branch 0 (mkApp (x_o, [| succ 1 |])) |]);
           branch 1
             (case pos_case positive (mkRel 2)
                [| branch 1 (mkApp (x_i, [| add 6 2 1 |]));
                   branch 1 (mkApp (x_o, [| add 6 2 1 |]));
                   branch 0 (mkApp (x_i, [| mkRel 1 |])) |]);
           branch 0
             (case pos_case positive (mkRel 1)
                [| branch 1 (mkApp (x_o, [| succ 1 |]));
                   branch 1 (mkApp (x_i, [| mkRel 1 |]));
                   branch 0 (mkApp (x_o, [| x_h |])) |]) |]))
  in
  let body_carry =
    lambda positive (lambda positive
      (case pos_case positive (mkRel 2)
        [| branch 1
             (case pos_case positive (mkRel 2)
                [| branch 1 (mkApp (x_i, [| add 5 2 1 |]));
                   branch 1 (mkApp (x_o, [| add 5 2 1 |]));
                   branch 0 (mkApp (x_i, [| succ 1 |])) |]);
           branch 1
             (case pos_case positive (mkRel 2)
                [| branch 1 (mkApp (x_o, [| add 5 2 1 |]));
                   branch 1 (mkApp (x_i, [| add 6 2 1 |]));
                   branch 0 (mkApp (x_o, [| succ 1 |])) |]);
           branch 0
             (case pos_case positive (mkRel 1)
                [| branch 1 (mkApp (x_i, [| succ 1 |]));
                   branch 1 (mkApp (x_o, [| succ 1 |]));
                   branch 0 (mkApp (x_i, [| x_h |])) |]) |]))
  in
  let typ = product [positive; positive] positive in
  mkFix (([| 0; 0 |], 0),
         ([| Context.anonR; Context.anonR |], [| typ; typ |], [| body_add; body_carry |]))

let reference_mul env =
  let x_i_constructor, x_o_constructor, x_h_constructor = find_pos env in
  let positive = type_of_constructor x_i_constructor in
  let x_o = term_of_constructor x_o_constructor in
  let add = find_registered env Retroknowledge.Pos_add in
  let pos_case = case_info (fst x_i_constructor) [| 1; 1; 0 |] in
  let recursive p y = mkApp (mkRel 4, [| mkRel p; mkRel y |]) in
  let body =
    lambda positive (lambda positive
      (case pos_case positive (mkRel 2)
        [| branch 1 (mkApp (add, [| mkRel 2; mkApp (x_o, [| recursive 1 2 |]) |]));
           branch 1 (mkApp (x_o, [| recursive 1 2 |]));
           branch 0 (mkRel 1) |]))
  in
  let typ = product [positive; positive] positive in
  ignore x_h_constructor;
  fixpoint 0 typ body

let reference env = function
  | Retroknowledge.Pos_compare_cont -> reference_compare_cont env
  | Retroknowledge.Pos_eqb -> reference_eqb env
  | Retroknowledge.Pos_add -> reference_add env
  | Retroknowledge.Pos_succ -> reference_succ env
  | Retroknowledge.Pos_mul -> reference_mul env

let check env operation constant =
  let cb = Environ.lookup_constant constant env in
  match cb.const_universes, cb.const_body with
  | Monomorphic, Def body ->
    let reference = reference env operation in
    if Constr.equal body reference then ()
    else begin
      match Conversion.conv env body reference with
      | Result.Ok () -> ()
      | Result.Error () ->
        error ("the body of " ^ Names.Constant.to_string constant ^
               " is not convertible to the registered reference")
    end
  | Polymorphic _, _ ->
    error "a universe monomorphic constant is expected"
  | Monomorphic, (Undef _ | OpaqueDef _ | Primitive _ | Symbol _) ->
    error "a transparent definition is expected"
