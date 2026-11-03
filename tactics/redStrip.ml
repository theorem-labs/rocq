(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Typed location strippers of globalized reduction expressions
    (see redStrip.mli). *)

open Genredexpr

let g_trm = ConstrStrip.glob_constr_and_expr

let g_cst (c : g_cst) : g_cst =
  GlobStrip.or_var (fun (ev, short) -> (ev, Option.map ConstrStrip.lident short)) c

let occvar = GlobStrip.or_var (fun (n : int) -> n)

let occs o = GlobStrip.occurrences_gen occvar o

let glob_red_flag (f : g_cst glob_red_flag) : g_cst glob_red_flag =
  { f with rConst = List.map g_cst f.rConst }

let red_context (c : (g_cst, g_trm, int Locus.or_var) red_context) =
  Option.map (fun (o, u) ->
      (occs o, match u with
        | Util.Inl b -> Util.Inl (g_cst b)
        | Util.Inr t -> Util.Inr (g_trm t))) c

let glob_red_expr strip_usr (r : 'usr glob_red_expr) : 'usr glob_red_expr =
  match r with
  | Red -> Red
  | Hnf -> Hnf
  | Simpl (fl, ctx) -> Simpl (glob_red_flag fl, red_context ctx)
  | Cbv fl -> Cbv (glob_red_flag fl)
  | Cbn fl -> Cbn (glob_red_flag fl)
  | Lazy fl -> Lazy (glob_red_flag fl)
  | Unfold l -> Unfold (List.map (fun (o, c) -> (occs o, g_cst c)) l)
  | Fold l -> Fold (List.map g_trm l)
  | Pattern l -> Pattern (List.map (fun (o, c) -> (occs o, g_trm c)) l)
  | ExtraRedExpr _ as r -> r
  | CbvVm ctx -> CbvVm (red_context ctx)
  | CbvNative ctx -> CbvNative (red_context ctx)
  | UserRed u -> UserRed (strip_usr u)
