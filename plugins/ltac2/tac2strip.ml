(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tac2expr

(** A [CAst] node whose value holds no location: [Libnames.qualid],
    [Names.lident], [Names.lname], [string CAst.t], [int CAst.t]. *)
let cast_leaf x = LocStrip.cast (fun v -> v) x

(** [AbsKn] payloads (kernel names, tuple arities) hold no location. *)
let or_relid = function
  | RelId qid -> RelId (cast_leaf qid)
  | AbsKn _ as r -> r

(** {5 Globalized expressions} *)

(* glb_pat, case_info, Name.t, atom, ml_tactic_name and kernel names hold no
   location: they are returned as they are. *)
let rec glb_tacexpr = function
  | GTacAtm _ | GTacVar _ | GTacRef _ | GTacPrm _ as e -> e
  | GTacFun (nas, e) -> GTacFun (nas, glb_tacexpr e)
  | GTacApp (f, args) -> GTacApp (glb_tacexpr f, List.map glb_tacexpr args)
  | GTacLet (isrec, bnd, e) ->
    let bnd = List.map (fun (na, b) -> (na, glb_tacexpr b)) bnd in
    GTacLet (isrec, bnd, glb_tacexpr e)
  | GTacCst (info, n, args) -> GTacCst (info, n, List.map glb_tacexpr args)
  | GTacCse (e, info, cst, ncst) ->
    let ncst = Array.map (fun (nas, b) -> (nas, glb_tacexpr b)) ncst in
    GTacCse (glb_tacexpr e, info, Array.map glb_tacexpr cst, ncst)
  | GTacPrj (kn, e, n) -> GTacPrj (kn, glb_tacexpr e, n)
  | GTacSet (kn, e, n, r) -> GTacSet (kn, glb_tacexpr e, n, glb_tacexpr r)
  | GTacOpn (kn, args) -> GTacOpn (kn, List.map glb_tacexpr args)
  | GTacWth m -> GTacWth (open_match m)
  | GTacFullMatch (e, brs) ->
    let brs = List.map (fun (pat, b) -> (pat, glb_tacexpr b)) brs in
    GTacFullMatch (glb_tacexpr e, brs)
  | GTacExt (tag, v) -> GTacExt (tag, Tac2env.strip_ml_object tag v)

and open_match { opn_match; opn_branch; opn_default } =
  let opn_branch =
    KerName.Map.map (fun (na, nas, b) -> (na, nas, glb_tacexpr b)) opn_branch
  in
  let opn_default = let (na, b) = opn_default in (na, glb_tacexpr b) in
  { opn_match = glb_tacexpr opn_match; opn_branch; opn_default }

(** {5 Raw expressions} *)

let rec raw_typexpr t = LocStrip.cast raw_typexpr_r t

and raw_typexpr_r = function
  | CTypVar _ as t -> t
  | CTypArrow (t1, t2) -> CTypArrow (raw_typexpr t1, raw_typexpr t2)
  | CTypRef (r, args) -> CTypRef (or_relid r, List.map raw_typexpr args)

let rec raw_patexpr p = LocStrip.cast raw_patexpr_r p

and raw_patexpr_r = function
  | CPatVar _ | CPatAtm _ as p -> p
  | CPatRef (r, args) -> CPatRef (or_relid r, List.map raw_patexpr args)
  | CPatRecord fields ->
    CPatRecord (List.map (fun (r, p) -> (or_relid r, raw_patexpr p)) fields)
  | CPatCnv (p, t) -> CPatCnv (raw_patexpr p, raw_typexpr t)
  | CPatOr ps -> CPatOr (List.map raw_patexpr ps)
  | CPatAs (p, id) -> CPatAs (raw_patexpr p, cast_leaf id)

let rec raw_tacexpr e = LocStrip.cast raw_tacexpr_r e

and raw_tacexpr_r = function
  | CTacAtm _ as e -> e
  | CTacRef r -> CTacRef (or_relid r)
  | CTacCst r -> CTacCst (or_relid r)
  | CTacFun (pats, e) -> CTacFun (List.map raw_patexpr pats, raw_tacexpr e)
  | CTacApp (f, args) -> CTacApp (raw_tacexpr f, List.map raw_tacexpr args)
  | CTacSyn (bnd, kn) ->
    CTacSyn (List.map (fun (na, e) -> (cast_leaf na, raw_tacexpr e)) bnd, kn)
  | CTacLet (isrec, bnd, e) ->
    let bnd = List.map (fun (p, b) -> (raw_patexpr p, raw_tacexpr b)) bnd in
    CTacLet (isrec, bnd, raw_tacexpr e)
  | CTacCnv (e, t) -> CTacCnv (raw_tacexpr e, raw_typexpr t)
  | CTacSeq (e1, e2) -> CTacSeq (raw_tacexpr e1, raw_tacexpr e2)
  | CTacIft (c, t, f) -> CTacIft (raw_tacexpr c, raw_tacexpr t, raw_tacexpr f)
  | CTacCse (e, brs) -> CTacCse (raw_tacexpr e, List.map raw_taccase brs)
  | CTacRec (def, fields) -> CTacRec (Option.map raw_tacexpr def, raw_recexpr fields)
  | CTacPrj (e, p) -> CTacPrj (raw_tacexpr e, or_relid p)
  | CTacSet (e, p, r) -> CTacSet (raw_tacexpr e, or_relid p, raw_tacexpr r)
  | CTacExt (tag, _) ->
    (* Raw ML payloads have no stripper; globalization never leaves one in
       a stored expression (see [Tac2intern.globalize]). *)
    LocStrip.unknown ("Ltac2 raw ML object " ^ Tac2dyn.Arg.repr tag)
  | CTacGlb (prms, args, body, ty) ->
    let args = List.map (fun (na, e, t) -> (cast_leaf na, raw_tacexpr e, t)) args in
    CTacGlb (prms, args, glb_tacexpr body, ty)

and raw_taccase (p, e) = (raw_patexpr p, raw_tacexpr e)

and raw_recexpr fields = List.map (fun (p, e) -> (or_relid p, raw_tacexpr e)) fields

(** {5 Notation syntax} *)

let rec sexpr = function
  | SexprStr s -> SexprStr (cast_leaf s)
  | SexprInt i -> SexprInt (cast_leaf i)
  | SexprRec (loc, na, args) ->
    SexprRec (LocStrip.loc loc, LocStrip.cast (Option.map cast_leaf) na, List.map sexpr args)

(* Type parameters and Ltac2 types ([int glb_typexpr]) hold no location. *)
let notation_data = function
  | Tac2env.UntypedNota body -> Tac2env.UntypedNota (raw_tacexpr body)
  | Tac2env.TypedNota { nota_prms; nota_argtys; nota_ty; nota_body } ->
    Tac2env.TypedNota { nota_prms; nota_argtys; nota_ty; nota_body = glb_tacexpr nota_body }

(** {5 Generic arguments} *)

let () =
  Genstrip.register_strip0 Tac2env.wit_ltac2_constr
    (fun (ids, e) -> (ids, glb_tacexpr e));
  (* The Ltac2 language of [Gentactic] (proof mode, Solve Obligations...). *)
  Genstrip.register_strip0 Tac2env.wit_ltac2_tac glb_tacexpr;
  (* [var_quotation_kind * Id.t]: no location. *)
  Genstrip.register_strip0 Tac2env.wit_ltac2_var_quotation (fun v -> v)
