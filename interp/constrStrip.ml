(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Typed location strippers of concrete syntax and notations
    (see constrStrip.mli). *)

open Constrexpr
open Notation_term

let id x = x

let qualid (q : Libnames.qualid) : Libnames.qualid = LocStrip.cast id q
let lident (x : Names.lident) : Names.lident = LocStrip.cast id x
let lname (x : Names.lname) : Names.lname = LocStrip.cast id x

let or_by_notation f (x : 'a or_by_notation) : 'a or_by_notation =
  LocStrip.cast (function
      | AN a -> AN (f a)
      | ByNotation n -> ByNotation n) x

(** Universes and sorts *)

let sort_name_expr = function
  | (CSProp | CProp | CSet | CRawType _) as s -> s
  | CType q -> CType (qualid q)

let glob_sort_gen f = function
  | Glob_term.UAnonymous { rigid } -> Glob_term.UAnonymous { rigid }
  | Glob_term.UNamed x -> Glob_term.UNamed (f x)

let univ_level_expr (l : univ_level_expr) : univ_level_expr =
  glob_sort_gen sort_name_expr l

let qvar_expr = function
  | CQVar q -> CQVar (qualid q)
  | CQAnon loc -> CQAnon (LocStrip.loc_opt loc)
  | CRawQVar _ as q -> q

let quality_expr = function
  | CQConstant _ as q -> q
  | CQualVar q -> CQualVar (qvar_expr q)

let relevance_expr = function
  | (CRelevant | CIrrelevant) as r -> r
  | CRelevanceVar q -> CRelevanceVar (qvar_expr q)

let relevance_info_expr r = Option.map relevance_expr r

let sort_expr ((q, s) : sort_expr) : sort_expr =
  (Option.map qvar_expr q,
   glob_sort_gen (List.map (fun (n, k) -> (sort_name_expr n, k))) s)

let instance_expr ((qs, us) : instance_expr) : instance_expr =
  (List.map quality_expr qs, List.map univ_level_expr us)

let univ_constraint_expr ((u, k, v) : univ_constraint_expr) : univ_constraint_expr =
  (sort_name_expr u, k, sort_name_expr v)

let elim_constraint_expr ((q, k, q') : elim_constraint_expr) : elim_constraint_expr =
  (quality_expr q, k, quality_expr q')

let sort_constraint_expr = function
  | UnivCst c -> UnivCst (univ_constraint_expr c)
  | ElimCst c -> ElimCst (elim_constraint_expr c)
let gen_universe_decl fq fe fi fu (d : (_, _, _, _) UState.gen_universe_decl)
  : (_, _, _, _) UState.gen_universe_decl =
  let open UState in
  { univdecl_qualities = fq d.univdecl_qualities;
    univdecl_extensible_qualities = d.univdecl_extensible_qualities;
    univdecl_elim_constraints = fe d.univdecl_elim_constraints;
    univdecl_instance = fi d.univdecl_instance;
    univdecl_extensible_instance = d.univdecl_extensible_instance;
    univdecl_univ_constraints = fu d.univdecl_univ_constraints;
    univdecl_extensible_constraints = d.univdecl_extensible_constraints }

let universe_decl_expr (d : universe_decl_expr) : universe_decl_expr =
  gen_universe_decl (List.map lident) (List.map elim_constraint_expr)
    (List.map lident) (List.map univ_constraint_expr) d

let lident_with_variance ((x, v) : lident_with_variance) : lident_with_variance =
  (lident x, v)

let cumul_univ_decl_expr (d : cumul_univ_decl_expr) : cumul_univ_decl_expr =
  gen_universe_decl (List.map lident_with_variance) (List.map elim_constraint_expr)
    (List.map lident_with_variance) (List.map univ_constraint_expr) d

let ident_decl ((x, d) : ident_decl) : ident_decl =
  (lident x, Option.map universe_decl_expr d)

let cumul_ident_decl ((x, d) : cumul_ident_decl) : cumul_ident_decl =
  (lident x, Option.map cumul_univ_decl_expr d)

let name_decl ((x, d) : name_decl) : name_decl =
  (lname x, Option.map universe_decl_expr d)

(** Terms *)

let explicitation (e : explicitation CAst.t) = LocStrip.cast id e

let rec cases_pattern_expr (p : cases_pattern_expr) : cases_pattern_expr =
  LocStrip.cast cases_pattern_expr_r p

and cases_pattern_expr_r = function
  | CPatAlias (p, na) -> CPatAlias (cases_pattern_expr p, lname na)
  | CPatCstr (q, l1, l2) ->
    CPatCstr (qualid q, Option.map (List.map cases_pattern_expr) l1,
              List.map cases_pattern_expr l2)
  | CPatAtom q -> CPatAtom (Option.map qualid q)
  | CPatOr l -> CPatOr (List.map cases_pattern_expr l)
  | CPatNotation (sc, ntn, subst, args) ->
    CPatNotation (sc, ntn, cases_pattern_notation_substitution subst,
                  List.map cases_pattern_expr args)
  | CPatPrim _ as p -> p
  | CPatRecord l -> CPatRecord (List.map (fun (q, p) -> (qualid q, cases_pattern_expr p)) l)
  | CPatDelimiters (d, s, p) -> CPatDelimiters (d, s, cases_pattern_expr p)
  | CPatCast (p, c) -> CPatCast (cases_pattern_expr p, constr_expr c)

and kinded_cases_pattern_expr ((p, bk) : kinded_cases_pattern_expr) =
  (cases_pattern_expr p, bk)

and cases_pattern_notation_substitution (l1, l2, l3) =
  (List.map cases_pattern_expr l1,
   List.map (List.map cases_pattern_expr) l2,
   List.map kinded_cases_pattern_expr l3)

and constr_expr (c : constr_expr) : constr_expr = LocStrip.cast constr_expr_r c

and ref_inst (q, inst) = (qualid q, Option.map instance_expr inst)

and app_arg (c, e) = (constr_expr c, Option.map explicitation e)

and constr_expr_r = function
  | CRef (q, inst) -> CRef (qualid q, Option.map instance_expr inst)
  | CFix (x, l) -> CFix (lident x, List.map fix_expr l)
  | CCoFix (x, l) -> CCoFix (lident x, List.map cofix_expr l)
  | CProdN (bl, c) -> CProdN (List.map local_binder_expr bl, constr_expr c)
  | CLambdaN (bl, c) -> CLambdaN (List.map local_binder_expr bl, constr_expr c)
  | CLetIn (na, b, t, c) ->
    CLetIn (lname na, constr_expr b, Option.map constr_expr t, constr_expr c)
  | CAppExpl (r, args) -> CAppExpl (ref_inst r, List.map constr_expr args)
  | CApp (f, args) -> CApp (constr_expr f, List.map app_arg args)
  | CProj (expl, r, args, c) ->
    CProj (expl, ref_inst r, List.map app_arg args, constr_expr c)
  | CRecord l -> CRecord (List.map (fun (q, c) -> (qualid q, constr_expr c)) l)
  | CCases (st, rt, tms, brs) ->
    CCases (st, Option.map constr_expr rt, List.map case_expr tms,
            List.map branch_expr brs)
  | CLetTuple (nas, (na, rt), b, c) ->
    CLetTuple (List.map lname nas, (Option.map lname na, Option.map constr_expr rt),
               constr_expr b, constr_expr c)
  | CIf (c, (na, rt), b1, b2) ->
    CIf (constr_expr c, (Option.map lname na, Option.map constr_expr rt),
         constr_expr b1, constr_expr b2)
  | CHole _ as c -> c (* glob_evar_kind holds no location *)
  | CGenarg _ ->
    (* A raw generic argument: strippers are registered at the glob level
       only (Genstrip), so there is no typed way to strip it. *)
    LocStrip.unknown "raw generic argument (CGenarg)"
  | CGenargGlob g -> CGenargGlob (Genstrip.generic_strip g)
  | CPatVar _ as c -> c
  | CEvar (ev, args) ->
    CEvar (LocStrip.cast id ev,
           List.map (fun (x, c) -> (lident x, constr_expr c)) args)
  | CSort s -> CSort (sort_expr s)
  | CCast (c, k, t) -> CCast (constr_expr c, k, constr_expr t)
  | CNotation (sc, ntn, subst) -> CNotation (sc, ntn, constr_notation_substitution subst)
  | CGeneralization (bk, c) -> CGeneralization (bk, constr_expr c)
  | CPrim _ as c -> c
  | CDelimiters (d, s, c) -> CDelimiters (d, s, constr_expr c)
  | CArray (inst, t, def, ty) ->
    CArray (Option.map instance_expr inst, Array.map constr_expr t,
            constr_expr def, constr_expr ty)

and case_expr ((c, na, p) : case_expr) : case_expr =
  (constr_expr c, Option.map lname na, Option.map cases_pattern_expr p)

and branch_expr (b : branch_expr) : branch_expr =
  LocStrip.cast (fun (pats, c) ->
      (List.map (List.map cases_pattern_expr) pats, constr_expr c)) b

and fix_expr ((x, r, ord, bl, t, c) : fix_expr) : fix_expr =
  (lident x, relevance_info_expr r, Option.map fixpoint_order_expr ord,
   List.map local_binder_expr bl, constr_expr t, constr_expr c)

and cofix_expr ((x, r, bl, t, c) : cofix_expr) : cofix_expr =
  (lident x, relevance_info_expr r, List.map local_binder_expr bl,
   constr_expr t, constr_expr c)

and fixpoint_order_expr (o : fixpoint_order_expr) : fixpoint_order_expr =
  LocStrip.cast (function
      | CStructRec x -> CStructRec (lident x)
      | CWfRec (x, c) -> CWfRec (lident x, constr_expr c)
      | CMeasureRec (x, m, r) ->
        CMeasureRec (Option.map lident x, constr_expr m, Option.map constr_expr r)) o

and local_binder_expr = function
  | CLocalAssum (nas, r, bk, t) ->
    CLocalAssum (List.map lname nas, relevance_info_expr r, bk, constr_expr t)
  | CLocalDef (na, r, b, t) ->
    CLocalDef (lname na, relevance_info_expr r, constr_expr b, Option.map constr_expr t)
  | CLocalPattern p -> CLocalPattern (cases_pattern_expr p)

and constr_notation_substitution (l1, l2, l3, l4) =
  (List.map constr_expr l1,
   List.map (List.map constr_expr) l2,
   List.map kinded_cases_pattern_expr l3,
   List.map (List.map local_binder_expr) l4)

(** Modules *)

let with_declaration_ast = function
  | CWith_Module (ids, q) -> CWith_Module (LocStrip.cast id ids, qualid q)
  | CWith_Definition (ids, ud, c) ->
    CWith_Definition (LocStrip.cast id ids, Option.map universe_decl_expr ud, constr_expr c)

let rec module_ast (m : module_ast) : module_ast =
  LocStrip.cast (function
      | CMident q -> CMident (qualid q)
      | CMapply (m, q) -> CMapply (module_ast m, qualid q)
      | CMwith (m, w) -> CMwith (module_ast m, with_declaration_ast w)) m

(** Globalized terms paired with their source *)

let glob_constr_and_expr ((c, e) : Genintern.glob_constr_and_expr) : Genintern.glob_constr_and_expr =
  (GlobStrip.glob_constr c, Option.map constr_expr e)

let glob_constr_pattern_and_expr ((ids, c, p) : Genintern.glob_constr_pattern_and_expr)
  : Genintern.glob_constr_pattern_and_expr =
  (ids, glob_constr_and_expr c, GlobStrip.uninstantiated_pattern p)

(** Notations (no location of their own; [glob_sort], [cases_pattern] and
    generic arguments can hold some) *)

let rec notation_constr (c : notation_constr) : notation_constr =
  let f = notation_constr in
  match c with
  | NRef (r, inst) -> NRef (r, Option.map GlobStrip.glob_instance inst)
  | NVar _ as c -> c
  | NApp (h, args) -> NApp (f h, List.map f args)
  | NProj ((cst, inst), args, c) ->
    NProj ((cst, Option.map GlobStrip.glob_instance inst), List.map f args, f c)
  | NHole _ as c -> c (* glob_evar_kind holds no location *)
  | NGenarg g -> NGenarg (Genstrip.generic_strip g)
  | NList (x, y, it, ter, assoc) -> NList (x, y, f it, f ter, assoc)
  | NLambda (na, t, b) -> NLambda (na, Option.map f t, f b)
  | NProd (na, t, b) -> NProd (na, Option.map f t, f b)
  | NBinderList (x, y, it, ter, assoc) -> NBinderList (x, y, f it, f ter, assoc)
  | NLetIn (na, b, t, c) -> NLetIn (na, f b, Option.map f t, f c)
  | NCases (st, rt, tms, brs) ->
    NCases (st, Option.map f rt,
            List.map (fun (tm, p) -> (f tm, p)) tms,
            List.map (fun (pats, c) -> (List.map GlobStrip.cases_pattern pats, f c)) brs)
  | NLetTuple (nas, (na, rt), b, c) -> NLetTuple (nas, (na, Option.map f rt), f b, f c)
  | NIf (c, (na, rt), b1, b2) -> NIf (f c, (na, Option.map f rt), f b1, f b2)
  | NRec (fk, ids, decls, tys, bodies) ->
    NRec (fk, ids,
          Array.map (List.map (fun (na, b, t) -> (na, Option.map f b, f t))) decls,
          Array.map f tys, Array.map f bodies)
  | NSort s -> NSort (GlobStrip.glob_sort s)
  | NCast (c, k, t) -> NCast (f c, k, f t)
  | (NInt _ | NFloat _ | NString _) as c -> c
  | NArray (t, def, ty) -> NArray (Array.map f t, f def, f ty)

(* The variable metadata (scopes, entry levels, binder sets, instance
   types) holds no location. *)
let interpretation ((vars, c) : interpretation) : interpretation =
  (vars, notation_constr c)
