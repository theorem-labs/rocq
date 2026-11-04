(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Typed location strippers of globalized terms (see globStrip.mli). *)

open Glob_term

let lident (id : Names.lident) = LocStrip.cast (fun x -> x) id
let lname (na : Names.lname) = LocStrip.cast (fun x -> x) na

let glob_qvar = function
  | GLocalQVar na -> GLocalQVar (lname na)
  | (GQVar _ | GRawQVar _) as q -> q

let glob_relevance = function
  | (GRelevant | GIrrelevant) as r -> r
  | GRelevanceVar q -> GRelevanceVar (glob_qvar q)

let relevance_info r = Option.map glob_relevance r

let glob_quality = function
  | GQConstant _ as q -> q
  | GQualVar q -> GQualVar (glob_qvar q)

let glob_sort_name = function
  | (GSProp | GProp | GSet | GUniv _ | GRawUniv _) as s -> s
  | GLocalUniv id -> GLocalUniv (lident id)

let glob_sort_gen f = function
  | UAnonymous { rigid } -> UAnonymous { rigid }
  | UNamed x -> UNamed (f x)

let glob_level l = glob_sort_gen glob_sort_name l

let glob_instance ((qs, us) : glob_instance) : glob_instance =
  (List.map glob_quality qs, List.map glob_level us)

let glob_sort ((q, s) : glob_sort) : glob_sort =
  (Option.map glob_qvar q,
   glob_sort_gen (List.map (fun (n, k) -> (glob_sort_name n, k))) s)

let glob_constraint ((u, k, v) : glob_constraint) : glob_constraint =
  (glob_sort_name u, k, glob_sort_name v)

(* [glob_evar_kind] (Evar_kinds) holds no location: GlobRef, Id, Name,
   question_mark (Name, Constant, inductive), bools. *)

let rec cases_pattern : 'a. 'a cases_pattern_g -> 'a cases_pattern_g =
  fun p -> LocStrip.dast cases_pattern_r p

and cases_pattern_r : 'a. 'a cases_pattern_r -> 'a cases_pattern_r = function
  | PatVar _ as p -> p
  | PatCstr (c, l, na) -> PatCstr (c, List.map cases_pattern l, na)

let rec glob_constr : 'a. 'a glob_constr_g -> 'a glob_constr_g =
  fun c -> LocStrip.dast glob_constr_r c

and glob_constr_r : 'a. 'a glob_constr_r -> 'a glob_constr_r = function
  | GRef (r, inst) -> GRef (r, Option.map glob_instance inst)
  | GVar _ as c -> c
  | GEvar (ev, args) ->
    GEvar (LocStrip.cast (fun x -> x) ev,
           List.map (fun (id, c) -> (lident id, glob_constr c)) args)
  | GPatVar _ as c -> c
  | GApp (f, args) -> GApp (glob_constr f, List.map glob_constr args)
  | GLambda (na, r, bk, t, b) ->
    GLambda (na, relevance_info r, bk, glob_constr t, glob_constr b)
  | GProd (na, r, bk, t, b) ->
    GProd (na, relevance_info r, bk, glob_constr t, glob_constr b)
  | GLetIn (na, r, b, t, c) ->
    GLetIn (na, relevance_info r, glob_constr b, Option.map glob_constr t, glob_constr c)
  | GCases (st, rt, tms, cls) ->
    GCases (st, Option.map glob_constr rt, List.map tomatch_tuple tms,
            List.map cases_clause cls)
  | GLetTuple (nas, (na, rt), b, c) ->
    GLetTuple (nas, (na, Option.map glob_constr rt), glob_constr b, glob_constr c)
  | GIf (c, (na, rt), b1, b2) ->
    GIf (glob_constr c, (na, Option.map glob_constr rt), glob_constr b1, glob_constr b2)
  | GRec (fk, ids, decls, tys, bodies) ->
    GRec (fk, ids, Array.map (List.map glob_decl) decls,
          Array.map glob_constr tys, Array.map glob_constr bodies)
  | GSort s -> GSort (glob_sort s)
  | GHole _ as c -> c
  | GGenarg g -> GGenarg (Genstrip.generic_strip g)
  | GCast (c, k, t) -> GCast (glob_constr c, k, glob_constr t)
  | GProj ((cst, inst), args, c) ->
    GProj ((cst, Option.map glob_instance inst), List.map glob_constr args, glob_constr c)
  | (GInt _ | GFloat _ | GString _) as c -> c
  | GArray (inst, t, def, ty) ->
    GArray (Option.map glob_instance inst, Array.map glob_constr t,
            glob_constr def, glob_constr ty)

and glob_decl : 'a. 'a glob_decl_g -> 'a glob_decl_g =
  fun (na, r, bk, b, t) ->
  (na, relevance_info r, bk, Option.map glob_constr b, glob_constr t)

and predicate_pattern : 'a. 'a predicate_pattern_g -> 'a predicate_pattern_g =
  fun (na, ind) -> (na, Option.map (LocStrip.cast (fun x -> x)) ind)

and tomatch_tuple : 'a. 'a tomatch_tuple_g -> 'a tomatch_tuple_g =
  fun (c, p) -> (glob_constr c, predicate_pattern p)

and cases_clause : 'a. 'a cases_clause_g -> 'a cases_clause_g =
  fun cl ->
  LocStrip.cast (fun (ids, pats, c) ->
      (ids, List.map cases_pattern pats, glob_constr c)) cl

let disjunctive_cases_clause cl =
  LocStrip.cast (fun (ids, pats, c) ->
      (ids, List.map (List.map cases_pattern) pats, glob_constr c)) cl

let extended_glob_local_binder_r = function
  | GLocalAssum (na, r, bk, t) -> GLocalAssum (na, relevance_info r, bk, glob_constr t)
  | GLocalDef (na, r, b, t) ->
    GLocalDef (na, relevance_info r, glob_constr b, Option.map glob_constr t)
  | GLocalPattern ((pats, ids), id, bk, t) ->
    GLocalPattern ((List.map cases_pattern pats, ids), id, bk, glob_constr t)

let extended_glob_local_binder b = LocStrip.dast extended_glob_local_binder_r b

let rec constr_pattern_r (p : Pattern.uninstantiated_pattern) : Pattern.uninstantiated_pattern =
  let open Pattern in
  let f = constr_pattern_r in
  match p with
  | (PRef _ | PVar _ | PRel _ | PSort _ | PMeta _ | PInt _ | PFloat _ | PString _) as p -> p
  | PEvar (ev, args) -> PEvar (ev, List.map f args)
  | PApp (h, args) -> PApp (f h, Array.map f args)
  | PSoApp (v, args) -> PSoApp (v, List.map f args)
  | PProj (pr, c) -> PProj (pr, f c)
  | PLambda (na, t, b) -> PLambda (na, f t, f b)
  | PProd (na, t, b) -> PProd (na, f t, f b)
  | PLetIn (na, b, t, c) -> PLetIn (na, f b, Option.map f t, f c)
  | PIf (c, b1, b2) -> PIf (f c, f b1, f b2)
  | PCase (ci, rt, c, brs) ->
    PCase (ci, Option.map (fun (nas, t) -> (nas, f t)) rt, f c,
           List.map (fun (i, nas, b) -> (i, nas, f b)) brs)
  | PFix (fi, (nas, tys, bds)) -> PFix (fi, (nas, Array.map f tys, Array.map f bds))
  | PCoFix (i, (nas, tys, bds)) -> PCoFix (i, (nas, Array.map f tys, Array.map f bds))
  | PArray (t, def, ty) -> PArray (Array.map f t, f def, f ty)
  | PExtra g -> PExtra (Genstrip.generic_strip g)

let uninstantiated_pattern = constr_pattern_r

(** Locus *)

let or_var f = function
  | Locus.ArgArg x -> Locus.ArgArg (f x)
  | Locus.ArgVar id -> Locus.ArgVar (lident id)

let occurrences_gen f = function
  | Locus.AllOccurrences -> Locus.AllOccurrences
  | Locus.AtLeastOneOccurrence -> Locus.AtLeastOneOccurrence
  | Locus.NoOccurrences -> Locus.NoOccurrences
  | Locus.AllOccurrencesBut l -> Locus.AllOccurrencesBut (List.map f l)
  | Locus.OnlyOccurrences l -> Locus.OnlyOccurrences (List.map f l)

let occurrences_expr o = occurrences_gen (or_var (fun n -> n)) o

let hyp_location_expr fid (((occs, id), fl) : _ Locus.hyp_location_expr) =
  ((occurrences_expr occs, fid id), fl)

let clause_expr fid (cl : _ Locus.clause_expr) : _ Locus.clause_expr =
  { Locus.onhyps = Option.map (List.map (hyp_location_expr fid)) cl.Locus.onhyps;
    concl_occs = occurrences_expr cl.Locus.concl_occs }
