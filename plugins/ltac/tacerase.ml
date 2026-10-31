(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* BET-84: see the interface. Each function rebuilds its value with the same
   constructor and the same non-location fields, and with [None] for every
   location; a field of a type that holds no location is kept as it is. *)

open Names
open Locus
open Genarg
open Glob_term
open Constrexpr
open Pattern
open Genredexpr
open Tactypes
open Tacexpr

(** {5 Locations} *)

let lident (id : lident) : lident = CAst.make id.CAst.v
let lname (na : lname) : lname = CAst.make na.CAst.v
let qualid (q : Libnames.qualid) : Libnames.qualid = CAst.make q.CAst.v
let located ((_, x) : 'a Loc.located) : 'a Loc.located = (None, x)

let or_var (f : 'a -> 'a) = function
  | ArgArg x -> ArgArg (f x)
  | ArgVar id -> ArgVar (lident id)

let int_or_var : int or_var -> int or_var = fun n -> or_var (fun n -> n) n

(** {5 Generic arguments} *)

module EraseObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb -> 'glb
  let name = "erase_locations"
  let default _ = Some (fun v -> v)
end

module Erase = Register (EraseObj)

let register_erase0 = Erase.register0

let rec erase_at : type r g t. (r, g, t) genarg_type -> g -> g = fun wit v ->
  match wit with
  | ListArg wit -> List.map (erase_at wit) v
  | OptArg wit -> Option.map (erase_at wit) v
  | PairArg (wit1, wit2) -> let (a, b) = v in (erase_at wit1 a, erase_at wit2 b)
  | ExtraArg _ -> Erase.obj wit v

let erase_genarg (GenArg (Glbwit wit, v)) = in_gen (glbwit wit) (erase_at wit v)

(** {5 Sorts and universe instances} *)

let glob_sort_gen (f : 'a -> 'a) = function
  | UNamed x -> UNamed (f x)
  | UAnonymous { rigid } -> UAnonymous { rigid }

let glob_qvar = function
  | GLocalQVar na -> GLocalQVar (lname na)
  | GQVar _ | GRawQVar _ as q -> q

let glob_relevance = function
  | GRelevanceVar q -> GRelevanceVar (glob_qvar q)
  | GRelevant | GIrrelevant as r -> r

let relevance_info r = Option.map glob_relevance r

let glob_quality = function
  | GQualVar q -> GQualVar (glob_qvar q)
  | GQConstant _ as q -> q

let glob_sort_name = function
  | GLocalUniv id -> GLocalUniv (lident id)
  | GSProp | GProp | GSet | GUniv _ | GRawUniv _ as s -> s

let glob_instance ((qs, ls) : glob_instance) : glob_instance =
  (List.map glob_quality qs, List.map (glob_sort_gen glob_sort_name) ls)

let glob_sort ((q, s) : glob_sort) : glob_sort =
  (Option.map glob_qvar q,
   glob_sort_gen (List.map (fun (na, n) -> (glob_sort_name na, n))) s)

(** {5 Globalized terms} *)

let rec cases_pattern (p : cases_pattern) : cases_pattern =
  DAst.make (match DAst.get p with
      | PatVar _ as v -> v
      | PatCstr (c, l, na) -> PatCstr (c, List.map cases_pattern l, na))

let rec glob_constr (c : glob_constr) : glob_constr =
  DAst.make (glob_constr_r (DAst.get c))

and glob_constr_r = function
  | GRef (r, u) -> GRef (r, Option.map glob_instance u)
  | GVar _ | GPatVar _ | GHole _ | GInt _ | GFloat _ | GString _ as c -> c
  | GEvar (ev, l) ->
    GEvar (CAst.make ev.CAst.v, List.map (fun (id, c) -> (lident id, glob_constr c)) l)
  | GApp (f, l) -> GApp (glob_constr f, List.map glob_constr l)
  | GLambda (na, r, bk, t, b) -> GLambda (na, relevance_info r, bk, glob_constr t, glob_constr b)
  | GProd (na, r, bk, t, b) -> GProd (na, relevance_info r, bk, glob_constr t, glob_constr b)
  | GLetIn (na, r, b, t, c) ->
    GLetIn (na, relevance_info r, glob_constr b, Option.map glob_constr t, glob_constr c)
  | GCases (st, rt, tml, cl) ->
    GCases (st, Option.map glob_constr rt, List.map tomatch_tuple tml, List.map cases_clause cl)
  | GLetTuple (nal, (na, po), b, c) ->
    GLetTuple (nal, (na, Option.map glob_constr po), glob_constr b, glob_constr c)
  | GIf (c, (na, po), b1, b2) ->
    GIf (glob_constr c, (na, Option.map glob_constr po), glob_constr b1, glob_constr b2)
  | GRec (fk, ids, decls, tys, bodies) ->
    GRec (fk, ids, Array.map (List.map glob_decl) decls,
          Array.map glob_constr tys, Array.map glob_constr bodies)
  | GSort s -> GSort (glob_sort s)
  | GGenarg g -> GGenarg (erase_genarg g)
  | GCast (c, k, t) -> GCast (glob_constr c, k, glob_constr t)
  | GProj ((cst, u), args, c) ->
    GProj ((cst, Option.map glob_instance u), List.map glob_constr args, glob_constr c)
  | GArray (u, a, d, t) ->
    GArray (Option.map glob_instance u, Array.map glob_constr a, glob_constr d, glob_constr t)

and glob_decl (na, r, bk, b, t) =
  (na, relevance_info r, bk, Option.map glob_constr b, glob_constr t)

and tomatch_tuple (c, (na, ind)) =
  (glob_constr c, (na, Option.map (fun ind -> CAst.make ind.CAst.v) ind))

and cases_clause cl =
  let (ids, pl, c) = cl.CAst.v in
  CAst.make (ids, List.map cases_pattern pl, glob_constr c)

let erase_glob_constr = glob_constr

(** {5 Concrete terms} *)

let qvar_expr = function
  | CQVar q -> CQVar (qualid q)
  | CQAnon _ -> CQAnon None
  | CRawQVar _ as q -> q

let quality_expr = function
  | CQualVar q -> CQualVar (qvar_expr q)
  | CQConstant _ as q -> q

let relevance_expr = function
  | CRelevanceVar q -> CRelevanceVar (qvar_expr q)
  | CRelevant | CIrrelevant as r -> r

let relevance_info_expr r = Option.map relevance_expr r

let sort_name_expr = function
  | CType q -> CType (qualid q)
  | CSProp | CProp | CSet | CRawType _ as s -> s

let sort_expr ((q, s) : sort_expr) : sort_expr =
  (Option.map qvar_expr q,
   glob_sort_gen (List.map (fun (na, n) -> (sort_name_expr na, n))) s)

let instance_expr ((qs, ls) : instance_expr) : instance_expr =
  (List.map quality_expr qs, List.map (glob_sort_gen sort_name_expr) ls)

let explicitation (e : explicitation CAst.t option) = Option.map (fun e -> CAst.make e.CAst.v) e

let rec constr_expr (c : constr_expr) : constr_expr = CAst.make (constr_expr_r c.CAst.v)

and constr_expr_r = function
  | CRef (q, u) -> CRef (qualid q, Option.map instance_expr u)
  | CFix (id, l) -> CFix (lident id, List.map fix_expr l)
  | CCoFix (id, l) -> CCoFix (lident id, List.map cofix_expr l)
  | CProdN (bl, c) -> CProdN (List.map local_binder bl, constr_expr c)
  | CLambdaN (bl, c) -> CLambdaN (List.map local_binder bl, constr_expr c)
  | CLetIn (na, b, t, c) -> CLetIn (lname na, constr_expr b, Option.map constr_expr t, constr_expr c)
  | CAppExpl ((q, u), l) -> CAppExpl ((qualid q, Option.map instance_expr u), List.map constr_expr l)
  | CApp (f, l) -> CApp (constr_expr f, List.map app_arg l)
  | CProj (e, (q, u), l, c) ->
    CProj (e, (qualid q, Option.map instance_expr u), List.map app_arg l, constr_expr c)
  | CRecord l -> CRecord (List.map (fun (q, c) -> (qualid q, constr_expr c)) l)
  | CCases (st, rt, cl, bl) ->
    CCases (st, Option.map constr_expr rt, List.map case_expr cl, List.map branch_expr bl)
  | CLetTuple (nal, (na, po), b, c) ->
    CLetTuple (List.map lname nal, (Option.map lname na, Option.map constr_expr po),
               constr_expr b, constr_expr c)
  | CIf (c, (na, po), b1, b2) ->
    CIf (constr_expr c, (Option.map lname na, Option.map constr_expr po),
         constr_expr b1, constr_expr b2)
  (* A raw generic argument has no eraser: its type is open. *)
  | CHole _ | CGenarg _ | CPatVar _ | CPrim _ as c -> c
  | CGenargGlob g -> CGenargGlob (erase_genarg g)
  | CEvar (ev, l) ->
    CEvar (CAst.make ev.CAst.v, List.map (fun (id, c) -> (lident id, constr_expr c)) l)
  | CSort s -> CSort (sort_expr s)
  | CCast (c, k, t) -> CCast (constr_expr c, k, constr_expr t)
  | CNotation (sc, ntn, subst) -> CNotation (sc, ntn, notation_substitution subst)
  | CGeneralization (bk, c) -> CGeneralization (bk, constr_expr c)
  | CDelimiters (d, s, c) -> CDelimiters (d, s, constr_expr c)
  | CArray (u, a, d, t) ->
    CArray (Option.map instance_expr u, Array.map constr_expr a, constr_expr d, constr_expr t)

and app_arg (c, e) = (constr_expr c, explicitation e)

and case_expr (c, na, p) = (constr_expr c, Option.map lname na, Option.map cases_pattern_expr p)

and branch_expr b =
  let (pll, c) = b.CAst.v in
  CAst.make (List.map (List.map cases_pattern_expr) pll, constr_expr c)

and fix_expr (id, r, ord, bl, t, c) =
  (lident id, relevance_info_expr r, Option.map fixpoint_order_expr ord,
   List.map local_binder bl, constr_expr t, constr_expr c)

and cofix_expr (id, r, bl, t, c) =
  (lident id, relevance_info_expr r, List.map local_binder bl, constr_expr t, constr_expr c)

and fixpoint_order_expr o =
  CAst.make (match o.CAst.v with
      | CStructRec id -> CStructRec (lident id)
      | CWfRec (id, c) -> CWfRec (lident id, constr_expr c)
      | CMeasureRec (id, m, r) -> CMeasureRec (Option.map lident id, constr_expr m, Option.map constr_expr r))

and local_binder = function
  | CLocalAssum (nal, r, bk, t) -> CLocalAssum (List.map lname nal, relevance_info_expr r, bk, constr_expr t)
  | CLocalDef (na, r, b, t) -> CLocalDef (lname na, relevance_info_expr r, constr_expr b, Option.map constr_expr t)
  | CLocalPattern p -> CLocalPattern (cases_pattern_expr p)

and notation_substitution (l, ll, bl, bll) =
  (List.map constr_expr l, List.map (List.map constr_expr) ll,
   List.map kinded_cases_pattern bl, List.map (List.map local_binder) bll)

and kinded_cases_pattern (p, bk) = (cases_pattern_expr p, bk)

and cases_pattern_expr p =
  CAst.make (match p.CAst.v with
      | CPatAlias (p, na) -> CPatAlias (cases_pattern_expr p, lname na)
      | CPatCstr (q, l1, l2) ->
        CPatCstr (qualid q, Option.map (List.map cases_pattern_expr) l1, List.map cases_pattern_expr l2)
      | CPatAtom q -> CPatAtom (Option.map qualid q)
      | CPatOr l -> CPatOr (List.map cases_pattern_expr l)
      | CPatNotation (sc, ntn, (l, ll, bl), args) ->
        CPatNotation (sc, ntn,
                      (List.map cases_pattern_expr l, List.map (List.map cases_pattern_expr) ll,
                       List.map kinded_cases_pattern bl),
                      List.map cases_pattern_expr args)
      | CPatPrim _ as p -> p
      | CPatRecord l -> CPatRecord (List.map (fun (q, p) -> (qualid q, cases_pattern_expr p)) l)
      | CPatDelimiters (d, s, p) -> CPatDelimiters (d, s, cases_pattern_expr p)
      | CPatCast (p, c) -> CPatCast (cases_pattern_expr p, constr_expr c))

let erase_constr_expr = constr_expr

let trm ((c, e) : Genintern.glob_constr_and_expr) : Genintern.glob_constr_and_expr =
  (glob_constr c, Option.map constr_expr e)

(** {5 Patterns} *)

let rec pattern (p : uninstantiated_pattern) : uninstantiated_pattern = match p with
  | PExtra g -> PExtra (erase_genarg g)
  | PRef _ | PVar _ | PRel _ | PSort _ | PMeta _ | PInt _ | PFloat _ | PString _ as p -> p
  | PEvar (ev, l) -> PEvar (ev, List.map pattern l)
  | PApp (f, a) -> PApp (pattern f, Array.map pattern a)
  | PSoApp (v, l) -> PSoApp (v, List.map pattern l)
  | PProj (pr, c) -> PProj (pr, pattern c)
  | PLambda (na, t, b) -> PLambda (na, pattern t, pattern b)
  | PProd (na, t, b) -> PProd (na, pattern t, pattern b)
  | PLetIn (na, b, t, c) -> PLetIn (na, pattern b, Option.map pattern t, pattern c)
  | PIf (c, b1, b2) -> PIf (pattern c, pattern b1, pattern b2)
  | PCase (ci, po, c, br) ->
    PCase (ci, Option.map (fun (nas, p) -> (nas, pattern p)) po, pattern c,
           List.map (fun (i, nas, p) -> (i, nas, pattern p)) br)
  | PFix (r, (nas, tys, bds)) -> PFix (r, (nas, Array.map pattern tys, Array.map pattern bds))
  | PCoFix (i, (nas, tys, bds)) -> PCoFix (i, (nas, Array.map pattern tys, Array.map pattern bds))
  | PArray (a, d, t) -> PArray (Array.map pattern a, pattern d, pattern t)

let pat ((ids, c, p) : Genintern.glob_constr_pattern_and_expr) : Genintern.glob_constr_pattern_and_expr =
  (ids, trm c, pattern p)

(** {5 Occurrences, clauses, bindings, intro patterns} *)

let occurrences_gen (f : 'a -> 'a) = function
  | AllOccurrencesBut l -> AllOccurrencesBut (List.map f l)
  | OnlyOccurrences l -> OnlyOccurrences (List.map f l)
  | AllOccurrences | AtLeastOneOccurrence | NoOccurrences as o -> o

let occs : occurrences_expr -> occurrences_expr = fun o -> occurrences_gen int_or_var o

let clause { onhyps; concl_occs } =
  { onhyps = Option.map (List.map (fun ((o, id), fl) -> ((occs o, lident id), fl))) onhyps;
    concl_occs = occs concl_occs }

let quantified_hypothesis = function
  | NamedHyp id -> NamedHyp (lident id)
  | AnonHyp _ as h -> h

let bindings (f : 'a -> 'a) = function
  | ImplicitBindings l -> ImplicitBindings (List.map f l)
  | ExplicitBindings l ->
    ExplicitBindings (List.map (fun b ->
        let (h, c) = b.CAst.v in CAst.make (quantified_hypothesis h, f c)) l)
  | NoBindings -> NoBindings

let wbind (c, bl) = (trm c, bindings trm bl)
let wbind_arg (clear, c) = (clear, wbind c)

let rec ipat p = CAst.make (ipat_r p.CAst.v)

and ipat_r = function
  | IntroForthcoming _ | IntroNaming _ as p -> p
  | IntroAction a -> IntroAction (ipat_action a)

and ipat_action = function
  | IntroWildcard | IntroRewrite _ as a -> a
  | IntroOrAndPattern p -> IntroOrAndPattern (or_and_ipat_r p)
  | IntroInjection l -> IntroInjection (List.map ipat l)
  | IntroApplyOn (c, p) -> IntroApplyOn (CAst.make (trm c.CAst.v), ipat p)

and or_and_ipat_r = function
  | IntroOrPattern ll -> IntroOrPattern (List.map (List.map ipat) ll)
  | IntroAndPattern l -> IntroAndPattern (List.map ipat l)

let or_and_ipat p = CAst.make (or_and_ipat_r p.CAst.v)

let naming (n : Namegen.intro_pattern_naming_expr CAst.t) = CAst.make n.CAst.v

let destruction_arg (clear, d) =
  (clear, match d with
    | Tactics.ElimOnConstr c -> Tactics.ElimOnConstr (wbind c)
    | Tactics.ElimOnIdent id -> Tactics.ElimOnIdent (lident id)
    | Tactics.ElimOnAnonHyp _ as d -> d)

(** {5 Reduction expressions} *)

let cst : g_cst -> g_cst = or_var (fun (e, short) -> (e, Option.map lident short))

let red_flag fl = { fl with rConst = List.map cst fl.rConst }

let red_context ctx =
  Option.map (fun (o, u) ->
      (occs o, match u with Util.Inl c -> Util.Inl (cst c) | Util.Inr p -> Util.Inr (trm p)))
    ctx

(* A user reduction keeps its locations: its type is open. *)
let red_expr (r : Redexpr.glob_red_expr) : Redexpr.glob_red_expr = match r with
  | Red | Hnf | ExtraRedExpr _ | UserRed _ as r -> r
  | Simpl (fl, ctx) -> Simpl (red_flag fl, red_context ctx)
  | Cbv fl -> Cbv (red_flag fl)
  | Cbn fl -> Cbn (red_flag fl)
  | Lazy fl -> Lazy (red_flag fl)
  | Unfold l -> Unfold (List.map (fun (o, c) -> (occs o, cst c)) l)
  | Fold l -> Fold (List.map trm l)
  | Pattern l -> Pattern (List.map (fun (o, c) -> (occs o, trm c)) l)
  | CbvVm ctx -> CbvVm (red_context ctx)
  | CbvNative ctx -> CbvNative (red_context ctx)

(** {5 Tactics} *)

let ltac_ref : g_ref -> g_ref = or_var located

let message_token = function
  | MsgIdent id -> MsgIdent (lident id)
  | MsgString _ | MsgInt _ as m -> m

let inversion_strength = function
  | NonDepInversion (k, ids, p) ->
    NonDepInversion (k, List.map lident ids, Option.map (or_var or_and_ipat) p)
  | DepInversion (k, c, p) -> DepInversion (k, Option.map trm c, Option.map (or_var or_and_ipat) p)
  | InversionUsing (c, ids) -> InversionUsing (trm c, List.map lident ids)

let induction_clause (d, (eqn, as_), cl) =
  (destruction_arg d, (Option.map naming eqn, Option.map (or_var or_and_ipat) as_), Option.map clause cl)

let match_pattern = function
  | Term p -> Term (pat p)
  | Subterm (ido, p) -> Subterm (ido, pat p)

let match_context_hyp = function
  | Hyp (na, mp) -> Hyp (lname na, match_pattern mp)
  | Def (na, mv, mp) -> Def (lname na, match_pattern mv, match_pattern mp)

let rec atomic (t : glob_atomic_tactic_expr) : glob_atomic_tactic_expr = match t with
  | TacIntroPattern (ev, l) -> TacIntroPattern (ev, List.map ipat l)
  | TacApply (a, ev, cb, cl) ->
    TacApply (a, ev, List.map wbind_arg cb, List.map (fun (id, p) -> (lident id, Option.map ipat p)) cl)
  | TacElim (ev, cb, cbo) -> TacElim (ev, wbind_arg cb, Option.map wbind cbo)
  | TacCase (ev, cb) -> TacCase (ev, wbind_arg cb)
  | TacMutualFix (id, n, l) -> TacMutualFix (id, n, List.map (fun (id, n, c) -> (id, n, trm c)) l)
  | TacMutualCofix (id, l) -> TacMutualCofix (id, List.map (fun (id, c) -> (id, trm c)) l)
  | TacAssert (ev, b, otac, p, c) ->
    TacAssert (ev, b, Option.map (Option.map tactic) otac, Option.map ipat p, trm c)
  | TacGeneralize l -> TacGeneralize (List.map (fun ((o, c), na) -> ((occs o, trm c), na)) l)
  | TacLetTac (ev, na, c, cl, b, eqn) -> TacLetTac (ev, na, trm c, clause cl, b, Option.map naming eqn)
  | TacInductionDestruct (r, ev, (l, el)) ->
    TacInductionDestruct (r, ev, (List.map induction_clause l, Option.map wbind el))
  | TacReduce (r, cl) -> TacReduce (red_expr r, clause cl)
  | TacChange (check, op, c, cl) -> TacChange (check, Option.map trm op, trm c, clause cl)
  | TacRewrite (ev, l, cl, by) ->
    TacRewrite (ev, List.map (fun (b, m, c) -> (b, m, wbind_arg c)) l, clause cl, Option.map tactic by)
  | TacInversion (s, h) -> TacInversion (inversion_strength s, quantified_hypothesis h)

and tactic (t : glob_tactic_expr) : glob_tactic_expr = CAst.make (tactic_r t.CAst.v)

and tactic_r = function
  | TacAtom t -> TacAtom (atomic t)
  | TacThen (t1, t2) -> TacThen (tactic t1, tactic t2)
  | TacDispatch l -> TacDispatch (List.map tactic l)
  | TacExtendTac (tf, t, tl) -> TacExtendTac (Array.map tactic tf, tactic t, Array.map tactic tl)
  | TacThens (t, l) -> TacThens (tactic t, List.map tactic l)
  | TacThens3parts (t1, tf, t2, tl) ->
    TacThens3parts (tactic t1, Array.map tactic tf, tactic t2, Array.map tactic tl)
  | TacFirst l -> TacFirst (List.map tactic l)
  | TacSolve l -> TacSolve (List.map tactic l)
  | TacTry t -> TacTry (tactic t)
  | TacOr (t1, t2) -> TacOr (tactic t1, tactic t2)
  | TacOnce t -> TacOnce (tactic t)
  | TacExactlyOnce t -> TacExactlyOnce (tactic t)
  | TacIfThenCatch (t, tt, te) -> TacIfThenCatch (tactic t, tactic tt, tactic te)
  | TacOrelse (t1, t2) -> TacOrelse (tactic t1, tactic t2)
  | TacDo (n, t) -> TacDo (int_or_var n, tactic t)
  | TacTimeout (n, t) -> TacTimeout (int_or_var n, tactic t)
  | TacTime (s, t) -> TacTime (s, tactic t)
  | TacRepeat t -> TacRepeat (tactic t)
  | TacProgress t -> TacProgress (tactic t)
  | TacAbstract (t, id) -> TacAbstract (tactic t, id)
  | TacId l -> TacId (List.map message_token l)
  | TacFail (g, n, l) -> TacFail (g, int_or_var n, List.map message_token l)
  | TacLetIn (r, l, t) -> TacLetIn (r, List.map (fun (na, a) -> (lname na, tacarg a)) l, tactic t)
  | TacMatch (lz, t, rules) -> TacMatch (lz, tactic t, List.map match_rule rules)
  | TacMatchGoal (lz, lr, rules) -> TacMatchGoal (lz, lr, List.map match_rule rules)
  | TacFun (args, body) -> TacFun (args, tactic body)
  | TacArg a -> TacArg (tacarg a)
  | TacSelect (s, t) -> TacSelect (s, tactic t)
  | TacML (e, l) -> TacML (e, List.map tacarg l)
  | TacAlias (kn, l) -> TacAlias (kn, List.map tacarg l)

and tacarg = function
  | TacGeneric (q, g) -> TacGeneric (q, erase_genarg g)
  | ConstrMayEval m -> ConstrMayEval (may_eval m)
  | Reference r -> Reference (ltac_ref r)
  | TacCall c -> let (f, l) = c.CAst.v in TacCall (CAst.make (ltac_ref f, List.map tacarg l))
  | TacFreshId l -> TacFreshId (List.map (or_var (fun s -> s)) l)
  | Tacexp t -> Tacexp (tactic t)
  | TacPretype c -> TacPretype (trm c)
  | TacNumgoals -> TacNumgoals

and may_eval = function
  | ConstrTerm c -> ConstrTerm (trm c)
  | ConstrEval (r, c) -> ConstrEval (red_expr r, trm c)
  | ConstrContext (id, c) -> ConstrContext (lident id, trm c)
  | ConstrTypeOf c -> ConstrTypeOf (trm c)

and match_rule = function
  | Pat (hyps, mp, t) -> Pat (List.map match_context_hyp hyps, match_pattern mp, tactic t)
  | All t -> All (tactic t)

let erase_tactic = tactic

(** {5 The generic argument types this tree defines whose values hold a
    location} *)

let () =
  let open Stdarg in
  let open Tacarg in
  register_erase0 wit_int_or_var int_or_var;
  register_erase0 wit_nat_or_var int_or_var;
  register_erase0 wit_identref lident;
  register_erase0 wit_hyp lident;
  register_erase0 wit_ref (or_var located);
  register_erase0 wit_smart_global (or_var located);
  register_erase0 wit_constr trm;
  register_erase0 wit_uconstr trm;
  register_erase0 wit_open_constr trm;
  register_erase0 wit_clause_dft_concl clause;
  register_erase0 wit_open_binders (List.map local_binder);
  register_erase0 wit_intropattern ipat [@warning "-3"];
  register_erase0 wit_simple_intropattern ipat;
  register_erase0 wit_quant_hyp quantified_hypothesis;
  register_erase0 wit_constr_with_bindings wbind;
  register_erase0 wit_open_constr_with_bindings wbind;
  register_erase0 wit_bindings (bindings trm);
  register_erase0 wit_tactic tactic;
  register_erase0 wit_ltac_in_term (fun (ids, t) -> (ids, tactic t));
  register_erase0 wit_ltac tactic;
  register_erase0 wit_destruction_arg destruction_arg;
  register_erase0 Redexpr.wit_red_expr red_expr
