(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Univ
open UVars
open Constr
open Vars
open Declarations
open Declareops
open Environ
open Reduction
open Type_errors
open Context.Rel.Declaration
open Sorts

(* raises an anomaly if not an inductive type *)
let lookup_mind_specif env (kn,tyi) =
  let mib = Environ.lookup_mind kn env in
  if tyi >= Array.length mib.mind_packets then
    user_err Pp.(str "Inductive.lookup_mind_specif: invalid inductive index");
  (mib, mib.mind_packets.(tyi))

let find_rectype ?evars env c =
  let (t, l) = decompose_app_list (whd_all ?evars env c) in
  match kind t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

let find_inductive ?evars env c =
  let (t, l) = decompose_app_list (whd_all ?evars env c) in
  match kind t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_punivs ind))).mind_finite <> CoFinite -> (ind, l)
    | _ -> raise Not_found

let find_coinductive ?evars env c =
  let (t, l) = decompose_app_list (whd_all ?evars env c) in
  match kind t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_punivs ind))).mind_finite == CoFinite -> (ind, l)
    | _ -> raise Not_found

let inductive_params (mib,_) = mib.mind_nparams

let inductive_paramdecls (mib,u) =
  Vars.subst_instance_context u mib.mind_params_ctxt

let inductive_nnonrecparams mib = mib.mind_nparams - mib.mind_nparams_rec

let inductive_nonrec_rec_paramdecls (mib,u) =
  let nnonrecparamdecls = inductive_nnonrecparams mib in
  let paramdecls = inductive_paramdecls (mib,u) in
  Context.Rel.chop_nhyps nnonrecparamdecls paramdecls

let instantiate_inductive_constraints mib u =
  UVars.AbstractContext.instantiate u (Declareops.inductive_polymorphic_context mib)

(** Splits a fixpoint body between the context until the [recindx+1]-th
    assumption, and the rest of the body. Inlines local definitions,
    which is necessary for the computation of uniform arguments,
    and incidentally allows local definitions in the prefix to circumvent
    restrictions if their inlining passes them. *)
let split_struct_arg ?evars env recindx =
  let rec decrec env n ctx c =
    if Int.equal n 0 then ctx, c
    else
    let rc = whd_all ?evars env c in
    match kind rc with
    | Lambda (na, ty, bd) ->
        let d = LocalAssum (na, ty) in
        decrec (push_rel d env) (n-1) (Context.Rel.add d ctx) bd
    | _ -> invalid_arg "split_struct_arg"
  in
  decrec env (recindx + 1) Context.Rel.empty

(************************************************************************)

let instantiate_params t u args sign =
  let fail () =
    anomaly ~label:"instantiate_params" (Pp.str "type, ctxt and args mismatch.") in
  let (rem_args, subs, ty) =
    Context.Rel.fold_outside
      (fun decl (largs,subs,ty) ->
        match (decl, largs, kind ty) with
          | (LocalAssum _, a::args, Prod(_,_,t)) -> (args, a::subs, t)
          | (LocalDef (_,b,_), _, LetIn(_,_,_,t))    ->
            (largs, (substl subs (subst_instance_constr u b))::subs, t)
          | _                       -> fail ())
      sign
      ~init:(args,[],t)
  in
  let () = if not (List.is_empty rem_args) then fail () in
  substl subs ty

let full_constructor_instantiate (_,u,(mib,_),params) t =
  let inst_ind = subst_instance_constr u t in
   instantiate_params inst_ind u params mib.mind_params_ctxt

(************************************************************************)
(************************************************************************)

(* Functions to build standard types related to inductive *)

(*
Computing the actual sort of an applied or partially applied inductive type:

I_i: forall uniformparams:utyps, forall otherparams:otyps, Type(a)
uniformargs : utyps
otherargs : otyps
I_1:forall ...,s_1;...I_n:forall ...,s_n |- sort(C_kj(uniformargs)) = s_kj
s'_k = max(..s_kj..)
merge(..s'_k..) = ..s''_k..
--------------------------------------------------------------------
Gamma |- I_i uniformargs otherargs : phi(s''_i)

where

- if p=0, phi() = Prop
- if p=1, phi(s) = s
- if p<>1, phi(s) = sup(Set,s)

Remark: Set (predicative) is encoded as Type(0)
*)

(* Template polymorphism *)

type template_univ =
  | TemplateProp
  | TemplateAboveProp of Sorts.QVar.t * Universe.t
  | TemplateUniv of Universe.t

type template_subst = Sorts.Quality.t Int.Map.t * Universe.t Int.Map.t

let template_univ_quality = function
  | TemplateProp -> Sorts.Quality.qprop
  | TemplateUniv _ -> Sorts.Quality.qtype
  | TemplateAboveProp (q,_) -> Sorts.Quality.QVar q

(* this requires TemplateAboveProp to really be above prop *)
let max_template_quality a b =
  let open Sorts.Quality in
  match a, b with
  | QConstant QSProp, _ | _, QConstant QSProp -> assert false
  | QConstant QProp, q | q, QConstant QProp -> q
  | (QConstant QType as q), _ | _, (QConstant QType as q) -> q
  | QVar a', QVar b' ->
    if Sorts.QVar.equal a' b' then a
    else qtype

let template_univ_universe = function
  | TemplateProp -> Universe.type0
  | TemplateAboveProp (_,u) | TemplateUniv u -> u

let univ_bind_kind u =
  match Universe.level u with
  | None -> None
  | Some l -> Level.var_index l

let bind_kind = let open Sorts in function
  | SProp | Prop | Set -> assert false
  | Type u ->
    let u = univ_bind_kind u in
    assert (Option.has_some u);
    None, u
  | QSort (q,u) ->
    let q = Sorts.QVar.var_index q in
    let u = univ_bind_kind u in
    assert (Option.has_some q || Option.has_some u);
    q, u

(* Add a binding for a parameter binding qbind and ubind to su. *)
let cons_subst bind su (qsubst,usubst) =
  let qbind, ubind = bind_kind bind in
  let qsubst = match qbind with
    | None -> qsubst
    | Some qbind ->
      let sq = template_univ_quality su in
      Int.Map.update qbind (function
          | None -> Some sq
          | Some q0 -> Some (max_template_quality q0 sq))
        qsubst
  in
  let usubst = match ubind with
    | None -> usubst
    | Some ubind ->
      let u = template_univ_universe su in
      Int.Map.update ubind (function
          | None -> Some u
          | Some _ -> CErrors.anomaly Pp.(str "cons_subst found non linear template level."))
        usubst
  in
  qsubst, usubst

(* cons_default_subst adds the binding to the default universe to the substitution. *)
let cons_default_subst bind defaults (qsubst,usubst) =
  let qbind, ubind = bind_kind bind in
  let qsubst = match qbind with
    | None -> qsubst
    | Some qbind -> Int.Map.add qbind Sorts.Quality.qtype qsubst
  in
  let usubst = match ubind with
    | None -> usubst
    | Some ubind ->
      let u = UVars.subst_instance_universe defaults (Universe.make (Level.var ubind)) in
      Int.Map.update ubind (function
          | None -> Some u
          | Some _ -> CErrors.anomaly Pp.(str "cons_default_subst found non linear template level."))
        usubst
  in
  qsubst, usubst

type param_univs = (default:Sorts.t -> template_univ) list

(* Bind expected levels of parameters to actual levels *)
(* Propagate the new levels in the signature *)
let make_subst defaults =
  let rec make subst = function
    | LocalDef _ :: sign, exp, args ->
        make subst (sign, exp, args)
    | _d::sign, None::exp, args ->
        let args = match args with _::args -> args | [] -> [] in
        make subst (sign, exp, args)
    | LocalAssum (_,t)::sign, Some bind::exp, a::args ->
        (* [default] is used in error messages (e.g. when the user gave SProp) *)
        let _, default = Term.destArity t in
        let s = a ~default in
        make (cons_subst bind s subst) (sign, exp, args)
    | LocalAssum _ :: sign, Some bind::exp, [] ->
      make (cons_default_subst bind defaults subst) (sign, exp, [])
    | _sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
    | [], _, _ ->
        assert false
  in
  make (Int.Map.empty,Int.Map.empty)

let template_subst_universe (_,usubst) u =
  let supern u n = iterate Universe.super n u in
  let map (u,n) =
    match Level.var_index u with
    | None -> Universe.maken u n
    | Some u ->
      let u = Int.Map.get u usubst in
      supern u n
  in
  match List.map map (Universe.repr u) with
  | [] -> assert false
  | u :: rest ->
    List.fold_left Universe.sup u rest

let template_subst_sort (subst : template_subst) = function
| Sorts.Prop | Sorts.Set | Sorts.SProp as s -> s
| Sorts.Type u ->
  Sorts.sort_of_univ (template_subst_universe subst u)
| Sorts.QSort (q,u) ->
  let q = match Sorts.QVar.var_index q with
    | None -> Sorts.Quality.QVar q
    | Some q -> Int.Map.get q (fst subst)
  in
  (* shortcut for impredicative quality *)
  if Sorts.Quality.(equal qprop q) then Sorts.prop
  else Sorts.make q (template_subst_universe subst u)

let rec template_subst_ctx accu subs ctx params = match ctx, params with
| [], [] -> accu
| (LocalDef _ as decl) :: ctx, params ->
  template_subst_ctx (decl :: accu) subs ctx params
| (LocalAssum _ as decl) :: ctx, None :: params ->
  template_subst_ctx (decl :: accu) subs ctx params
| LocalAssum (na, t) :: ctx, Some s :: params ->
  let (decls, _) = Term.destArity t in
  let s = template_subst_sort subs s in
  let decl = LocalAssum (na, Term.it_mkProd_or_LetIn (mkSort s) decls) in
  template_subst_ctx (decl :: accu) subs ctx params
| _, [] | [], _ -> assert false

let template_subst_ctx subst ctx params = template_subst_ctx [] subst ctx params

let instantiate_template_constraints subst templ =
  let cstrs = UVars.UContext.constraints (UVars.AbstractContext.repr templ.template_context) in
  let foldq (q, cst, q') accq =
    let substq q = match q with
      | Quality.QConstant _ -> q
      | Quality.QVar q' ->
         begin
           match QVar.var_index q' with
           | None -> q
           | Some q' -> Int.Map.get q' (fst subst)
         end in
    ElimConstraints.add (substq q, cst, substq q') accq in
  let foldu (u, cst, v) accu =
    (* v is not a local universe by the unbounded from below property *)
    let u = match Level.var_index u with
      | None -> Universe.make u
      | Some u -> Int.Map.get u (snd subst)
    in
    (* if qsort, it is above prop *)
    let fold accu (u, n) = match n, cst with
      | 0, _ -> UnivConstraints.add (u, cst, v) accu
      | 1, UnivConstraint.Le -> UnivConstraints.add (u, UnivConstraint.Lt, v) accu
      | 1, (UnivConstraint.Eq | UnivConstraint.Lt) -> assert false (* FIXME? *)
      | _ -> assert false
    in
    List.fold_left fold accu (Univ.Universe.repr u)
  in
  PConstraints.fold (foldq, foldu) cstrs PConstraints.empty

let instantiate_template_universes mib args =
  let templ = match mib.mind_template with
  | None -> assert false
  | Some t -> t
  in
  let ctx = List.rev mib.mind_params_ctxt in
  let subst = make_subst templ.template_defaults (ctx,templ.template_param_arguments,args) in
  let ctx = template_subst_ctx subst ctx templ.template_param_arguments in
  let cstrs = instantiate_template_constraints subst templ in
  (cstrs, ctx, subst)

(* Type of an inductive type *)

let relevance_of_ind_body mip u =
  UVars.subst_instance_relevance u mip.mind_relevance

let relevance_of_inductive env (ind,u) =
  let _, mip = lookup_mind_specif env ind in
  relevance_of_ind_body mip u

let check_instance mib u =
  if not (match mib.mind_universes with
      | Monomorphic -> Instance.is_empty u
      | Polymorphic uctx -> Instance.length u = AbstractContext.size uctx)
  then CErrors.anomaly Pp.(str "bad instance length on mutind.")

let type_of_inductive_gen ((mib,mip),u) paramtyps =
  check_instance mib u;
  match mib.mind_template with
  | None ->
    let cst = instantiate_inductive_constraints mib u in
    subst_instance_constr u mip.mind_user_arity, cst
  | Some templ ->
    let cst, params, subst = instantiate_template_universes mib paramtyps in
    let ctx = (List.firstn mip.mind_nrealdecls mip.mind_arity_ctxt) @ params in
    let s = template_subst_sort subst templ.template_concl in
    Term.mkArity (ctx, s), cst

let type_of_inductive pind =
  let (ty, _cst) = type_of_inductive_gen pind [] in
  ty

let constrained_type_of_inductive pind =
  type_of_inductive_gen pind []

let type_of_inductive_knowing_parameters mip args =
  type_of_inductive_gen mip args

(************************************************************************)
(* Type of a constructor *)

let type_of_constructor_gen (cstr, u) (mib,mip) paramtyps =
  check_instance mib u;
  let i = index_of_constructor cstr in
  let nconstr = Array.length mip.mind_consnames in
  if i > nconstr then user_err Pp.(str "Not enough constructors in the type.");
  match mib.mind_template with
  | None ->
    let cst = instantiate_inductive_constraints mib u in
    subst_instance_constr u mip.mind_user_lc.(i-1), cst
  | Some _ ->
    let cst, params, _ = instantiate_template_universes mib paramtyps in
    let _, typ = Term.decompose_prod_n_decls (List.length mib.mind_params_ctxt) mip.mind_user_lc.(i - 1) in
    let typ = Term.it_mkProd_or_LetIn typ params in
    typ, cst

let type_of_constructor pcstr ind =
  let (ty, _cst) = type_of_constructor_gen pcstr ind [] in
  ty

let constrained_type_of_constructor cstru ind =
  type_of_constructor_gen cstru ind []

let type_of_constructor_knowing_parameters cstr specif args =
  type_of_constructor_gen cstr specif args

let arities_of_constructors (_,u) (_,mip) =
  let map (ctx, c) =
    let cty = Term.it_mkProd_or_LetIn c ctx in
    subst_instance_constr u cty
  in
  Array.map map mip.mind_nf_lc

let type_of_constructors (_,u) (_,mip) =
  Array.map (subst_instance_constr u) mip.mind_user_lc

let abstract_constructor_type_relatively_to_inductive_types_context ntyps mind t =
  let rec replace_ind k c =
    let hd, args = decompose_app c in
    match kind hd with
    | Ind ((mind',i),_) when MutInd.CanOrd.equal mind mind' ->
       mkApp (mkRel (ntyps+k-i), Array.map (replace_ind k) args)
    | _ -> map_with_binders succ replace_ind k c
  in
  replace_ind 0 t

(************************************************************************)

(** Elimination functions *)

let raw_eliminates_to = QGraph.ElimTable.eliminates_to

let eliminates_to g = QGraph.eliminates_to g

let sort_eliminates_to g s s' = eliminates_to g (Sorts.quality s) (Sorts.quality s')

type squash = SquashToSet | SquashToQuality of Quality.t

type 'a allow_elimination_actions =
  { not_squashed : 'a
  ; squashed_to_set_below : 'a
  ; squashed_to_set_above : 'a
  ; squashed_to_quality : Quality.t -> 'a }

let is_squashed_gen g nf_quality ((_,mip),u) =
  let s = mip.mind_sort in
  match mip.mind_squashed with
  | None -> None
  | Some squash ->
    let indq = nf_quality (UVars.subst_instance_quality u @@ Sorts.quality s) in
    match squash with
    | AlwaysSquashed ->
      begin match s with
      | Set -> Some SquashToSet
      | _ -> Some (SquashToQuality indq)
      end
    | SometimesSquashed squash ->
      (* impredicative set squashes are always quashed,
         so here if inds=Set it is a sort poly squash (see "foo6" in test sort_poly.v) *)
      if Quality.Set.for_all
          (fun q -> eliminates_to g indq (nf_quality (UVars.subst_instance_quality u q)))
          squash && not @@ Quality.is_qvar indq
      then None
      else Some (SquashToQuality indq)

let allowed_elimination_gen g nf_quality actions specifu s =
  match is_squashed_gen g nf_quality specifu with
  | None -> actions.not_squashed
  | Some SquashToSet ->
    begin match s with
      | SProp|Prop|Set -> actions.squashed_to_set_below
      | QSort _ | Type _ -> actions.squashed_to_set_above
    end
  | Some (SquashToQuality indq) -> actions.squashed_to_quality indq

let is_squashed env specif =
  is_squashed_gen (Environ.qualities env) Fun.id specif

let is_allowed_elimination_actions g s =
  { not_squashed = true
  ; squashed_to_set_below = true
  (* XXX in [Type u] case, should we check [u == set] in the ugraph? *)
  ; squashed_to_set_above = false
  ; squashed_to_quality
    = fun indq -> eliminates_to g indq (Sorts.quality s)}

let is_allowed_elimination env specifu s =
  let g = Environ.qualities env in
  allowed_elimination_gen g
    Fun.id
    (is_allowed_elimination_actions g s)
    specifu s

(* We always allow fixpoints on values in Prop (for the accessibility predicate for instance). *)
let is_allowed_fixpoint elim_to sind star =
  elim_to (Sorts.quality sind) Quality.qprop ||
    elim_to (Sorts.quality sind) (Sorts.quality star)

(************************************************************************)

let is_private (mib,_) = mib.mind_private = Some true
let is_primitive_record (_,mip) =
  match mip.mind_record with
  | PrimRecord _ -> true
  | NotRecord | FakeRecord -> false

(** {6 Changes of representation of Case nodes} *)

(** Provided:
    - a universe instance [u]
    - a term substitution [subst]
    - name replacements [nas]
    [instantiate_context u subst nas ctx] applies both [u] and [subst] to [ctx]
    while replacing names using [nas] (order reversed)
*)
let instantiate_context = Environ.instantiate_context

let expand_arity = Environ.expand_arity

let expand_branch_contexts = Environ.expand_branch_contexts

type ('constr,'types,'r) pexpanded_case =
  (case_info * ('constr * 'r) * 'constr pcase_invert * 'constr * 'constr array)

type expanded_case = (constr,types,Sorts.relevance) pexpanded_case

let expand_case_specif mib (ci, u, params, (p,rp), iv, c, br) =
  (* Γ ⊢ c : I@{u} params args *)
  (* Γ, indices, self : I@{u} params indices ⊢ p : Type *)
  let mip = mib.mind_packets.(snd ci.ci_ind) in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
  (* Expand the return clause *)
  let ep =
    let (nas, p) = p in
    let realdecls = expand_arity (mib, mip) (ci.ci_ind, u) params nas in
    Term.it_mkLambda_or_LetIn p realdecls
  in
  (* Expand the branches *)
  let ebr =
    let build_one_branch i (nas, br) (ctx, _) =
      let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
      let ctx = instantiate_context u paramsubst nas ctx in
      Term.it_mkLambda_or_LetIn br ctx
    in
    Array.map2_i build_one_branch br mip.mind_nf_lc
  in
  (ci, (ep,rp), iv, c, ebr)

let expand_case env (ci, _, _, _, _, _, _ as case) =
  let specif = Environ.lookup_mind (fst ci.ci_ind) env in
  expand_case_specif specif case

let contract_case env (ci, (p,rp), iv, c, br) =
  let (mib, mip) = lookup_mind_specif env ci.ci_ind in
  let (arity, p) = Term.decompose_lambda_n_decls (mip.mind_nrealdecls + 1) p in
  let (u, pms) = match arity with
  | LocalAssum (_, ty) :: _ ->
    (** Last binder is the self binder for the term being eliminated *)
    let (ind, args) = decompose_app ty in
    let (ind, u) = destInd ind in
    let () = assert (QInd.equal env ind ci.ci_ind) in
    let pms = Array.sub args 0 mib.mind_nparams in
    (** Unlift the parameters from under the index binders *)
    let dummy = List.make mip.mind_nrealdecls mkProp in
    let pms = Array.map (fun c -> Vars.substl dummy c) pms in
    (u, pms)
  | _ -> assert false
  in
  let p =
    let nas = Array.of_list (List.rev_map get_annot arity) in
    ((nas, p),rp)
  in
  let map i br =
    let (ctx, br) = Term.decompose_lambda_n_decls mip.mind_consnrealdecls.(i) br in
    let nas = Array.of_list (List.rev_map get_annot ctx) in
    (nas, br)
  in
  (ci, u, pms, p, iv, c, Array.mapi map br)

(************************************************************************)
(* Type of case branches *)

(* [p] is the predicate, [i] is the constructor number (starting from 0),
   and [cty] is the type of the constructor (params not instantiated) *)
let build_branches_type (ind,u) (_,mip as specif) params p =
  let build_one_branch i (ctx, c) =
    let cty = Term.it_mkProd_or_LetIn c ctx in
    let typi = full_constructor_instantiate (ind,u,specif,params) cty in
    let (cstrsign,ccl) = Term.decompose_prod_decls typi in
    let nargs = Context.Rel.length cstrsign in
    let (_,allargs) = decompose_app_list ccl in
    let (lparams,vargs) = List.chop (inductive_params specif) allargs in
    let cargs =
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let dep_cstr = Term.applist (mkConstructU (cstr,u),lparams@(Context.Rel.instance_list mkRel 0 cstrsign)) in
      vargs @ [dep_cstr] in
    let base = Term.lambda_appvect_decls (mip.mind_nrealdecls+1) (lift nargs p) (Array.of_list cargs) in
    Term.it_mkProd_or_LetIn base cstrsign in
  Array.mapi build_one_branch mip.mind_nf_lc

(************************************************************************)
(* Checking the case annotation is relevant *)

let check_case_info env (indsp,u) ci =
  let (mib,mip as spec) = lookup_mind_specif env indsp in
  if
    not (QInd.equal env indsp ci.ci_ind) ||
    not (Int.equal mib.mind_nparams ci.ci_npar) ||
    not (Array.equal Int.equal mip.mind_consnrealdecls ci.ci_cstr_ndecls) ||
    not (Array.equal Int.equal mip.mind_consnrealargs ci.ci_cstr_nargs) ||
    is_primitive_record spec
  then raise (TypeError(env,WrongCaseInfo((indsp,u),ci)))


(************************************************************************)
(************************************************************************)

let apply_branch ((_, i), _u) args ci lf =
  let args = List.skipn ci.ci_npar args in
  let br = lf.(i - 1) in
  let ctx, br = Term.decompose_lambda_n_decls ci.ci_cstr_ndecls.(i - 1) br in
  let subst = subst_of_rel_context_instance_list ctx args in
  Vars.substl subst br

let contract_fix ((recindices,bodynum),(_,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    mkFix ((recindices,ind),typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

let contract_cofix (bodynum,(_,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let coind = nbodies-j-1 in
    mkCoFix (coind,typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(************************************************************************)
(************************************************************************)

(* Guard conditions for fix and cofix-points *)

(* Check if t is a subterm of Rel n, and gives its specification,
   assuming lst already gives index of
   subterms with corresponding specifications of recursive arguments *)

(* A powerful notion of subterm *)

(* To each inductive definition corresponds an array describing the
   structure of recursive arguments for each constructor, we call it
   the recursive spec of the type (it has type recargs vect).  For
   checking the guard, we start from the decreasing argument (Rel n)
   with its recursive spec.  During checking the guardness condition,
   we collect patterns variables corresponding to subterms of n, each
   of them with its recursive spec.  They are organised in a list lst
   of type (int * recargs) list which is sorted with respect to the
   first argument.
*)

(*************************************************************)
(* Environment annotated with marks on recursive arguments *)

(* tells whether it is a strict or loose subterm *)
type size = Large | Strict

(* merging information *)
let size_glb s1 s2 =
  match s1,s2 with
      Strict, Strict -> Strict
    | _ -> Large

(* possible specifications for a term:
   - Not_subterm: when the size of a term is not related to the
     recursive argument of the fixpoint
   - Internally_bound_subterm: when the recursive call is in a subterm
     of a redex and the recursive argument is bound to a variable
     which will be instantiated by reducing the redex; the integers
     refer to the number of redexes stacked, with 1 counting for the
     variables bound at head in the body of the fix (as e.g. [x] in
     [fix f n := fun x => f x]); there may be several such indices
     because [match] subterms may have combine several results;
   - Subterm: when the term is a subterm of the recursive argument
       the wf_paths argument specifies which subterms are recursive;
     the [int list] is used in the [match] case where one branch of
     the [match] might be a subterm but (an arbitrary number of)
     others are calls to bound variables
   - Dead_code: when the term has been built by elimination over an
       empty type
 *)

type subterm_spec =
    Subterm of (Int.Set.t * size * wf_paths)
  | Dead_code
  | Not_subterm
  | Internally_bound_subterm of Int.Set.t

let is_norec_path t = match Rtree.dest_head t with
| Norec -> true
| Mrec _ -> false
| exception (Failure _) -> false

let inter_recarg r1 r2 = if eq_recarg r1 r2 then Some r1 else None

let inter_wf_paths = Rtree.inter Declareops.eq_recarg inter_recarg Norec

let incl_wf_paths = Rtree.incl Declareops.eq_recarg inter_recarg Norec

let spec_of_tree internal t =
  if is_norec_path t
  then Not_subterm
  else Subterm (internal, Strict, t)

let merge_internal_subterms l1 l2 =
  Int.Set.union l1 l2

let inter_spec s1 s2 =
  match s1, s2 with
  | _, Dead_code -> s1
  | Dead_code, _ -> s2
  | Not_subterm, _ -> s1
  | _, Not_subterm -> s2
  | Internally_bound_subterm l1, Internally_bound_subterm l2 -> Internally_bound_subterm (merge_internal_subterms l1 l2)
  | Subterm (l1,a1,t1), Internally_bound_subterm l2 -> Subterm (merge_internal_subterms l1 l2,a1,t1)
  | Internally_bound_subterm l1, Subterm (l2,a2,t2) -> Subterm (merge_internal_subterms l1 l2,a2,t2)
  | Subterm (l1,a1,t1), Subterm (l2,a2,t2) ->
     Subterm (merge_internal_subterms l1 l2, size_glb a1 a2, inter_wf_paths t1 t2)

let subterm_spec_glb =
  Array.fold_left inter_spec Dead_code

type guard_env =
  { env     : env;
    (* dB of last fixpoint *)
    rel_min : int;
    (* dB of variables denoting subterms *)
    genv    : subterm_spec Lazy.t list;
  }

let make_renv env recarg tree =
  { env = env;
    rel_min = recarg+2; (* recarg = 0 ==> Rel 1 -> recarg; Rel 2 -> fix *)
    genv = [Lazy.from_val(Subterm(Int.Set.empty, Large,tree))] }

let push_var renv (x,ty,spec) =
  { env = push_rel (LocalAssum (x,ty)) renv.env;
    rel_min = renv.rel_min+1;
    genv = spec:: renv.genv }

let push_let renv (x,c,ty,spec) =
  { env = push_rel (LocalDef (x,c,ty)) renv.env;
    rel_min = renv.rel_min+1;
    genv = spec:: renv.genv }

let assign_var_spec renv (i,spec) =
  { renv with genv = List.assign renv.genv (i-1) spec }

let push_var_renv renv n (x,ty) =
  let spec = Lazy.from_val (if n >= 1 then Internally_bound_subterm (Int.Set.singleton n) else Not_subterm) in
  push_var renv (x,ty,spec)

(* Fetch recursive information about a variable p *)
let subterm_var p renv =
  try Lazy.force (List.nth renv.genv (p-1))
  with Failure _ | Invalid_argument _ -> (* outside context of the fixpoint *) Not_subterm

let push_ctxt_renv renv ctxt =
  let n = Context.Rel.length ctxt in
  { env = push_rel_context ctxt renv.env;
    rel_min = renv.rel_min+n;
    genv = iterate (fun ge -> lazy Not_subterm::ge) n renv.genv }

let push_fix_renv renv (_,v,_ as recdef) =
  let n = Array.length v in
  { env = push_rec_types recdef renv.env;
    rel_min = renv.rel_min+n;
    genv = iterate (fun ge -> lazy Not_subterm::ge) n renv.genv }

(* The chain of abstractions that [raw_prefix_escapes] and
   [check_erased_prefix] follow, with each let's annotation and each cast's
   type taken out. Nothing evaluates those types, so a mention of a
   recursive function there is harmless, and a binder read only there is a
   DEAD binder: its value is then reported, because call-by-value evaluation
   computes it all the same. Only the chain the walks follow is erased (the
   [needed] abstractions, the lets and casts between them, and the bodies of
   the beta redexes they reduce); a type that reaches the walks another way
   is still a position. A lambda's domain is kept: it stays in the context
   [split_struct_arg] returns. *)
let rec erase_chain_types needed c =
  if Int.equal needed 0 then c
  else match kind c with
    | Lambda (na, ty, bd) -> mkLambda (na, ty, erase_chain_types (needed-1) bd)
    | LetIn (na, v, _, bd) -> mkLetIn (na, v, mkProp, erase_chain_types needed bd)
    | Cast (c, _, _) -> erase_chain_types needed c
    | App (f, args) when isLambda f ->
      mkApp (erase_beta_types needed f (Array.length args), args)
    | _ -> c
and erase_beta_types needed f nargs =
  if Int.equal nargs 0 then erase_chain_types needed f
  else match kind f with
    | Lambda (na, ty, bd) -> mkLambda (na, ty, erase_beta_types needed bd (nargs-1))
    | _ -> f

(* The guard analysis measures a fixpoint body after [split_struct_arg] has
   reduced its binder prefix away, but the kernel stores the body as
   WRITTEN, so an occurrence of a recursive function that the reduction
   ERASES is checked by nothing and is still evaluated. [raw_prefix_escapes]
   reduces the head of the body the way [whd_all] does in [split_struct_arg]
   and [inductive_of_mutfix], until it has gone under the [recindx + 1]
   abstractions of the prefix, and reports whether a function of the block
   sits in material this reduction drops:

   - a lambda's domain, a let's annotation and a cast's type. The
     annotations and casts of the chain of abstractions are taken out first
     ([erase_chain_types]): nothing evaluates them. A domain of the prefix
     stays in the context [split_struct_arg] returns: leaving it to
     [check_nested_fix_body] reaches a kernel anomaly on breaka/D5.v, and one
     that reaches the block through a let reaches the anomaly "Bad
     occurrence of recursive call" in [inductive_of_mutfix];
   - the value of a [let], the argument of a beta redex and the argument of
     a constructor (or the value of one of its let-ins) passed to the
     selected branch of a match, when its binder is not read (a binder read
     only in an erased type is not read);
   - what iota of a match or of a projection on a constructor drops: the
     return predicate, the parameters of the match, its inversion indices,
     the branches it does not select, the constructor's parameters, the
     fields a projection does not select. The types of the constructor's
     arguments are not dropped material: they mention only the parameters,
     which are checked, and earlier arguments, which are kept or checked;
   - when the walk stops at a head it does not take apart (a fixpoint or a
     cofixpoint to unfold, a constant without a value: an axiom, an opaque
     or primitive constant, a rewrite-rule symbol; a match or a projection
     whose argument does not reduce to a constructor, a variable without a
     value, an evar, a function of the block), everything that is left:
     the reduction may erase in it in ways the walk does not model.

   "Sits" means: mentions a function of the block, directly or through the
   values of the variables it reads ([closure_reaches]). A value that is
   bound and read is not dropped: the reduction puts it where its binder is
   read, so it reaches the analysis or is dropped there, and checked, later.

   The walk is a lazy Krivine machine, the reduction strategy of [whd_all]
   (kernel/cClosure.ml): a closure (a term with the environment of the
   binders the walk went under) applied to a stack of arguments, with a
   stack of pending matches and projections whose scrutinee is being
   reduced, kept on the heap. Beta and zeta bind a value instead of
   substituting it. A bound value, a constant and a local definition read
   at the head are reduced to head normal form once, and the result is
   shared by every later read (the update frames of [whd_all]; an update
   frame pushed on another one with no argument in between replaces it,
   as [compact_stack] does there, so a chain of reads of shared values
   costs no frames). Terms are annotated with their free variables
   ([pterm]) lazily, node by node, the first time the walk asks; a
   constructor's declared let-in values and its inductive's let-in
   parameter values are annotated once per constructor and universe
   instance ([ctor_decls]). A closure made from a constant or a section
   variable is closed, and nothing in it is scanned while the walk has
   bound nothing inside it. Dropped terms are not walked, only their free
   variables are looked up, and each bound value is examined once
   ([pb_reaches]). So the walk makes the steps [whd_all] makes, each at a
   constant cost (a logarithmic one for an environment lookup, and the
   size of what a step drops for its free variables), and nothing it does
   nests on the program stack beyond the depth of a term
   (test-suite/complexity/guard_prefix_steps_*.v).

   A body that does not mention the block is accepted first: nothing in it
   can. Otherwise, until its first step the walk does what the rule did
   before it took steps (release-8 a3a27a829aa2): a let, a beta redex, a
   cast, an abstraction of the prefix, with the same check of a binder that
   is not read. That rule stopped at any other head, and refused when the
   term there reached the block; the walk takes the step instead, and when
   it stops it refuses only when what is left reaches the block, so every
   body the rule accepted is accepted the same way. The steps find the
   abstractions behind an Equations let-pattern ([let H := H f in let (s, p)
   := H in (fun s0 p0 t => ...) s p]), behind [id (fun n => ...)] and behind
   a helper applied to a partial call ([step (rec a)]); stock 9.2.0 accepts
   these definitions and the rule without steps refused them
   (test-suite/success/guard_prefix_let_pattern.v, guard_prefix_head_step.v,
   guard_prefix_min_*.v). Every term a step keeps is a term [whd_all] keeps,
   so it is walked further or reaches the analysis; every term it drops is
   held to the rule above (test-suite/failure/guard_prefix_head_step_*.v). *)

(* A term, with its free variables (the occurrences [noccur_with_meta]
   sees, sorted) and the subterms the walk takes apart, each computed and
   kept when it is first asked for, so that a part of the body the walk
   never reaches costs nothing. The subterms ([pt_sub]) are: a lambda's
   domain and body; a let's value, type and body; a cast's term and type;
   an application's head and arguments; a projection's argument; a match's
   scrutinee, return predicate, parameters, inversion indices and
   branches, in that order. Other terms have none. *)
type pterm = {
  pt : constr;
  mutable pt_fv_ : int array option;
  mutable pt_sub_ : pterm array option;
  mutable pt_read_ : bool option;   (* abstraction or let: its body reads its binder *)
  mutable pt_drop_ : int array option array; (* match: what iota on each constructor drops *)
}

let pterm_of c = { pt = c; pt_fv_ = None; pt_sub_ = None; pt_read_ = None; pt_drop_ = [||] }

let pt_fv t = match t.pt_fv_ with
  | Some a -> a
  | None ->
    let rec go d acc c = match kind c with
      | Rel j -> if j > d then (j - d) :: acc else acc
      | App (f, _) when (match kind f with Meta _ -> true | Cast (m, _, _) -> isMeta m | _ -> false) -> acc
      | Evar _ -> acc
      | _ -> Constr.fold_constr_with_binders succ go d acc c
    in
    let a = Array.of_list (List.sort_uniq Int.compare (go 0 [] t.pt)) in
    let () = t.pt_fv_ <- Some a in
    a

let pt_sub t = match t.pt_sub_ with
  | Some a -> a
  | None ->
    let a = match kind t.pt with
      | Lambda (_, ty, b) -> [| pterm_of ty; pterm_of b |]
      | LetIn (_, v, ty, b) -> [| pterm_of v; pterm_of ty; pterm_of b |]
      | Cast (c, _, ty) -> [| pterm_of c; pterm_of ty |]
      | App (f, _) when (match kind f with Meta _ -> true | Cast (m, _, _) -> isMeta m | _ -> false) ->
        [||]
      | App (f, args) -> Array.append [| pterm_of f |] (Array.map pterm_of args)
      | Proj (_, _, c) -> [| pterm_of c |]
      | Case (_, _, pms, ((_, p), _), iv, tm, br) ->
        let indices = match iv with NoInvert -> [||] | CaseInvert { indices } -> indices in
        Array.concat [
          [| pterm_of tm; pterm_of p |]; Array.map pterm_of pms; Array.map pterm_of indices;
          Array.map (fun (_, b) -> pterm_of b) br ]
      | _ -> [||]
    in
    let () = t.pt_sub_ <- Some a in
    a

(* The slot where the free variables of what iota of the match [t] on its
   [i]-th constructor drops are kept. *)
let pt_drop t nbranches =
  let () = if Int.equal (Array.length t.pt_drop_) 0 then t.pt_drop_ <- Array.make nbranches None in
  t.pt_drop_

(* Whether the body of the abstraction or let [t] reads its binder,
   computed once: the walk asks it again at every application of the same
   abstraction. *)
let pt_binder_read t = match t.pt_read_ with
  | Some b -> b
  | None ->
    let b = match kind t.pt with
      | Lambda (_, _, bd) | LetIn (_, _, _, bd) -> not (Vars.noccurn 1 bd)
      | _ -> assert false
    in
    let () = t.pt_read_ <- Some b in
    b

type prefix_binding = {
  pb_value : prefix_closure option; (* [None] for an abstraction of the prefix *)
  mutable pb_reaches : bool option; (* whether the value reaches the block, once known *)
  mutable pb_inert : prefix_inert option; (* its shape as a dropped term, once known *)
  pb_whnf : prefix_whnf;            (* its head normal form, once computed *)
}
(* A head normal form: a closure at an abstraction or a constructor, and
   the arguments it is applied to; or the cell of another value whose head
   normal form is this one's. *)
and prefix_whnf = { mutable pw : prefix_whnf_state }
and prefix_whnf_state =
  | PWUnknown
  | PWDone of prefix_closure * prefix_closure list
  | PWSame of prefix_whnf
(* In [pc_term], [Rel j] with [j <= pe_len] is the binding
   [Int.Map.find (pe_len - j + 1) pe_map], and [Rel j] with [j > pe_len] is
   [Rel (j - pe_len + pe_shift)] of the environment of the block, whose
   [Rel 1] to [Rel nbfix] are the functions of the block. *)
and prefix_closure = { pc_term : pterm; pc_env : prefix_env }
and prefix_env = { pe_len : int; pe_map : prefix_binding Int.Map.t; pe_shift : int }
(* The shape of a term that is DROPPED, as far as the block is concerned: a
   function of the block applied to those arguments, each with the
   environment it lives in; an abstraction whose body is inert unapplied;
   or a term that may make a call. See [summary]. *)
and prefix_inert =
  | PIHead of int * prefix_closure list
  | PIAbs
  | PINot

(* What the walk resumes once the scrutinee it is reducing is a constructor
   (a match, held as its term with its environment, or a projection), or
   once a shared value is in head normal form (an update). Each holds the
   arguments the result is applied to. *)
type prefix_frame =
  | PFCase of prefix_env * pterm * prefix_closure list
  | PFProj of Projection.t * prefix_closure list
  | PFUpdate of prefix_whnf * prefix_closure list

exception PrefixEscape

let raw_prefix_escapes env nvect recindx body =
  let nbfix = Array.length nvect in
  let empty = { pe_len = 0; pe_map = Int.Map.empty; pe_shift = 0 } in
  (* The environment of a closed term (the value of a constant or of a
     section variable): it has no free variable, so nothing in it can
     reach the block, and the walk never looks a variable up in it. *)
  let closed = { pe_len = 0; pe_map = Int.Map.empty; pe_shift = -1 } in
  let clos e c = { pc_term = c; pc_env = e } in
  let binding e j = Int.Map.find (e.pe_len - j + 1) e.pe_map in
  let push e b =
    { e with pe_len = e.pe_len + 1; pe_map = Int.Map.add (e.pe_len + 1) b e.pe_map } in
  let has_rel a k =
    let rec search lo hi =
      lo < hi &&
      (let m = (lo + hi) / 2 in
       let x = a.(m) in
       Int.equal x k || (if x < k then search (m + 1) hi else search lo m))
    in
    search 0 (Array.length a) in
  (* Whether a bound value reaches the block: a depth-first search, with its
     own stack, of the values it reads (they were bound before it, so there
     is no cycle); every value it finishes is memoised. *)
  let binding_reaches b0 =
    match b0.pb_reaches with
    | Some r -> r
    | None ->
      let frame b = match b.pb_value with
        | Some v -> (b, v.pc_env, pt_fv v.pc_term, ref 0)
        | None -> assert false (* an abstraction has [pb_reaches = Some false] *)
      in
      let found st = List.iter (fun (b, _, _, _) -> b.pb_reaches <- Some true) st; true in
      let rec loop = function
        | [] -> false
        | ((b, e, rels, i) :: rest) as st ->
          if !i >= Array.length rels then
            let () = b.pb_reaches <- Some false in
            loop rest
          else
            let j = rels.(!i) in
            let () = incr i in
            if j > e.pe_len then
              if e.pe_shift < 0 || j - e.pe_len + e.pe_shift <= nbfix then found st else loop st
            else
              let b' = binding e j in
              match b'.pb_reaches with
              | Some true -> found st
              | Some false -> loop st
              | None -> loop (frame b' :: st)
      in
      loop [frame b0]
  in
  (* Whether free variables [rels] of a term under [d] binders, in [e],
     reach the block. *)
  let rels_reach e d rels =
    let rec go i =
      i < Array.length rels &&
      (let j = rels.(i) - d in
       (j > 0 &&
        (if j > e.pe_len then e.pe_shift < 0 || j - e.pe_len + e.pe_shift <= nbfix
         else binding_reaches (binding e j)))
       || go (i + 1))
    in
    go 0 in
  (* A closed term in a closed environment that has no binding yet can
     reach nothing; once the walk binds something there, its variables are
     looked up as everywhere else (a variable above the bindings of a
     closed environment cannot exist, and counts as reaching). *)
  let closure_reaches e d c =
    not (e.pe_shift < 0 && Int.equal e.pe_len 0) && rels_reach e d (pt_fv c) in
  let new_whnf () = { pw = PWUnknown } in
  let assum e =
    push e { pb_value = None; pb_reaches = Some false;
             pb_inert = Some PINot; pb_whnf = new_whnf () } in
  (* A term the reduction DROPS and that reaches the block is still let
     through when it is INERT: a function of the block applied to at most
     its own structural index of arguments, possibly under abstractions and
     through reads of bound values, with nothing else in it reaching the
     block. No reduction unfolds such a term, because fix-iota needs its
     structural argument, and a dropped term is never at the head of an
     application, so it is discarded without making a call.

     [summary e t args] describes [t] in [e], applied to [args]. The summary
     of a bound value is memoised ([pb_inert]), so an alias chain is
     followed once and the arguments compose by concatenation.

     Such an occurrence is in the body as WRITTEN and not in the body the
     analysis measures, so the uniform-parameter count of the block must see
     it: [bound] keeps, over all of them, the number of leading arguments
     that are the binders crossed, in order, which is the count
     [find_uniform_parameters] gives an occurrence and the count stock Rocq
     gives it in the raw body. An argument in the environment of a
     constant's body counts for nothing: it is no binder of this body. *)
  let bound = ref max_int in
  let rec summary e t args =
    let sub = pt_sub t in
    match kind t.pt with
    | Lambda _ ->
      if not (List.is_empty args) then PINot
      else if closure_reaches e 0 sub.(0) then PINot
      else if inert_at (assum e) sub.(1) then PIAbs else PINot
    | App _ when not (Array.is_empty sub) ->
      let n = Array.length sub - 1 in
      let rec bad k = k <= n && (closure_reaches e 0 sub.(k) || bad (k + 1)) in
      if bad 1 then PINot
      else
        let rec go k acc = if k < 1 then acc else go (k - 1) (clos e sub.(k) :: acc) in
        summary e sub.(0) (go n args)
    | Rel j when j <= e.pe_len ->
      let b = binding e j in
      begin match b.pb_value with
      | None -> PINot
      | Some w ->
        let s = match b.pb_inert with
          | Some s -> s
          | None ->
            let s = summary w.pc_env w.pc_term [] in
            let () = b.pb_inert <- Some s in
            s
        in
        begin match s with
        | PIHead (i, l) -> PIHead (i, l @ args)
        | PIAbs -> if List.is_empty args then PIAbs else PINot
        | PINot -> PINot
        end
      end
    | Rel j ->
      let o = j - e.pe_len + e.pe_shift in
      if e.pe_shift >= 0 && o >= 1 && o <= nbfix then PIHead (nbfix - o, args) else PINot
    | _ -> PINot
  (* [c] in [e] is inert; the count it allows is kept in [bound]. *)
  and inert_at e c =
    match summary e c [] with
    | PIHead (i, l) ->
      List.length l <= nvect.(i) && (bound := min !bound (uniform_count l); true)
    | PIAbs -> true
    | PINot -> false
  and uniform_count args =
    let rec go j = function
      | a :: rest ->
        begin match kind a.pc_term.pt with
        | Rel m when Int.equal a.pc_env.pe_shift 0
                     && Int.equal m (a.pc_env.pe_len - j) -> go (j + 1) rest
        | _ -> j
        end
      | [] -> j
    in
    go 0 args
  in
  (* [c] in [e], under [d] binders of its own, is inert. *)
  let inert e d c = inert_at (iterate assum d e) c in
  let drop_under e d c =
    if closure_reaches e d c && not (inert e d c) then raise_notrace PrefixEscape in
  let drop e c = drop_under e 0 c in
  let drop_clos v = drop v.pc_env v.pc_term in
  (* A binding of [v] to a binder; a binder that is not read drops [v] *)
  let binding_of v read =
    if read then
      { pb_value = Some v; pb_reaches = None; pb_inert = None; pb_whnf = new_whnf () }
    else
      let () = drop_clos v in
      (* Not [Some false]: [drop_clos] now lets an INERT value that reaches
         the block through, so this binding may reach it. An unread binder
         is read nowhere in the branch, but [branch_env] binds the match
         parameters unread into the environment a constructor's let-in
         values live in, and such a value can read it; recording [Some false]
         would hide the occurrence from that value's own [drop]. Computed
         lazily, as for a read binder. *)
      { pb_value = Some v; pb_reaches = None;
        pb_inert = None; pb_whnf = new_whnf () }
  in
  let bind e v read = push e (binding_of v read) in
  let push_args e sub stack =
    let rec go k s = if Int.equal k 0 then s else go (k - 1) (clos e sub.(k) :: s) in
    go (Array.length sub - 1) stack in
  (* Shared head normal forms of constants (by constant and universe
     instance), section variables and local definitions of the block's
     environment (by index). *)
  let const_whnf = ref Cmap.empty in
  let var_whnf = ref Id.Map.empty in
  let rel_whnf = ref Int.Map.empty in
  let const_cell (cst, u) =
    let l = Option.default [] (Cmap.find_opt cst !const_whnf) in
    match List.find_opt (fun (u', _) -> UVars.Instance.equal u u') l with
    | Some (_, w) -> w
    | None ->
      let w = new_whnf () in
      let () = const_whnf := Cmap.add cst ((u, w) :: l) !const_whnf in
      w
  in
  let var_cell id = match Id.Map.find_opt id !var_whnf with
    | Some w -> w
    | None -> let w = new_whnf () in let () = var_whnf := Id.Map.add id w !var_whnf in w in
  let rel_cell o = match Int.Map.find_opt o !rel_whnf with
    | Some w -> w
    | None -> let w = new_whnf () in let () = rel_whnf := Int.Map.add o w !rel_whnf in w in
  (* The cell a chain of [PWSame] leads to, with the chain made to point
     there (two loops, so a long chain costs no stack). *)
  let resolve w =
    let rec root w = match w.pw with PWSame w' -> root w' | PWUnknown | PWDone _ -> w in
    let r = root w in
    let rec compress w = match w.pw with
      | PWSame w' when w' != r -> let () = w.pw <- PWSame r in compress w'
      | PWSame _ | PWUnknown | PWDone _ -> ()
    in
    let () = compress w in
    r
  in
  (* The positions of the parts of a match [c] in [pt_sub c] *)
  let case_parts c = match kind c.pt with
    | Case (ci, u, pms, ((pnas, _), _), iv, _, br) ->
      let npms = Array.length pms in
      let nidx = match iv with NoInvert -> 0 | CaseInvert { indices } -> Array.length indices in
      (ci, u, pms, pnas, br, npms, nidx)
    | _ -> assert false
  in
  (* The free variables of what iota of the match [c] on its [i]-th
     constructor drops: its return predicate, parameters, inversion indices
     and other branches. Computed once per match and constructor. *)
  let case_drop_rels c i =
    let (_, _, _, pnas, br, npms, nidx) = case_parts c in
    let slots = pt_drop c (Array.length br) in
    match slots.(i - 1) with
    | Some r -> r
    | None ->
      let under n t acc =
        Array.fold_right (fun j acc -> if j > n then (j - n) :: acc else acc) (pt_fv t) acc in
      let l = under (Array.length pnas) (pt_sub c).(1) [] in
      let l = ref l in
      let () = for k = 2 to 1 + npms + nidx do l := under 0 (pt_sub c).(k) !l done in
      let () = Array.iteri (fun j (nas, _) ->
          if not (Int.equal j (i - 1)) then
            l := under (Array.length nas) (pt_sub c).(2 + npms + nidx + j) !l) br in
      let r = Array.of_list (List.sort_uniq Int.compare !l) in
      let () = slots.(i - 1) <- Some r in
      r
  in
  (* Whether what is left when the walk stops reaches the block. *)
  let left_reaches v stack frames =
    let clos_reaches a = closure_reaches a.pc_env 0 a.pc_term in
    let case_reaches ce c =
      let (_, _, _, pnas, br, npms, nidx) = case_parts c in
      closure_reaches ce (Array.length pnas) (pt_sub c).(1)
      || (let rec mid k = k <= 1 + npms + nidx && (closure_reaches ce 0 (pt_sub c).(k) || mid (k + 1)) in
          mid 2)
      || Array.exists (fun x -> x)
           (Array.mapi (fun j (nas, _) ->
                closure_reaches ce (Array.length nas) (pt_sub c).(2 + npms + nidx + j)) br)
    in
    clos_reaches v
    || List.exists clos_reaches stack
    || List.exists (function
        | PFCase (ce, c, s) -> List.exists clos_reaches s || case_reaches ce c
        | PFProj (_, s) | PFUpdate (_, s) -> List.exists clos_reaches s)
      frames
  in
  (* Bind the declarations of a constructor's context, outermost first: an
     argument from [real], a let-in from its value [values.(k)]. [eb] is
     the environment of the branch body and [ev] the one its declared
     values live in; both grow with the same bindings, as [get_branch]
     does (kernel/cClosure.ml). [dread.(k)] says whether declaration [k] is
     read; one that is not is dropped. *)
  let fill_branch eb ev ndecls values dread real =
    let rec fill eb ev k real =
      if Int.equal k ndecls then eb
      else
        let b, real = match values.(k), real with
          | None, a :: real -> binding_of a dread.(k), real
          | Some bdy, _ -> binding_of (clos ev bdy) dread.(k), real
          | None, [] -> assert false
        in
        fill (push eb b) (push ev b) (k + 1) real
    in
    fill eb ev 0 real
  in
  (* The annotated values of a context's let-ins, outermost first, with
     [None] for an assumption. *)
  let annotate_ctx ctx = Array.of_list (List.rev_map (function
      | LocalDef (_, bdy, _) -> Some (pterm_of bdy)
      | LocalAssum _ -> None) ctx) in
  (* The let-in values of the parameter context of [ind] and of the
     context of its constructor [i], as declared (under the block's
     inductive types, then the parameters), with the universe instance
     [u] applied. Computed once per constructor and instance, so that an
     iota builds nothing: the annotation, and with it the free variables
     of each value, is shared by every step. *)
  let decls_memo = ref Indmap_env.empty in
  let ctor_decls (ind, i) mib mip u =
    let per_ind = match Indmap_env.find_opt ind !decls_memo with
      | Some s -> s
      | None -> let s = ref [] in let () = decls_memo := Indmap_env.add ind s !decls_memo in s
    in
    match List.find_opt (fun ((i', u'), _) -> Int.equal i i' && UVars.Instance.equal u u') !per_ind with
    | Some (_, d) -> d
    | None ->
      let inst c = if UVars.Instance.is_empty u then c else Vars.subst_instance_context u c in
      let ctx, _ = List.chop mip.mind_consnrealdecls.(i - 1) (fst mip.mind_nf_lc.(i - 1)) in
      let d = (annotate_ctx (inst mib.mind_params_ctxt), annotate_ctx (inst ctx)) in
      let () = per_ind := ((i, u), d) :: !per_ind in
      d
  in
  (* The environment of the selected branch [bbody] (with [ndecls] binders)
     of the match [ci, u] in [ce], its constructor [i] applied to its
     parameters [params] and its arguments [real]. Iota drops every
     parameter of the application: the reduction instantiates the
     constructor's context with the parameters of the MATCH, which
     [case_drop_rels] checks, so both are held to the rule. *)
  let branch_env ce ci u params i bnas bbody real =
    let rels = pt_fv bbody in
    let ndecls = Array.length bnas in
    let () = List.iter drop_clos params in
    if Int.equal ndecls ci.ci_cstr_nargs.(i - 1) then
      fst (List.fold_left (fun (e, k) a -> (bind e a (has_rel rels (ndecls - k)), k + 1))
             (ce, 0) real)
    else
      (* Let-ins in the constructor. Their values live in the
         constructor's own context: the block's inductive types, then one
         binding per parameter DECLARATION, then the declarations before
         them; the branch body lives in [ce] with the declarations alone,
         as in [get_branch] (kernel/cClosure.ml). Both are filled with the
         same bindings. The declared values are used as they are declared,
         with the parameters bound rather than substituted into them; the
         inductive types are bound as abstractions, which no value of the
         block can read. A declaration is read by the branch or by the
         value of a later let-in; one that is not is dropped. *)
      let (mib, mip) = lookup_mind_specif env ci.ci_ind in
      let pvalues, values = ctor_decls (ci.ci_ind, i) mib mip u in
      let lets = List.filter (fun m -> Option.has_some values.(m)) (List.init ndecls (fun m -> m)) in
      let dread = Array.init ndecls (fun k ->
          has_rel rels (ndecls - k)
          || List.exists (fun m ->
              m > k && (match values.(m) with
                  | Some bdy -> has_rel (pt_fv bdy) (m - k)
                  | None -> false)) lets) in
      let rec bind_params ev p ps =
        if Int.equal p (Array.length pvalues) then ev
        else match pvalues.(p), ps with
          | None, a :: ps -> bind_params (bind ev a false) (p + 1) ps
          | Some bdy, ps -> bind_params (bind ev (clos ev bdy) false) (p + 1) ps
          | None, [] -> ev
      in
      let ev = bind_params (iterate assum (Array.length mib.mind_packets) ce) 0 params in
      fill_branch ce ev ndecls values dread real
  in
  let rec run needed v stack frames =
    let e = v.pc_env in
    let sub = pt_sub v.pc_term in
    match kind v.pc_term.pt with
    | Lambda _ ->
      begin match stack, frames with
      | a :: rest, _ ->
        let () = drop e sub.(0) in
        run needed (clos (bind e a (pt_binder_read v.pc_term)) sub.(1)) rest frames
      | [], PFUpdate (w, s) :: frames ->
        let () = w.pw <- PWDone (v, []) in
        run needed v s frames
      | [], [] ->
        let () = drop e sub.(0) in
        if Int.equal needed 1 then false
        else run (needed - 1) (clos (assum e) sub.(1)) [] []
      | [], (PFCase _ | PFProj _) :: _ -> left_reaches v stack frames
      end
    | LetIn _ ->
      let () = drop e sub.(1) in
      run needed
        (clos (bind e (clos e sub.(0)) (pt_binder_read v.pc_term)) sub.(2)) stack frames
    | Cast _ ->
      let () = drop e sub.(1) in
      run needed (clos e sub.(0)) stack frames
    | App _ when Array.is_empty sub -> left_reaches v stack frames (* a meta at the head *)
    | App _ -> run needed (clos e sub.(0)) (push_args e sub stack) frames
    | Case _ -> run needed (clos e sub.(0)) [] (PFCase (e, v.pc_term, stack) :: frames)
    | Proj (pr, _, _) -> run needed (clos e sub.(0)) [] (PFProj (pr, stack) :: frames)
    | Construct ((_, i), _) ->
      begin match frames with
      | PFUpdate (w, s) :: frames ->
        let () = w.pw <- PWDone (v, stack) in
        run needed v (stack @ s) frames
      | PFCase (ce, c, s) :: frames ->
        let (ci, u, _, _, br, npms, nidx) = case_parts c in
        let npar = ci.ci_npar in
        if i < 1 || i > Array.length br
           || not (Int.equal (List.length stack) (npar + ci.ci_cstr_nargs.(i - 1)))
           || not (Int.equal (Array.length (fst br.(i - 1))) ci.ci_cstr_ndecls.(i - 1))
        then true (* ill-typed: cannot happen *)
        else
          (* What iota drops. The quick test is on the free variables of all
             of it at once; when it fires, each part is held to the rule of
             [drop], so an inert occurrence passes here too. *)
          let () =
            if rels_reach ce 0 (case_drop_rels c i) then begin
              let (_, _, _, pnas, _, _, _) = case_parts c in
              drop_under ce (Array.length pnas) (pt_sub c).(1);
              for k = 2 to 1 + npms + nidx do drop_under ce 0 (pt_sub c).(k) done;
              Array.iteri (fun j (nas, _) ->
                  if not (Int.equal j (i - 1)) then
                    drop_under ce (Array.length nas) (pt_sub c).(2 + npms + nidx + j)) br
            end in
          let params, real = List.chop npar stack in
          let bbody = (pt_sub c).(2 + npms + nidx + i - 1) in
          run needed
            (clos (branch_env ce ci u params i (fst br.(i - 1)) bbody real) bbody) s frames
      | PFProj (pr, s) :: frames ->
        let field = Projection.npars pr + Projection.arg pr in
        begin match List.nth_opt stack field with
        | None -> true (* ill-typed: cannot happen *)
        | Some a ->
          let () = List.iteri (fun j x -> if not (Int.equal j field) then drop_clos x) stack in
          run needed a s frames
        end
      | [] -> left_reaches v stack frames
      end
    | Rel j when j <= e.pe_len ->
      let b = binding e j in
      begin match b.pb_value with
      | Some w -> force needed b.pb_whnf (fun () -> w) stack frames
      | None -> left_reaches v stack frames
      end
    | Rel j ->
      let o = j - e.pe_len + e.pe_shift in
      if e.pe_shift < 0 || o <= nbfix then left_reaches v stack frames
      else begin match lookup_rel o env with
        | LocalDef (_, w, _) ->
          force needed (rel_cell o)
            (fun () -> clos { empty with pe_shift = o } (pterm_of w)) stack frames
        | LocalAssum _ -> left_reaches v stack frames
      end
    | Var id ->
      begin match Context.Named.Declaration.get_value (lookup_named id env) with
      | Some w -> force needed (var_cell id) (fun () -> clos closed (pterm_of w)) stack frames
      | None -> left_reaches v stack frames
      end
    | Const (cst, _ as cu) ->
      if evaluable_constant cst env then
        force needed (const_cell cu)
          (fun () -> clos closed (pterm_of (constant_value_in env cu))) stack frames
      else left_reaches v stack frames
    | Meta _ | Evar _ | Sort _ | Prod _ | Ind _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> left_reaches v stack frames
  (* A read at the head of a shared value: its head normal form if known;
     else the value, reduced under an update frame, which replaces an
     update frame on top when no argument is in between (the value read
     there has this head normal form too). *)
  and force needed w value stack frames =
    let w = resolve w in
    match w.pw, stack, frames with
    | PWDone (v', s'), _, _ -> run needed v' (s' @ stack) frames
    | PWUnknown, [], PFUpdate (w', s) :: frames when w' != w ->
      let () = w'.pw <- PWSame w in
      run needed (value ()) [] (PFUpdate (w, s) :: frames)
    | PWUnknown, _, _ -> run needed (value ()) [] (PFUpdate (w, stack) :: frames)
    | PWSame _, _, _ -> assert false (* [resolve] *)
  in
  let body = erase_chain_types (recindx + 1) body in
  (* A body that mentions no function of the block has nothing to check;
     the test comes before the annotation, which the walk then builds only
     along the path it takes. *)
  if noccur_with_meta 1 nbfix body then false, max_int
  else
    let escaped =
      try run (recindx + 1) (clos empty (pterm_of body)) [] []
      with PrefixEscape -> true in
    escaped, !bound

type fix_check_result =
  | NeedReduce of env * fix_guard_error
  | NoNeedReduce

(* Definition and manipulation of the stack *)
type stack_element =
  (* arguments in the evaluation stack *)
  (* [constr] is typed in [guard_env] and [int] is the number of
     binders added in the current env on top of [guard_env.env] *)
  | SClosure of fix_check_result * guard_env * int * constr
  (* arguments applied to a "match": only their spec traverse the match *)
  | SArg of subterm_spec Lazy.t

let (|||) x y = match x with
  | NeedReduce _ -> x
  | NoNeedReduce -> y

let rec needreduce_of_stack = function
  | [] -> NoNeedReduce
  | SArg _ :: l -> needreduce_of_stack l
  | SClosure (needreduce,_,_,_) :: l -> needreduce ||| needreduce_of_stack l

let redex_level rs = List.length rs

let push_stack_closure renv needreduce c stack =
  (SClosure (needreduce, renv, 0, c)) :: stack

let push_stack_closures renv l stack =
  List.fold_right (push_stack_closure renv NoNeedReduce) l stack

let push_stack_args l stack =
  List.fold_right (fun spec stack -> SArg spec :: stack) l stack

let lift_stack k =
   List.map (function
       | SClosure (needreduce,s,n,c) -> SClosure (needreduce,s,n+k,c)
       | x -> x)

let lift1_stack = lift_stack 1

(******************************)
(* {6 Computing the recursive subterms of a term (propagation of size
   information through Cases).} *)

let lookup_subterms env ind =
  let (_,mip) = lookup_mind_specif env ind in
  mip.mind_recargs

let match_inductive ind ra =
  match ra with
    | Mrec (RecArgInd i) -> Ind.CanOrd.equal ind i
    | Norec | Mrec (RecArgPrim _) -> false

(* In {match c as z in ci y_s return P with | C_i x_s => t end}
   [branches_specif renv c_spec ci] returns an array of x_s specs knowing
   c_spec. *)
let branches_specif renv c_spec ci =
  let car =
    (* We fetch the regular tree associated to the inductive of the match.
       This is just to get the number of constructors (and constructor
       arities) that fit the match branches without forcing c_spec.
       Note that c_spec might be more precise than [v] below, because of
       nested inductive types. *)
    let (_,mip) = lookup_mind_specif renv.env ci.ci_ind in
    let tree = Rtree.Kind.make mip.mind_recargs in
    match Rtree.Kind.kind tree with
    | Rtree.Kind.Node (_, v) -> Array.map Array.length v
    | Rtree.Kind.Var _ -> assert false
  in
  let subterms = lazy begin match Lazy.force c_spec with
  | Subterm (_, _, t) -> dest_subterms t
  | Dead_code | Internally_bound_subterm _ | Not_subterm -> assert false
  end in
  Array.mapi
      (fun i nca -> (* i+1-th cstructor has arity nca *)
         let lvra = lazy
           (match Lazy.force c_spec with
                Subterm (internal,_,t) when match_inductive ci.ci_ind (dest_recarg t) ->
                  let vra = Array.of_list (Lazy.force subterms).(i) in
                  assert (Int.equal nca (Array.length vra));
                  Array.map (spec_of_tree internal) vra
              | Dead_code -> Array.make nca Dead_code
              | Internally_bound_subterm _ as x -> Array.make nca x
              | Subterm _ | Not_subterm -> Array.make nca Not_subterm) in
         List.init nca (fun j -> lazy (Lazy.force lvra).(j)))
      car

let check_inductive_codomain ?evars env p =
  let absctx, ar = whd_decompose_lambda_decls ?evars env p in
  let env = push_rel_context absctx env in
  let arctx, s = whd_decompose_prod_decls ?evars env ar in
  let env = push_rel_context arctx env in
  let i,_l' = decompose_app (whd_all ?evars env s) in
  isInd i

(* The following functions are almost duplicated from indtypes.ml, except
that they carry here a poorer environment (containing less information). *)
let ienv_push_var (env, lra) (x,a,ra) =
  (push_rel (LocalAssum (x,a)) env, (Norec,ra)::lra)

let ienv_push_inductive ?evars (env, ra_env) ((mind,u),lpar) =
  let mib = Environ.lookup_mind mind env in
  let ntypes = Declareops.mind_ntypes mib in
  let push_ind mip env =
    let r = relevance_of_ind_body mip u in
    let anon = Context.make_annot Anonymous r in
    let decl = LocalAssum (anon, hnf_prod_applist ?evars env (type_of_inductive ((mib,mip),u)) lpar) in
    push_rel decl env
  in
  let env = Array.fold_right push_ind mib.mind_packets env in
  let rc = Array.mapi (fun j t -> Mrec (RecArgInd (mind,j)),t) (Rtree.mk_rec_calls ntypes) in
  let lra_ind = Array.rev_to_list rc in
  let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
  (env, lra_ind @ ra_env)

let rec ienv_decompose_prod ?evars (env,_ as ienv) n c =
 if Int.equal n 0 then (ienv,c) else
   let c' = whd_all ?evars env c in
   match kind c' with
   Prod(na,a,b) ->
     let ienv' = ienv_push_var ienv (na,a,mk_norec) in
     ienv_decompose_prod ?evars ienv' (n-1) b
     | _ -> assert false

(* This removes global parameters of the inductive types in lc (for
   nested inductive types only ) *)
let dummy_univ = Level.(make (UGlobal.make (DirPath.make [Id.of_string "implicit"]) "" 0))
let dummy_implicit_sort = mkType (Universe.make dummy_univ)
let lambda_implicit n a =
  let anon = Context.make_annot Anonymous Sorts.Relevant in
  let lambda_implicit a = mkLambda (anon, dummy_implicit_sort, a) in
  iterate lambda_implicit n a

let abstract_mind_lc ntyps npars mind lc =
  let lc = Array.map (fun (ctx, c) -> Term.it_mkProd_or_LetIn c ctx) lc in
  let rec replace_ind k c =
    let hd, args = decompose_app_list c in
    match kind hd with
    | Ind ((mind',i),_) when MutInd.CanOrd.equal mind mind' ->
      let rec drop_params n = function
        | _ :: args when n > 0 -> drop_params (n-1) args
        | args -> lambda_implicit n (Term.applist (mkRel (ntyps+n+k-i), List.Smart.map (replace_ind (n+k)) args))
      in
      drop_params npars args
    | _ -> map_with_binders succ replace_ind k c
  in
  Array.map (replace_ind 0) lc

let is_primitive_positive_container env c =
  match (Environ.retroknowledge env).Retroknowledge.retro_array with
  | Some c' when QConstant.equal env c c' -> true
  | _ -> false

module Cache :
sig
  type t
  val create : unit -> t
  val get_inductive_subterms : MutInd.t -> mutual_inductive_body -> t -> wf_paths list array array
end =
struct
  type ans = wf_paths list array array
  type t = ans Mindmap_env.t ref
  let create () = ref Mindmap_env.empty
  let get_inductive_subterms mind mib cache = match Mindmap_env.find_opt mind !cache with
  | None ->
    let ans = Array.map (fun mip -> dest_subterms mip.mind_recargs) mib.mind_packets in
    let () = cache := Mindmap_env.add mind ans !cache in
    ans
  | Some ans -> ans
end

(* [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for ind, knowing args. The argument tree is used to know when candidate
nested types should be traversed, pruning the tree otherwise. This code is very
close to check_positive in indtypes.ml, but does no positivity check and does not
compute the number of recursive arguments. *)
let get_recargs_approx cache ?evars env tree ind args =
  let rec build_recargs (env, ra_env as ienv) tree c =
    let x,largs = decompose_app_list (whd_all ?evars env c) in
    match kind x with
    | Prod (na,b,d) ->
       assert (List.is_empty largs);
       build_recargs (ienv_push_var ienv (na, b, mk_norec)) tree d
    | Rel k ->
       (* Free variables are allowed and assigned Norec *)
       (try snd (List.nth ra_env (k-1))
        with Failure _ | Invalid_argument _ -> mk_norec)
    | Ind ind_kn ->
       (* When the inferred tree allows it, we consider that we have a potential
       nested inductive type *)
       begin match dest_recarg tree with
             | Mrec (RecArgInd ind') when QInd.equal env (fst ind_kn) ind' ->
               build_recargs_nested ienv tree (ind_kn, largs)
             | Norec | Mrec _ -> mk_norec
       end
    | Const (c,_) when is_primitive_positive_container env c ->
       begin match dest_recarg tree with
             | Mrec (RecArgPrim c') when QConstant.equal env c c' ->
               build_recargs_nested_primitive ienv tree (c, largs)
             | Norec | Mrec _ -> mk_norec
       end
    | _err ->
       mk_norec

  and build_recargs_nested (env,_ra_env as ienv) tree (((mind,i),u), largs) =
    (* If the inferred tree already disallows recursion, no need to go further *)
    if is_norec_path tree then tree
    else
    let mib = Environ.lookup_mind mind env in
    let nonrecpar = mib.mind_nparams - mib.mind_nparams_rec in
    let (lpar,_) = List.chop mib.mind_nparams_rec largs in
    let auxntyp = Declareops.mind_ntypes mib in
    (* Extends the environment with a variable corresponding to
             the inductive def *)
    let (env',_ as ienv') = ienv_push_inductive ?evars ienv ((mind,u),lpar) in
    (* Parameters expressed in env' *)
    let lpar' = List.map (lift auxntyp) lpar in
    (* In case of mutual inductive types, we use the recargs tree which was
    computed statically. This is fine because nested inductive types with
    mutually recursive containers are not supported. *)
    let trees =
      if Int.equal auxntyp 1 then [|dest_subterms tree|]
      else Cache.get_inductive_subterms mind mib cache
    in
    let mk_irecargs j mip =
      (* The nested inductive type with parameters removed *)
      let auxlcvect = abstract_mind_lc auxntyp mib.mind_nparams_rec mind mip.mind_nf_lc in
      let paths = Array.mapi
        (fun k c ->
         let c' = hnf_prod_applist ?evars env' c lpar' in
         (* skip non-recursive parameters *)
         let (ienv',c') = ienv_decompose_prod ?evars ienv' nonrecpar c' in
         build_recargs_constructors ienv' trees.(j).(k) c')
        auxlcvect
      in
      mk_paths (Mrec (RecArgInd (mind,j))) paths
    in
    let irecargs = Array.mapi mk_irecargs mib.mind_packets in
    (Rtree.mk_rec irecargs).(i)

  and build_recargs_nested_primitive (env, ra_env) tree (c, largs) =
    if is_norec_path tree then tree
    else
    let ntypes = 1 in (* Primitive types are modelled by non-mutual inductive types *)
    let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
    let ienv = (env, ra_env) in
    let paths = List.map2 (build_recargs ienv) (dest_subterms tree).(0) largs in
    let recargs = [| mk_paths (Mrec (RecArgPrim c)) [| paths |] |] in
    (Rtree.mk_rec recargs).(0)

  and build_recargs_constructors ienv trees c =
    let rec recargs_constr_rec (env,_ra_env as ienv) trees lrec c =
      let x,largs = decompose_app_list (whd_all ?evars env c) in
        match kind x with

          | Prod (na,b,d) ->
             let () = assert (List.is_empty largs) in
             let recarg = build_recargs ienv (List.hd trees) b in
             let ienv' = ienv_push_var ienv (na,b,mk_norec) in
             recargs_constr_rec ienv' (List.tl trees) (recarg::lrec) d
          | _hd ->
             List.rev lrec
    in
    recargs_constr_rec ienv trees [] c
  in
  (* starting with ra_env = [] seems safe because any unbounded Rel will be
  assigned Norec *)
  build_recargs_nested (env,[]) tree (ind, args)

(* Check that the parameter arguments of an inductive type do not mention some
   variable range. This is used as a fast-path when casting recursive trees
   against a commutative cut: indices are irrelevant for the tree
   computation in {!get_recargs_approx}. *)
let has_constant_parameters env nvars k ((mind, _), _) args =
  let mib = Environ.lookup_mind mind env in
  let auxnpar = mib.mind_nparams_rec in
  let (lpar, _) = List.chop auxnpar args in
  List.for_all (fun c -> noccur_with_meta (1 + k) (nvars + k) c) lpar

(* [restrict_spec env spec p] restricts the size information in spec to what is
   allowed to flow out of a match with predicate p in environment env. *)
let restrict_spec cache ?evars env spec p =
  match spec with
  | Not_subterm | Internally_bound_subterm _ -> spec
  | _ ->
  let absctx, ar = whd_decompose_lambda_decls ?evars env p in
  let absctxlen = Context.Rel.length absctx in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 absctxlen ar then spec
  else
  let env = push_rel_context absctx env in
  let arctx, s = whd_decompose_prod ?evars env ar in
  let env = push_rel_context arctx env in
  let i,args = decompose_app_list (whd_all ?evars env s) in
  match kind i with
  | Ind i ->
    if has_constant_parameters env absctxlen (List.length arctx) i args then spec
    else begin match spec with
    | Dead_code -> spec
    | Subterm (l, st, tree) ->
      let recargs = get_recargs_approx cache ?evars env tree i args in
      let tree = inter_wf_paths tree recargs in
      Subterm (l, st, tree)
    | _ -> assert false
    end
  | _ -> Not_subterm

(* [filter_stack_domain env spec p] restricts the size information in stack to
   what is allowed to enter under a match with predicate p in environment env. *)
let filter_stack_domain cache stack_element_specif set_iota_specif ?evars env p stack =
  let absctx, ar = Term.decompose_lambda_decls p in
  let absctxlen = Context.Rel.length absctx in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 absctxlen ar then stack
  else
    let env = push_rel_context absctx env in
    let rec filter_stack env k ar stack = match stack with
    | [] -> []
    | elt :: stack' ->
      let t = whd_all ?evars env ar in
      match kind t with
      | Prod (n, a, c0) ->
        let d = LocalAssum (n, a) in
        let ctx, a = whd_decompose_prod ?evars env a in
        let env = push_rel_context ctx env in
        let ty, args = decompose_app_list (whd_all ?evars env a) in
        let elt = match kind ty with
        | Ind ind ->
          let spec = stack_element_specif cache ?evars elt in
          if has_constant_parameters env absctxlen (k + List.length ctx) ind args then SArg spec
          else
            let sarg = lazy begin match Lazy.force spec with
            | Not_subterm | Dead_code | Internally_bound_subterm _ as spec -> spec
            | Subterm (l, s, tree) ->
              let recargs = get_recargs_approx cache ?evars env tree ind args in
              let tree = inter_wf_paths tree recargs in
              Subterm (l, s, tree)
            end in
            SArg sarg
        | _ -> SArg (set_iota_specif (lazy Not_subterm))
        in
        elt :: filter_stack (push_rel d env) (k + 1) c0 stack'
      | _ ->
        List.map (fun _ -> SArg (set_iota_specif (lazy Not_subterm))) stack
  in
  filter_stack env 0 ar stack

(* [subterm_specif renv t] computes the recursive structure of [t] and
   compare its size with the size of the initial recursive argument of
   the fixpoint we are checking. [renv] collects such information
   about variables.
*)

let rec subterm_specif cache ?evars renv stack t =
  (* maybe reduction is not always necessary! *)
  let f,l = decompose_app_list (whd_all ?evars renv.env t) in
    match kind f with
    | Rel k -> subterm_var k renv
    | Case (ci, u, pms, p, iv, c, lbr) -> (* iv ignored: it's just a cache *)
      let (ci, (p,_), _iv, c, lbr) = expand_case renv.env (ci, u, pms, p, iv, c, lbr) in
      let stack' = push_stack_closures renv l stack in
      let stack' = filter_stack_domain cache stack_element_specif Fun.id ?evars renv.env p stack' in
      let cases_spec =
        branches_specif renv (lazy_subterm_specif cache ?evars renv [] c) ci
      in
      let stl =
        Array.mapi (fun i br' ->
                    let stack_br = push_stack_args (cases_spec.(i)) stack' in
                    subterm_specif cache ?evars renv stack_br br')
                  lbr in
      let spec = subterm_spec_glb stl in
      restrict_spec cache ?evars renv.env spec p

    | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
      (* when proving that the fixpoint f(x)=e is less than n, it is enough
         to prove that e is less than n assuming f is less than n
         furthermore when f is applied to a term which is strictly less than
         n, one may assume that x itself is strictly less than n
      *)
    if not (check_inductive_codomain ?evars renv.env typarray.(i)) then Not_subterm
    else
      let (ctxt,clfix) = whd_decompose_prod ?evars renv.env typarray.(i) in
      let oind =
        let env' = push_rel_context ctxt renv.env in
          try Some(fst (find_inductive ?evars env' clfix))
          with Not_found -> None in
        (match oind with
      None -> Not_subterm (* happens if fix is polymorphic *)
        | Some (ind, _) ->
        let nbfix = Array.length typarray in
        let recargs = lookup_subterms renv.env ind in
                   (* pushing the fixpoints *)
        let renv' = push_fix_renv renv recdef in
        let renv' =
                     (* Why Strict here ? To be general, it could also be
                        Large... *)
          assign_var_spec renv'
          (nbfix-i, lazy (Subterm(Int.Set.empty,Strict,recargs))) in
        let decrArg = recindxs.(i) in
        let theBody = bodies.(i)   in
        (* Reduce in [renv'.env], where the body's own declarations are, for
           the reason given at the call of [find_uniform_parameters]. A body
           with too few abstractions gives no subterm information rather than
           an anomaly: the guard condition then refuses what depends on it. *)
        match split_struct_arg ?evars renv'.env decrArg theBody with
        | exception Invalid_argument _ -> Not_subterm
        | sign, strippedBody ->
                   (* pushing the fix parameters *)
        let stack' = push_stack_closures renv l stack in
        let renv'' = push_ctxt_renv renv' sign in
        let renv'' =
          if List.length stack' < decrArg + 1 then renv''
          else
            let decrArg = List.nth stack' decrArg in
            let arg_spec = stack_element_specif cache ?evars decrArg in
              assign_var_spec renv'' (1, arg_spec) in
          subterm_specif cache ?evars renv'' [] strippedBody)

    | Lambda (x,a,b) ->
      let () = assert (List.is_empty l) in
      let spec,stack' = extract_stack cache ?evars stack in
        subterm_specif cache ?evars (push_var renv (x,a,spec)) stack' b

      (* Metas and evars are considered OK *)
    | (Meta _|Evar _) -> Dead_code

    | Proj (p, _, c) ->
      let subt = subterm_specif cache ?evars renv stack c in
      (match subt with
       | Subterm (internal, _s, wf) ->
         (* We take the subterm specs of the constructor of the record *)
         let wf_args = (dest_subterms wf).(0) in
         (* We extract the tree of the projected argument *)
         let n = Projection.arg p in
         spec_of_tree internal (List.nth wf_args n)
       | Dead_code -> Dead_code
       | Not_subterm -> Not_subterm
       | Internally_bound_subterm n -> Internally_bound_subterm n)

    | Const c ->
      begin try
        let _ = Environ.constant_value_in renv.env c in Not_subterm
      with
        | NotEvaluableConst (IsPrimitive (_u,op)) when List.length l >= CPrimitives.arity op ->
          primitive_specif cache ?evars renv op l
        | NotEvaluableConst _ -> Not_subterm
      end

    | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Ind _
      | Construct _ | CoFix _ | Int _ | Float _ | String _
      | Array _ -> Not_subterm


      (* Other terms are not subterms *)

and lazy_subterm_specif cache ?evars renv stack t =
  lazy (subterm_specif cache ?evars renv stack t)

and stack_element_specif cache ?evars = function
  | SClosure (_, h_renv, _, h) -> lazy_subterm_specif cache ?evars h_renv [] h
  | SArg x -> x

and extract_stack cache ?evars = function
   | [] -> Lazy.from_val Not_subterm, []
   | elt :: l -> stack_element_specif cache ?evars elt, l

and primitive_specif cache ?evars renv op args =
  let open CPrimitives in
  match op with
  | Arrayget | Arraydefault ->
    (* t.[i] and default t can be seen as strict subterms of t, with a
       potentially nested rectree. *)
    let arg = List.nth args 1 in (* the result is a strict subterm of the second argument *)
    let subt = subterm_specif cache ?evars renv [] arg in
    begin match subt with
    | Subterm (internal, _s, wf) ->
      let wf_args = (dest_subterms wf).(0) in
      spec_of_tree internal (List.nth wf_args 0) (* first and only parameter of `array` *)
    | Dead_code -> Dead_code
    | Not_subterm -> Not_subterm
    | Internally_bound_subterm n -> Internally_bound_subterm n
    end
  | _ -> Not_subterm

let set_iota_specif nr spec =
  lazy (match Lazy.force spec with
        | Not_subterm -> if nr >= 1 then Internally_bound_subterm (Int.Set.singleton nr) else Not_subterm
        | spec -> spec)

(************************************************************************)

exception FixGuardError of env * fix_guard_error

let illegal_rec_call renv fx = function
  | SClosure (_,arg_renv,_,arg) ->
    let le_lt_vars =
    lazy (let (_,le_vars,lt_vars) =
      List.fold_left
        (fun (i,le,lt) sbt ->
          match Lazy.force sbt with
              (Subterm(_,Strict,_) | Dead_code) -> (i+1, le, i::lt)
            | (Subterm(_,Large,_)) -> (i+1, i::le, lt)
            | _ -> (i+1, le ,lt))
        (1,[],[]) renv.genv in
          (le_vars,lt_vars)) in
    RecursionOnIllegalTerm(fx,(arg_renv.env, arg),le_lt_vars)
  | SArg _ ->
    (* Typically the case of a recursive call encapsulated under a
       rewriting before been applied to the parameter of a constructor *)
    NotEnoughArgumentsForFixCall fx

let set_need_reduce_one env nr err rs =
  let mr = List.length rs in
  let rs1, rs2 = List.chop (mr-nr) rs in
  let _, rs2 = List.sep_first rs2 in
  rs1 @ NeedReduce (env, err) :: rs2

let set_need_reduce env l err rs =
  Int.Set.fold (fun n -> set_need_reduce_one env n err) l rs

let set_need_reduce_top env err rs =
  set_need_reduce_one env (List.length rs) err rs

type check_subterm_result =
  | InvalidSubterm
  | NeedReduceSubterm of Int.Set.t (* empty = NoNeedReduce *)

(* Check term c can be applied to one of the mutual fixpoints. *)
let check_is_subterm x tree =
  match Lazy.force x with
  | Subterm (need_reduce,Strict,tree') ->
    if incl_wf_paths tree tree' then NeedReduceSubterm need_reduce
    else InvalidSubterm
  | Dead_code -> NeedReduceSubterm Int.Set.empty
  | Not_subterm | Subterm (_,Large,_) -> InvalidSubterm
  | Internally_bound_subterm l -> NeedReduceSubterm l

let find_uniform_parameters recindx nargs stripped =
  let bodies = stripped in
  let nbodies = Array.length bodies in
  (* Ensure that the structural argument is not uniform,
     so that it stays in [non_absorbed_stack] *)
  let min_indx = Array.fold_left min nargs recindx in
  let rec aux k nuniformparams c =
    let f, l = decompose_app_list c in
    match kind f with
    | Rel n ->
      let fold accu c = match kind c with
        | Rel m when m > k && m <= k + nbodies ->
          (* An argument that is a bare occurrence of one of the mutual
             fixpoints: it is applied to nothing, so no prefix of arguments can
             be extruded from it, and [drop_uniform_parameters] must not be
             asked to drop one. [fold_constr_with_binders] would miss it,
             because it visits the immediate children of the argument and a
             [Rel] has none. *)
          0
        | _ -> fold_constr_with_binders succ aux k accu c
      in
      let nuniformparams = List.fold_left fold nuniformparams l in
      (* A recursive reference to any one of the mutual fixpoints *)
      if n > k && n <= k + nbodies then
        List.fold_left_until (fun j arg ->
          if j >= nuniformparams then Stop nuniformparams else
          match kind arg with
          | Rel m when Int.equal m (k - j) ->
            (* a reference to the j-th parameter *)
            Cont (j+1)
          | _ ->
            (* not a parameter: this puts a bound on the size of an extrudable prefix of uniform arguments *)
            Stop j
          ) 0 l
      else
        nuniformparams
    | _ -> fold_constr_with_binders succ aux k nuniformparams c
  in
  (* [stripped] holds the bodies with their [recindx+1] leading abstractions
     removed and reduced, which is the form the rewriting below also sees, so
     the two passes measure one term. *)
  Array.fold_left2_i (fun _k nuniformparams recindx c ->
    aux (recindx + 1) nuniformparams c)
    min_indx recindx stripped

(** Given a fixpoint [fix f x y z n {struct n} := phi(f x y u t, ..., f x y u' t')]
    with [z] not uniform we build in context [x:A, y:B(x), z:C(x,y)] a term
    [fix f z n := phi(f u t, ..., f u' t')], say [psi], of some type
    [forall (z:C(x,y)) (n:I(x,y,z)), T(x,y,z,n)], so that
    [fun x y z => psi z] is of same type as the original term *)

(* Rewrites the SAME stripped bodies that [find_uniform_parameters] measured,
   at the same de Bruijn depth: each one sits under its own [recindx+1]
   abstractions. Starting at 0 instead would make the test below select the
   innermost stripped binders rather than the block's own variables, so
   arguments would be deleted from an unrelated application and a recursive
   call placed in one of them would never reach the guard condition. That
   admits a closed proof of False; the shape is
   test-suite/failure/guard_prefix_depth.v. *)
let drop_uniform_parameters nuniformparams recindx stripped =
  let nbodies = Array.length stripped in
  let rec aux k c =
    let f, l = decompose_app_list c in
    match kind f with
    | Rel n ->
      let l = List.map (fun c -> aux k c) l in
      (* A recursive reference to any one of the mutual fixpoints *)
      if n > k && n <= k + nbodies then
        let new_args = List.skipn_at_best nuniformparams l in
        Term.applist (f, new_args)
      else Term.applist (f, l)
    | _ -> map_with_binders succ aux k c
  in
  Array.map2 (fun recindx c -> aux (recindx + 1) c) recindx stripped

let filter_fix_stack_domain cache ?evars nr decrarg stack nuniformparams =
  let rec aux i nuniformparams stack =
    match stack with
    | [] -> []
    | a :: stack ->
      let uniform, nuniformparams = if nuniformparams = 0 then false, 0 else true, nuniformparams -1 in
      let a =
        if uniform then a
        else if Int.equal i decrarg then SArg (stack_element_specif cache ?evars a)
        (* We forget the needreduce status of the structural argument here,
           since it's checked in [non_absorbed_stack]. *)
        else
          (* deactivate the status of non-uniform parameters since we
             cannot guarantee that they are preserve in the recursive
             calls *)
          SArg (set_iota_specif nr (lazy Not_subterm)) in
      a :: aux (i+1) nuniformparams stack
  in aux 0 nuniformparams stack

let pop_argument cache ?evars needreduce renv elt stack x a b =
  match needreduce, elt with
  | NoNeedReduce, SClosure (NoNeedReduce, _, n, c) ->
    (* Neither function nor args have rec calls on internally bound variables *)
    let spec = stack_element_specif cache ?evars elt in
    (* Thus, args do not a priori require to be rechecked, so we push a let *)
    (* maybe the body of the let will have to be locally expanded though, see Rel case *)
    push_let renv (x,lift n c,a,spec), lift1_stack stack, b
  | _, SClosure (_, _, n, c) ->
    (* Either function or args have rec call on internally bound variables *)
    renv, stack, subst1 (lift n c) b
  | _, SArg spec ->
    (* Going down a case branch *)
    push_var renv (x,a,spec), lift1_stack stack, b

let judgment_of_fixpoint (_, types, bodies) =
  Array.map2 (fun typ body -> { uj_val = body ; uj_type = typ }) types bodies

(* Check if [def] is a guarded fixpoint body with decreasing arg.
   given [recpos], the decreasing arguments of each mutually defined
   fixpoint. *)
let check_one_fix cache ?evars renv recpos trees def =
  let nfi = Array.length recpos in

  (* Checks if [t] only make valid recursive calls
     [stack] is the list of constructor's argument specification and
     arguments that will be applied after reduction.
     example u in t where we have (match .. with |.. => t end) u;
     [rs] is the stack of redexes traversed w/o having been triggered *)
  let rec check_rec_call_stack renv stack rs t =
      match kind t with
        | App (f,args) ->
            begin
              let rs, stack =
                Array.fold_right (fun a (rs,stack) ->
                    let needreduce,rs = check_rec_call renv rs a in
                    let stack = push_stack_closure renv needreduce a stack in
                    (rs,stack)) args (rs,stack)
              in
              check_rec_call_stack renv stack rs f
            end

        | Rel p ->
            let rs =
              (* Test if [p] is a fixpoint (recursive call) *)
              if renv.rel_min <= p && p < renv.rel_min+nfi then
                (* the position of the invoked fixpoint: *)
                let glob = renv.rel_min+nfi-1-p in
                (* the decreasing arg of the rec call: *)
                let np = recpos.(glob) in
                if List.length stack <= np then
                  set_need_reduce_top renv.env (NotEnoughArgumentsForFixCall glob) rs
                else
                  (* Retrieve the expected tree for the argument *)
                  (* Check the decreasing arg is smaller *)
                  let z = List.nth stack np in
                  match check_is_subterm (stack_element_specif cache ?evars z) trees.(glob) with
                  | NeedReduceSubterm l -> set_need_reduce renv.env l (illegal_rec_call renv glob z) rs
                  | InvalidSubterm -> raise (FixGuardError (renv.env, illegal_rec_call renv glob z))
              else rs
            in
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
                match lookup_rel p renv.env with
                | LocalAssum _ -> None
                | LocalDef (_,c,_) -> Some (lift p c, []))

        | Case (ci, u, pms, ret, iv, c_0, br) -> (* iv ignored: it's just a cache *)
            let (ci, (p,_), _iv, c_0, brs) = expand_case renv.env (ci, u, pms, ret, iv, c_0, br) in
            let needreduce_c_0, rs = check_rec_call renv rs c_0 in
            let rs = check_inert_subterm_rec_call renv rs p in
            (* compute the recarg info for the arguments of each branch *)
            let rs' = NoNeedReduce::rs in
            let nr = redex_level rs' in
            let case_spec =
              branches_specif renv (set_iota_specif nr (lazy_subterm_specif cache ?evars renv [] c_0)) ci in
            let stack' = filter_stack_domain cache stack_element_specif (set_iota_specif nr) ?evars renv.env p stack in
            let rs' =
              Array.fold_left_i (fun k rs' br' ->
                  let stack_br = push_stack_args case_spec.(k) stack' in
                  check_rec_call_stack renv stack_br rs' br') rs' brs in
            let needreduce_br, rs = List.sep_first rs' in
            check_rec_call_state renv (needreduce_br ||| needreduce_c_0) stack rs (fun () ->
              (* we try hard to reduce the match away by looking for a
                 constructor in c_0 (we unfold definitions too) *)
              let c_0 = whd_all ?evars renv.env c_0 in
              let hd, args = decompose_app_list c_0 in
              let hd, args = match kind hd with
              | CoFix cofix ->
                  decompose_app_list (whd_all ?evars renv.env (Term.applist (contract_cofix cofix, args)))
              | _ -> hd, args in
              match kind hd with
              | Construct cstr -> Some (apply_branch cstr args ci brs, [])
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | String _ | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)

        (* Enables to traverse Fixpoint definitions in a more intelligent
           way, ie, the rule :
           if - g = fix g (y1:T1)...(yp:Tp) {struct yp} := e &
              - f is guarded with respect to the set of pattern variables S
                in a1 ... am        &
              - f is guarded with respect to the set of pattern variables S
                in T1 ... Tp        &
              - ap is a sub-term of the formal argument of f &
              - f is guarded with respect to the set of pattern variables
                S+{yp} in e
           then f is guarded with respect to S in (g a1 ... am).
           Eduardo 7/9/98 *)
        | Fix ((recindxs,i),(_,typarray,bodies as recdef) as fix) ->
            let decrArg = recindxs.(i) in
            let nbodies = Array.length bodies in
            let rs' = Array.fold_left (check_inert_subterm_rec_call renv) (NoNeedReduce::rs) typarray in
            let renv' = push_fix_renv renv recdef in
            let illformed k =
              error_ill_formed_rec_body renv.env (Type_errors.FixGuardError (NotEnoughAbstractionInFixBody recindxs.(k)))
                (pi1 recdef) k (push_rec_types recdef renv.env)
                (judgment_of_fixpoint recdef)
            in
            (* Split every body once, in [renv'.env], the environment that
               holds the block's own declarations and in which the kernel
               checks the bodies. With [renv.env], which is short by
               [nbodies] declarations and is what upstream passes, every
               lookup that [split_struct_arg]'s reduction makes is shifted,
               and a body whose head resolves to a different local definition
               is analysed in place of the real one. That admits closed proofs
               of False: test-suite/failure/guard_envshift_x03.v.

               The analysis and the rewriting then work on the SAME stripped
               bodies, and the abstractions are put back afterwards. Upstream
               analyses the stripped body and rewrites the raw one, so an
               occurrence living in the binder prefix is invisible to the
               analysis and visible to the rewriting: the prefix it computed
               is then not justified for that occurrence, and [List.skipn]
               raises inside the kernel. Measuring one term removes the
               disagreement rather than reporting it. *)
            (* The analysis measures each body after [split_struct_arg] has
               reduced its binder prefix away, but the kernel stores the body
               as WRITTEN, so an occurrence of a recursive function that the
               reduction ERASES is checked by nothing and is still evaluated.
               A fully applied call hidden there makes the kernel accept a
               definition whose evaluation does not terminate; upstream Rocq
               accepts those too (9.3.0 and master), and stock 9.2.0, which
               lacks rocq-prover/rocq#22384, does not.

               Submit every erased position to the ordinary analysis, in the
               environment where it occurs, so that a body is refused exactly
               when the erased material would have been refused had the
               reduction kept it: a legitimate call in a dead [let] stays
               legitimate, a call on a bigger argument is a guard error
               wherever it sits. The walk runs on the chain with its types
               erased ([erase_chain_types]) and its positions are the value
               of a [let] whose binder the body does not use (a binder read
               only in an erased type is not used), the argument of a beta
               redex whose binder the body does not use, a lambda's domain, a
               type the erasure did not take out, and, for any other head,
               the whole term: the reduction can erase inside it in ways this
               walk does not model. Unlike [raw_prefix_escapes], it takes no
               head-reduction step (delta, iota): when the abstractions of a
               nested fixpoint appear only after one, its whole head term is
               submitted here, in the enclosing context. A call of an
               enclosing function there passes when it is guarded in that
               context (outer_inner_id in success/guard_prefix_head_step.v),
               and is refused when its argument is guarded only by the
               nested fixpoint's own recursion, which stock 9.2.0 accepts
               and release-8 a3a27a829aa2 refuses too. A [let] whose binder
               IS used is substituted, as the reduction does, so that its
               value is checked wherever the binder sits: a chain [let x :=
               outer (S n) in let y := x in ...] does not hide the call
               behind the variable [x].

               What this reaches that nothing else does is a call to a
               function of an ENCLOSING block: the functions of this block
               are covered by [check_fix] on the block itself, which applies
               the same rule to its own prefix. *)
            (* A dropped term whose only mention of THIS (enclosing) block
               is the head of its application, a function applied to at most
               its structural index of arguments, possibly under
               abstractions, is discarded unapplied and makes no call: it
               needs no check. Anything else is checked as an inert subterm,
               as before. [m] is the [rel_min] of the block at that depth. *)
            let rec dropped_inert m c =
              match kind c with
              | Lambda (_, ty, b) -> noccur_with_meta m nfi ty && dropped_inert (m + 1) b
              | _ ->
                let hd, args = decompose_app c in
                match kind hd with
                | Rel p when m <= p && p < m + nfi ->
                  Array.length args <= recpos.(m + nfi - 1 - p)
                  && Array.for_all (noccur_with_meta m nfi) args
                | _ -> false
            in
            let check_dropped renv rs c =
              if dropped_inert renv.rel_min c then rs
              else check_inert_subterm_rec_call renv rs c
            in
            let rec check_erased_prefix renv needed c rs =
              if Int.equal needed 0 then rs
              else match kind c with
                | Lambda (x, ty, bd) ->
                  let rs = check_inert_subterm_rec_call renv rs ty in
                  check_erased_prefix
                    (push_var_renv renv (redex_level rs) (x,ty)) (needed-1) bd rs
                | LetIn (x, v, ty, bd) ->
                  let rs = check_inert_subterm_rec_call renv rs ty in
                  if noccurn 1 bd then
                    let rs = check_dropped renv rs v in
                    check_erased_prefix renv needed (subst1 v bd) rs
                  else if noccur_with_meta renv.rel_min nfi v then
                    (* The value carries no call of this block, so putting it
                       where its binder is read can change no verdict: keep
                       the binder, which costs one declaration instead of a
                       copy of the value at every read. *)
                    let spec = lazy_subterm_specif cache ?evars renv [] v in
                    check_erased_prefix (push_let renv (x,v,ty,spec)) needed bd rs
                  else check_erased_prefix renv needed (subst1 v bd) rs
                | Cast (c, _, t) ->
                  let rs = check_inert_subterm_rec_call renv rs t in
                  check_erased_prefix renv needed c rs
                | App (f, args) when isLambda f ->
                  check_erased_beta renv needed f (Array.to_list args) rs
                | _ -> check_inert_subterm_rec_call renv rs c
            and check_erased_beta renv needed f args rs =
              match args with
              | [] -> check_erased_prefix renv needed f rs
              | a :: rest ->
                match kind f with
                | Lambda (_, ty, bd) ->
                  let rs = check_inert_subterm_rec_call renv rs ty in
                  let rs = if noccurn 1 bd then check_dropped renv rs a else rs in
                  check_erased_beta renv needed (subst1 a bd) rest rs
                | _ -> check_inert_subterm_rec_call renv rs (Term.applist (f, args))
            in
            let rs' = Array.fold_left2_i (fun _k rs' recindx body ->
                check_erased_prefix renv' (recindx+1)
                  (erase_chain_types (recindx+1) body) rs')
                rs' recindxs bodies in
            let split = Array.map2_i (fun k recindx body ->
                try split_struct_arg ?evars renv'.env recindx body
                with Invalid_argument _ -> illformed k)
                recindxs bodies in
            let stripped = Array.map snd split in
            let nuniformparams = find_uniform_parameters recindxs (List.length stack) stripped in
            (* An occurrence of this block that the prefix reduction drops is
               in the body as WRITTEN and not in [stripped], so the count
               above does not see it, while the prefix walk now lets it
               through instead of refusing the definition. The walk counts
               those occurrences the way [find_uniform_parameters] counts the
               ones it sees, and the smaller of the two counts is kept: no
               prefix is extruded that the term as written does not justify.
               The walk is skipped where it cannot lower the count. *)
            let nuniformparams =
              if Int.equal nuniformparams 0 then 0
              else
                Array.fold_left2 (fun n recindx body ->
                    if n <= 0 || noccur_with_meta 1 nbodies body then n
                    else
                      match raw_prefix_escapes renv'.env recindxs recindx body with
                      | true, _ -> 0
                      | false, b -> min n b)
                  nuniformparams recindxs bodies in
            let stripped = drop_uniform_parameters nuniformparams recindxs stripped in
            let bodies = Array.map2 (fun (sign, _) body ->
                Term.it_mkLambda_or_LetIn body sign) split stripped in
            let fix_stack = filter_fix_stack_domain cache ?evars (redex_level rs) decrArg stack nuniformparams in
            let fix_stack = if List.length stack > decrArg then List.firstn (decrArg+1) fix_stack else fix_stack in
            let stack_this = lift_stack nbodies fix_stack in
            let stack_others = lift_stack nbodies (List.firstn nuniformparams fix_stack) in
            (* Check guard in the expanded fix *)
            let rs' = Array.fold_left2_i (fun j rs' recindx body ->
                let fix_stack = if Int.equal i j then stack_this else stack_others in
                check_nested_fix_body renv' (recindx+1) fix_stack rs' body) rs' recindxs bodies in
            let needreduce_fix, rs = List.sep_first rs' in
            let absorbed_stack, non_absorbed_stack = List.chop nuniformparams stack in
            check_rec_call_state renv needreduce_fix non_absorbed_stack rs (fun () ->
              (* we try hard to reduce the fix away by looking for a
                 constructor in [decrArg] (we unfold definitions too) *)
              if List.length stack <= decrArg then None else
              match List.nth stack decrArg with
              | SArg _ -> (* A match on the way *) None
              | SClosure (_,_,n,recArg) ->
              let c = whd_all ?evars renv.env (lift n recArg) in
              let hd, _ = decompose_app_list c in
              match kind hd with
              | Construct _ -> Some (contract_fix fix, absorbed_stack)
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | String _
              | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)

        | Const (kn,_u as cu) ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
                if evaluable_constant kn renv.env then Some (constant_value_in renv.env cu, [])
                else None)

        | Lambda (x,a,b) ->
            begin
              let needreduce, rs = check_rec_call renv rs a in
              match stack with
              | elt :: stack ->
                let renv, stack, b = pop_argument cache ?evars needreduce renv elt stack x a b in
                check_rec_call_stack renv stack rs b
              | [] ->
                check_rec_call_stack (push_var_renv renv (redex_level rs) (x,a)) [] rs b
            end

        | Prod (x,a,u) ->
            (* Note: we cannot ensure that the stack is empty because
               non-accessible branches of "match" expressions can have
               arbitrary types (see #17073) *)
            let rs = check_inert_subterm_rec_call renv rs a in
            (* Note: can recursive calls on [x] be else than inert "dead code"? *)
            check_rec_call_stack (push_var_renv renv (redex_level rs) (x,a)) [] rs u

        | CoFix (_i,(_,typarray,bodies as recdef)) ->
            let rs = Array.fold_left (check_inert_subterm_rec_call renv) rs typarray in
            let renv' = push_fix_renv renv recdef in
            Array.fold_left (fun rs body ->
                let needreduce', rs = check_rec_call renv' rs body in
                check_rec_call_state renv needreduce' stack rs (fun _ -> None))
              rs bodies

        | Ind _ | Construct _ ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () -> None)

        | Proj (p, _, c) ->
            begin
              let needreduce', rs = check_rec_call renv rs c in
              check_rec_call_state renv needreduce' stack rs (fun () ->
              (* we try hard to reduce the proj away by looking for a
                 constructor in c (we unfold definitions too) *)
              let c = whd_all ?evars renv.env c in
              let hd, args = decompose_app c in
              let hd, args = match kind hd with
              | CoFix cofix ->
                  decompose_app (whd_all ?evars renv.env (mkApp (contract_cofix cofix, args)))
              | _ -> hd, args in
              match kind hd with
              | Construct _ -> Some (args.(Projection.npars p + Projection.arg p), [])
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | String _ | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)
            end

        | Var id ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
              let open! Context.Named.Declaration in
              match lookup_named id renv.env with
              | LocalAssum _ -> None
              | LocalDef (_,c,_) -> Some (c, []))

        | LetIn (x,c,t,b) ->
            let needreduce_c, rs = check_rec_call renv rs c in
            let needreduce_t, rs = check_rec_call renv rs t in
            begin
              match needreduce_of_stack stack ||| needreduce_c ||| needreduce_t with
              | NoNeedReduce ->
                  (* Stack do not require to beta-reduce; let's look if the body of the let needs *)
                  let spec = lazy_subterm_specif cache ?evars renv [] c in
                  let stack = lift1_stack stack in
                  check_rec_call_stack (push_let renv (x,c,t,spec)) stack rs b
              | NeedReduce _ -> check_rec_call_stack renv stack rs (subst1 c b)
            end

        | Cast (c,_,t) ->
            let rs = check_inert_subterm_rec_call renv rs t in
            let rs = check_rec_call_stack renv stack rs c in
            rs

        | Sort _ | Int _ | Float _ | String _ ->
            (* See [Prod]: we cannot ensure that the stack is empty *)
            rs

        | Array (_u,t,def,ty) ->
            (* See [Prod]: we cannot ensure that the stack is empty *)
            let rs = Array.fold_left (check_inert_subterm_rec_call renv) rs t in
            let rs = check_inert_subterm_rec_call renv rs def in
            let rs = check_inert_subterm_rec_call renv rs ty in
            rs

        (* l is not checked because it is considered as the meta's context *)
        | (Evar _ | Meta _) ->
            rs

  and check_nested_fix_body renv decr stack rs body =
    if Int.equal decr 0 then
      check_inert_subterm_rec_call renv rs body
    else
      match kind (whd_all ?evars renv.env body) with
        | Lambda (x,a,body) ->
          begin
            let rs = check_inert_subterm_rec_call renv rs a in
            match stack with
            | elt :: stack ->
              let renv', stack', body' = pop_argument cache NoNeedReduce renv elt stack x a body in
              check_nested_fix_body renv' (decr-1) stack' rs body'
            | [] ->
              let renv' = push_var_renv renv (redex_level rs) (x,a) in
              check_nested_fix_body renv' (decr-1) [] rs body
          end
        | _ -> assert false
        (* We know from find_uniform_parameters that they are wellformed *)

  and check_rec_call_state renv needreduce_of_head stack rs expand_head =
    (* Test if either the head or the stack of a state
       needs the state to be reduced before continuing checking *)
    match needreduce_of_head ||| needreduce_of_stack stack with
    | NoNeedReduce -> rs
    | NeedReduce _ as e ->
        (* Expand if possible, otherwise, last chance, propagate need
           for expansion, in the hope to be eventually erased *)
        match expand_head () with
        | None -> e :: List.tl rs
        | Some (c, stack') -> check_rec_call_stack renv (stack'@stack) rs c

  and check_inert_subterm_rec_call renv rs c =
    (* Check rec calls of a term which does not interact with its
       immediate context and which can be possibly erased at higher
       level of the redex stack *)
    let need_reduce, rs = check_rec_call renv rs c in
    check_rec_call_state renv need_reduce [] rs (fun () -> None)

  and check_rec_call renv rs c =
    (* either fails if a non guarded call occurs or tells if there is
       rec call on a variable bound at the top of [c] and update the
       need for reduction in the redex stack with rec calls on
       variables bound at higher levels of the redex stack *)
    List.sep_first (check_rec_call_stack renv [] (NoNeedReduce::rs) c)

  in
  let need_reduce, rs = check_rec_call renv [] def in
  assert (List.is_empty rs);
  match need_reduce with
  | NeedReduce (env,err) -> raise (FixGuardError (env,err))
  | NoNeedReduce -> ()

let inductive_of_mutfix ?evars ?elim_to env ((nvect,bodynum),(names,types,bodies as recdef)) =
  let nbfix = Array.length bodies in
  if Int.equal nbfix 0
    || not (Int.equal (Array.length nvect) nbfix)
    || not (Int.equal (Array.length types) nbfix)
    || not (Int.equal (Array.length names) nbfix)
    || bodynum < 0
    || bodynum >= nbfix
  then anomaly (Pp.str "Ill-formed fix term.");
  let fixenv = push_rec_types recdef env in
  let vdefj = judgment_of_fixpoint recdef in
  let raise_err env i err =
    error_ill_formed_rec_body env (Type_errors.FixGuardError err) names i fixenv vdefj in
  (* Check the i-th definition with recarg k *)
  let find_ind i k def =
    (* check fi does not appear in the k+1 first abstractions,
       gives the type of the k+1-eme abstraction (must be an inductive)  *)
    let rec check_occur env n def =
      match kind (whd_all ?evars env def) with
        | Lambda (x,a,b) ->
            if noccur_with_meta n nbfix a then
              let env' = push_rel (LocalAssum (x,a)) env in
              if Int.equal n (k + 1) then
                (* get the inductive type of the fixpoint *)
                let (mind, _) =
                  try find_inductive ?evars env a
                  with Not_found ->
                    raise_err env i (RecursionNotOnInductiveType a) in
                let mib,_ = lookup_mind_specif env (out_punivs mind) in
                if mib.mind_finite != Finite then
                  raise_err env i (RecursionNotOnInductiveType a);
                (mind, (env', b))
              else check_occur env' (n+1) b
            else anomaly ~label:"check_one_fix" (Pp.str "Bad occurrence of recursive call.")
        | _ -> raise_err env i (NotEnoughAbstractionInFixBody k)
    in
    let ((ind, inst), _) as res = check_occur fixenv 1 def in
    let _, mip = lookup_mind_specif env ind in
    (* recursive sprop means non record with projections -> squashed *)
    let () =
      if Environ.ind_ignores_elim_constraints env ind then () else
      let sind = UVars.subst_instance_sort inst mip.mind_sort in
      let u = Sorts.univ_of_sort sind in
      (* This is an approximation: a [Relevant] variable might be of sort [Prop]
          or [Type]. As we only care about the quality, we have to be conservative
          here, i.e., every relevant sort (so, [Prop] or above) can be eliminated
          into any other relevant sort. *)
      let bsort = match names.(i).Context.binder_relevance with
        | Irrelevant -> Sorts.sprop
        | Relevant -> Sorts.prop
        | RelevanceVar q -> Sorts.qsort q u in
      let elim_to = match elim_to with
        | Some f -> f
        | None -> eliminates_to (Environ.qualities env) in
      if not (is_allowed_fixpoint elim_to sind bsort) then
        raise_err env i @@ FixpointOnNonEliminable (sind, bsort)
    in
    res
  in
  (* Do it on every fixpoint *)
  let rv = Array.map2_i find_ind nvect bodies in
  (Array.map fst rv, Array.map snd rv)


let check_fix ?evars ?elim_to env ((nvect,_),(names,_,bodies as recdef) as fix) =
  let cache = Cache.create () in
  let flags = Environ.typing_flags env in
  let nbfix = Array.length bodies in
  (* The same raw-prefix rule for the block the kernel is checking here, not
     only for the blocks nested inside its bodies: [check_occur] in
     [inductive_of_mutfix] reduces this prefix away too, so a call to one of
     these functions hidden in it reaches no check either, and a dead one is
     accepted by every 9.2 we have (test-suite/failure/
     guard_prefix_toplevel_let.v). Only this block's own functions are in
     question: anything enclosing it is covered by the enclosing block's own
     check, where this fix is a nested one. The rule runs BEFORE
     [inductive_of_mutfix], because that function raises the kernel anomaly
     "Bad occurrence of recursive call" on a prefix binder whose TYPE
     mentions the block (breaka/D5.v), and a guard refusal is the honest
     answer there. *)
  let () =
    if flags.check_guarded
       && Int.equal (Array.length nvect) nbfix
       && Int.equal (Array.length names) nbfix
    then
      let fixenv = push_rec_types recdef env in
      Array.iteri (fun i body ->
          if fst (raw_prefix_escapes fixenv nvect nvect.(i) body)
          then
            error_ill_formed_rec_body fixenv
              (Type_errors.FixGuardError (NotEnoughAbstractionInFixBody nvect.(i)))
              names i fixenv (judgment_of_fixpoint recdef))
        bodies in
  let (minds, rdef) = inductive_of_mutfix ?evars ?elim_to env fix in
  if flags.check_guarded then
    let get_tree (kn,i) =
      let mib = Environ.lookup_mind kn env in
      mib.mind_packets.(i).mind_recargs
    in
    let trees = Array.map (fun (mind,_) -> get_tree mind) minds in
    for i = 0 to Array.length bodies - 1 do
      let (fenv,body) = rdef.(i) in
      let renv = make_renv fenv nvect.(i) trees.(i) in
      try check_one_fix cache ?evars renv nvect trees body
      with FixGuardError (fixenv,err) ->
        error_ill_formed_rec_body fixenv (Type_errors.FixGuardError err) names i
          (push_rec_types recdef env) (judgment_of_fixpoint recdef)
    done
  else
    ()

(************************************************************************)
(* Co-fixpoints. *)

exception CoFixGuardError of env * cofix_guard_error

let anomaly_ill_typed () =
  anomaly ~label:"check_one_cofix" (Pp.str "too many arguments applied to constructor.")

let rec codomain_is_coind ?evars env c =
  let b = whd_all ?evars env c in
  match kind b with
    | Prod (x,a,b) ->
        codomain_is_coind ?evars (push_rel (LocalAssum (x,a)) env) b
    | _ ->
        (try find_coinductive ?evars env b
        with Not_found ->
          raise (CoFixGuardError (env, CodomainNotInductiveType b)))

let check_one_cofix cache ?evars env nbfix def deftype =
  let rec check_rec_call env alreadygrd n tree vlra t =
    if not (noccur_with_meta n nbfix t) then
      let () = check_erased env n t in
      let c,args = decompose_app_list (whd_all ?evars env t) in
      match kind c with
        | Rel p when  n <= p && p < n+nbfix ->
            (* recursive call: must be guarded and no nested recursive
               call allowed *)
            if not alreadygrd then
              raise (CoFixGuardError (env,UnguardedRecursiveCall t))
            else if not(List.for_all (noccur_with_meta n nbfix) args) then
              raise (CoFixGuardError (env,NestedRecursiveOccurrences))
        | Construct ((_,i as cstr_kn),_u)  ->
            let lra = vlra.(i-1) in
            let mI = inductive_of_constructor cstr_kn in
            let (mib,_mip) = lookup_mind_specif env mI in
            (* The parameters are evaluated too (cbv evaluates every
               constructor argument) and no position below measures them, so
               a recursive occurrence there is refused like one in a
               non-recursive argument (test-suite/failure/
               guard_cofix_ctor_param.v). This branch's parent, and the 9.2
               base ca856abb5b, take the List.skipn below and never look at
               the parameters. *)
            let () = List.iteri (fun j a ->
                if j < mib.mind_nparams && not (noccur_with_meta n nbfix a) then
                  raise (CoFixGuardError (env, RecCallInNonRecArgOfConstructor a)))
                args in
            let realargs = List.skipn mib.mind_nparams args in
            let rec process_args_of_constr = function
              | (t::lr), (rar::lrar) ->
                  if is_norec_path rar then
                    if noccur_with_meta n nbfix t
                    then process_args_of_constr (lr, lrar)
                    else raise (CoFixGuardError
                                 (env,RecCallInNonRecArgOfConstructor t))
                  else begin
                      check_rec_call env true n rar (dest_subterms rar) t;
                      process_args_of_constr (lr, lrar)
                    end
              | [],_ -> ()
              | _ -> anomaly_ill_typed ()
            in process_args_of_constr (realargs, lra)

        | Lambda (x,a,b) ->
            let () = assert (List.is_empty args) in
            if noccur_with_meta n nbfix a then
              let env' = push_rel (LocalAssum (x,a)) env in
              check_rec_call env' alreadygrd (n+1) tree vlra b
            else
              raise (CoFixGuardError (env,RecCallInTypeOfAbstraction a))

        | CoFix (_j,(_,varit,vdefs as recdef)) ->
            if List.for_all (noccur_with_meta n nbfix) args
            then
              if Array.for_all (noccur_with_meta n nbfix) varit then
                let nbfix = Array.length vdefs in
                let env' = push_rec_types recdef env in
                (Array.iter (check_rec_call env' alreadygrd (n+nbfix) tree vlra) vdefs;
                 List.iter (check_rec_call env alreadygrd n tree vlra) args)
              else
                raise (CoFixGuardError (env,RecCallInTypeOfDef c))
            else
              raise (CoFixGuardError (env,UnguardedRecursiveCall c))

        | Case (ci, u, pms, p, iv, tm, br) -> (* iv ignored: just a cache *)
          begin
            let (_, (p,_), _iv, tm, vrest) = expand_case env (ci, u, pms, p, iv, tm, br) in
            let tree = match restrict_spec cache ?evars env (Subterm (Int.Set.empty, Strict, tree)) p with
            | Dead_code -> assert false
            | Subterm (_, _, tree') -> tree'
            | _ -> raise (CoFixGuardError (env, ReturnPredicateNotCoInductive c))
            in
               if (noccur_with_meta n nbfix p) then
                 if (noccur_with_meta n nbfix tm) then
                   if (List.for_all (noccur_with_meta n nbfix) args) then
                     let vlra = dest_subterms tree in
                     Array.iter (check_rec_call env alreadygrd n tree vlra) vrest
                   else
                     raise (CoFixGuardError (env,RecCallInCaseFun c))
                 else
                   raise (CoFixGuardError (env,RecCallInCaseArg c))
               else
                 raise (CoFixGuardError (env,RecCallInCasePred c))
           end

        | Meta _ -> ()
        | Evar _ ->
            List.iter (check_rec_call env alreadygrd n tree vlra) args
        | Rel _ | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Const _
          | Ind _ | Fix _ | Proj _ | Int _ | Float _ | String _
          | Array _ ->
           raise (CoFixGuardError (env,NotGuardedForm t))

  (* The analysis above dispatches on [whd_all t], while the kernel stores
     [t] as written, so whatever head reduction DROPS on the way to that
     normal form is checked by nothing and is still evaluated later: a dead
     let value, a dead beta argument, the branches a match on a known
     constructor does not select and the constructor arguments the selected
     branch does not read, the fields a projection of a known record does not
     select, and the same material inside the head or the scrutinee while
     they are reduced. A recursive call hidden there makes the kernel accept
     a cofixpoint whose evaluation does not terminate
     (test-suite/failure/guard_cofix_dead_*.v).

     [check_erased] walks the head-reduction path of [t] itself and refuses
     the definition, with an ordinary guard error, when anything that path
     drops mentions a function of the block. Dropped types (a cast's type, a
     let's annotation, the domain of a reduced abstraction, a return
     predicate) are held to the same rule. Nothing is looked up in the
     recursion tree, so a dropped term of any type is safe to check: the
     rule this replaces submitted dropped terms to [check_rec_call] with the
     codomain's tree, and died with an out-of-bounds anomaly on a dropped
     term of another inductive type
     (test-suite/failure/guard_cofix_dead_other_type.v).

     The walk follows the reductions [whd_all] performs at the head: beta,
     zeta, delta of local and global definitions, iota of a match and of a
     projection on a constructor or on a cofixpoint, and iota of a fixpoint
     whose recursive argument reduces to a constructor. Three reductions it
     does not take apart: a primitive at the head, a rewrite rule at the
     head, and the case inversion of a match whose scrutinee stays stuck
     (which drops that scrutinee). For each of the three the term as a whole
     must not mention the block; when it does not, nothing that [whd_all]
     drops from it can, and the walk continues from [whd_all] of it.

     One reduction escapes that rule, deliberately: a rewrite rule whose
     left side fires only UNDER a match or a projection. The walk reduces
     the scrutinee, the rule does not fire there, and the stuck match is
     returned without the application ever being the head, so what the rule
     drops is unchecked. A proof that uses rewrite rules names the symbol in
     [Print Assumptions], which is where this is caught. *)
  and check_erased env n t =
    (* [dropped]/[inert] walk a dropped VALUE position, re-reducing with
       [whd_erasing], so a sub-term the dropped term duplicates would be
       examined once per copy. The memo records, per depth, the sub-terms
       already checked OK there and skips a repeat: verdict-preserving (a
       repeat accepts again) and never skipping a refusal (a refusal raises
       before the record). A repeat is found two ways: by physical identity,
       for the copies [subst] shares (scanned over the whole depth, each test
       is [==]); and up to [memo_equal], for copies written twice in the
       source, compared only against the few newest records whose bounded
       structural hash matches and with a budget per comparison, so a long
       run of similar terms (a tower, a list of literals) costs a constant per
       record. [memo_equal] compares casts and case-inversion indices, which
       the walk does not ignore. One memo per top-level [check_erased],
       threaded through the walk: nothing the walk calls re-enters
       [check_erased] or [check_rec_call]. The key needs no environment: the
       walk extends the environment only with [LocalAssum] binders, which
       [whd_erasing] never unfolds, so equal terms at one depth reach one
       verdict. *)
    let memo = (Hashtbl.create 17, Hashtbl.create 17) in
    let _ : constr = whd_erasing memo env n t in ()

  (* A dropped term whose only mention of the block is the HEAD of its
     application, a function of the block applied to arguments that mention
     no function of the block, possibly under abstractions whose domains
     mention none either, is a VALUE that nothing forces: a cofixpoint is
     unfolded only as the scrutinee of a match or the argument of a
     projection, and a dropped term is never in either position, nor at the
     head of an application. Evaluating it, by name or by value, builds the
     cofixpoint or a partial application of it and discards it. The attacks
     this rule exists for put a DESTRUCTION of the block there (the head is
     then a constant whose body matches on it), so their head is not a
     function of the block and they are refused as before
     (test-suite/failure/guard_cofix_dead_{beta,let,match}.v). *)
  and cofix_inert n c =
    match kind c with
    | Lambda (_, ty, b) -> noccur_with_meta n nbfix ty && cofix_inert (n + 1) b
    | _ ->
      let hd, args = decompose_app c in
      match kind hd with
      | Rel p when n <= p && p < n + nbfix ->
        Array.for_all (noccur_with_meta n nbfix) args
      | _ -> false

  and erased env n c =
    if not (noccur_with_meta n nbfix c) && not (cofix_inert n c) then
      raise (CoFixGuardError (env, UnguardedRecursiveCall c))

  (* The rule before the exemption: any mention of the block is refused.
     Used where a dropped position can still be read after all: the
     parameters of a match, and the arguments of a constructor that has
     let-ins, which a let-in value reads and call-by-value computes at iota
     even when the selected branch does not read the argument. *)
  and erased_strict env n c =
    if not (noccur_with_meta n nbfix c) then
      raise (CoFixGuardError (env, UnguardedRecursiveCall c))

  (* [memo]'s equality: structural, like [Constr.compare_head], but it
     compares casts (the walk holds a cast's type to [erased] and routes a
     binder read only by a cast type there, so two terms equal up to casts
     can get different verdicts) and case-inversion indices (held to
     [erased_strict] at iota). Physically equal sub-terms compare in one
     step. [budget] counts the nodes visited; when it runs out the answer is
     [false], which only costs the memo a skip. *)
  and memo_equal budget nargs t u =
    t == u ||
    (decr budget; !budget > 0) &&
    let eq_evar (e1, l1) (e2, l2) =
      Evar.equal e1 e2 && SList.equal (memo_equal budget 0) l1 l2 in
    match kind t, kind u with
    | Cast (c1, k1, ty1), Cast (c2, k2, ty2) ->
      k1 == k2 && memo_equal budget 0 c1 c2 && memo_equal budget 0 ty1 ty2
    | Cast _, _ | _, Cast _ -> false
    | App (f1, a1), App (f2, a2) ->
      Int.equal (Array.length a1) (Array.length a2) &&
      memo_equal budget (nargs + Array.length a1) f1 f2 &&
      Array.equal (memo_equal budget 0) a1 a2
    | App _, _ | _, App _ -> false
    | Case (_, _, _, _, iv1, _, _), Case (_, _, _, _, iv2, _, _) ->
      (match iv1, iv2 with
       | NoInvert, NoInvert -> true
       | CaseInvert { indices = i1 }, CaseInvert { indices = i2 } ->
         Array.equal (memo_equal budget 0) i1 i2
       | (NoInvert | CaseInvert _), _ -> false) &&
      Constr.compare_head eq_evar (memo_equal budget) nargs t u
    | _ -> Constr.compare_head eq_evar (memo_equal budget) nargs t u

  (* Dropped VALUE positions whose binder iota does not later REREAD and so
     call-by-value never forces: unselected match branches, plain unread
     constructor arguments (when the constructor has no let-in), dead let
     values, dead beta arguments, dropped projection fields. [dropped]
     accepts a term iff no occurrence of the block can be forced by a match
     or a projection in it. It extends [erased]'s [cofix_inert] exemption to
     constructor-headed inert terms ([c r]) and to any head the walk can
     follow safely; a head the walk cannot follow is refused only while a
     block occurrence still survives, so [coqchk] unfolding further cannot
     reach a force [coqc] did not. Positions iota CAN still force (match
     parameters, case-inversion indices, constructor arguments when the
     constructor has a let-in) stay with [erased_strict] above. *)
  and dropped ((phys, strct) as memo) env n t =
    if not (noccur_with_meta n nbfix t) then begin
      let same = Option.default [] (Hashtbl.find_opt phys n) in
      let key = (n, Hashtbl.hash_param 20 200 t) in
      let rec equal_recent k = function
        | [] -> false
        | u :: l -> k > 0 && (memo_equal (ref 256) 0 t u || equal_recent (k - 1) l)
      in
      if not (List.memq t same || equal_recent 8 (Hashtbl.find_all strct key)) then begin
        let () = inert memo env n t in
        let same = Option.default [] (Hashtbl.find_opt phys n) in
        let () = Hashtbl.replace phys n (t :: same) in
        Hashtbl.add strct key t
      end
    end

  and inert memo env n t =
    let hd, args = decompose_app_list (whd_erasing memo env n t) in
    match kind hd with
    | Rel p when n <= p && p < n + nbfix ->
      List.iter (erased env n) args
    | Construct _ -> List.iter (dropped memo env n) args
    | Lambda (x, a, b) when List.is_empty args ->
      let () = erased env n a in
      dropped memo (push_rel (LocalAssum (x, a)) env) (n + 1) b
    | CoFix (_, (_, varit, vdefs as recdef)) ->
      let () = List.iter (erased env n) args in
      let () = Array.iter (erased env n) varit in
      let env' = push_rec_types recdef env in
      Array.iter (dropped memo env' (n + Array.length vdefs)) vdefs
    | Case (ci, u, pms, p, iv, tm, br) ->
      (* A stuck match, or a stuck projection below, is a redex in waiting:
         once its scrutinee resolves (in an instance, under [cbv], in
         [coqchk]'s own delta) the selected branch may destroy whatever it is
         applied to. So its scrutinee AND its arguments are held to
         [erased_strict]; [erased]'s [cofix_inert] exemption covers only a
         position no destructor can reach. Its parameters keep the strict rule
         the iota arm below gives the parameters of a matched constructor. *)
      let () = erased_strict env n tm in
      let () = List.iter (erased_strict env n) args in
      let (_, (p', _), _, _, brs) = expand_case env (ci, u, pms, p, iv, tm, br) in
      let () = Array.iter (erased_strict env n) pms in
      let () = erased env n p' in
      Array.iter (dropped memo env n) brs
    | Proj (_, _, c) ->
      let () = erased_strict env n c in
      List.iter (erased_strict env n) args
    | Meta _ -> ()
    | Evar _ -> List.iter (dropped memo env n) args
    | _ ->
      if not (noccur_with_meta n nbfix (Term.applist (hd, args))) then
        raise (CoFixGuardError (env, UnguardedRecursiveCall t))

  and whd_erasing memo env n t =
    match kind t with
    | Cast (c, _, ty) ->
      let () = erased env n ty in
      whd_erasing memo env n c
    | LetIn (_, v, ty, b) ->
      let () = erased env n ty in
      let () = if noccurn 1 b then dropped memo env n v in
      whd_erasing memo env n (subst1 v b)
    | App (f, args) ->
      let hd, fargs = decompose_app_list (whd_erasing memo env n f) in
      whd_erasing_app memo env n hd (fargs @ Array.to_list args)
    | Case (ci, u, pms, p, iv, tm, br) ->
      let (ci', (p', _), _, tm', brs) = expand_case env (ci, u, pms, p, iv, tm, br) in
      let tmr = whd_erasing memo env n tm' in
      let hd, cargs = decompose_app_list tmr in
      begin match kind hd with
      | Construct ((_, i), _ as cstr) ->
        let () = erased env n p' in
        let () = Array.iteri (fun j b -> if not (Int.equal j (i - 1)) then dropped memo env n b) brs in
        let () = List.iteri (fun j a -> if j < ci'.ci_npar then erased_strict env n a) cargs in
        (* Iota also drops the case-inversion indices. They are not this
           exemption's business, so they keep the strict rule. *)
        let () = match iv with
          | NoInvert -> ()
          | CaseInvert { indices } -> Array.iter (erased_strict env n) indices in
        (* The constructor arguments whose binder the selected branch does
           not read are dropped by the substitution. When the constructor
           has a let-in, its value may read such an argument and is computed
           at iota, so the argument is held to the strict rule. *)
        let ctx, body = Term.decompose_lambda_n_decls ci'.ci_cstr_ndecls.(i - 1) brs.(i - 1) in
        let nd = List.length ctx in
        let has_letin = List.exists (function LocalDef _ -> true | LocalAssum _ -> false) ctx in
        let rec unread k decls args = match decls, args with
          | [], _ | _, [] -> ()
          | LocalDef _ :: decls, args -> unread (k + 1) decls args
          | LocalAssum _ :: decls, a :: args ->
            let () =
              if noccurn (nd - k) body then
                (if has_letin then erased_strict env n a else dropped memo env n a) in
            unread (k + 1) decls args
        in
        let () = unread 0 (List.rev ctx) (List.skipn_at_best ci'.ci_npar cargs) in
        whd_erasing memo env n (apply_branch cstr cargs ci' brs)
      | CoFix cofix ->
        whd_erasing memo env n
          (mkCase (ci, u, pms, p, iv, mkApp (contract_cofix cofix, Array.of_list cargs), br))
      | _ ->
        begin match iv with
        | CaseInvert _ -> let () = erased env n t in whd_all ?evars env t
        | NoInvert -> mkCase (ci, u, pms, p, iv, tmr, br)
        end
      end
    | Proj (pr, r, c) ->
      let cr = whd_erasing memo env n c in
      let hd, args = decompose_app_list cr in
      begin match kind hd with
      | Construct _ ->
        let k = Projection.npars pr + Projection.arg pr in
        let () = List.iteri (fun j a -> if not (Int.equal j k) then dropped memo env n a) args in
        whd_erasing memo env n (List.nth args k)
      | CoFix cofix ->
        whd_erasing memo env n (mkProj (pr, r, mkApp (contract_cofix cofix, Array.of_list args)))
      | _ -> mkProj (pr, r, cr)
      end
    | Rel k ->
      begin match lookup_rel k env with
      | LocalDef (_, b, _) -> whd_erasing memo env n (lift k b)
      | LocalAssum _ -> t
      end
    | Var id ->
      let open! Context.Named.Declaration in
      begin match lookup_named id env with
      | LocalDef (_, b, _) -> whd_erasing memo env n b
      | LocalAssum _ -> t
      end
    | Const (c, _ as cu) ->
      if evaluable_constant c env then whd_erasing memo env n (constant_value_in env cu)
      else if Environ.is_primitive env c || Environ.is_symbol env c then whd_all ?evars env t
      else t
    | Lambda _ | Prod _ | Sort _ | Construct _ | Ind _ | CoFix _ | Fix _
    | Evar _ | Meta _ | Int _ | Float _ | String _ | Array _ -> t

  and whd_erasing_app memo env n hd args =
    match kind hd, args with
    | _, [] -> hd
    | Lambda (_, ty, b), a :: rest ->
      let () = erased env n ty in
      let () = if noccurn 1 b then dropped memo env n a in
      let hd', args' = decompose_app_list (whd_erasing memo env n (subst1 a b)) in
      whd_erasing_app memo env n hd' (args' @ rest)
    | Fix ((recindxs, i), _ as fix), _ when List.length args > recindxs.(i) ->
      let k = recindxs.(i) in
      let ra = whd_erasing memo env n (List.nth args k) in
      let args = List.mapi (fun j a -> if Int.equal j k then ra else a) args in
      if isConstruct (fst (decompose_app ra)) then
        let hd', args' = decompose_app_list (whd_erasing memo env n (contract_fix fix)) in
        whd_erasing_app memo env n hd' (args' @ args)
      else Term.applist (hd, args)
    | Const (c, _), _ when Environ.is_primitive env c || Environ.is_symbol env c ->
      let t = Term.applist (hd, args) in
      let () = erased env n t in
      whd_all ?evars env t
    | _ -> Term.applist (hd, args) in

  let ((mind, _),_) = codomain_is_coind ?evars env deftype in
  let vlra = lookup_subterms env mind in
  check_rec_call env false 1 vlra (dest_subterms vlra) def

(* The  function which checks that the whole block of definitions
   satisfies the guarded condition *)

let check_cofix ?evars env (_bodynum,(names,types,bodies as recdef)) =
  let cache = Cache.create () in
  let flags = Environ.typing_flags env in
  if flags.check_guarded then
    let nbfix = Array.length bodies in
    for i = 0 to nbfix-1 do
      let fixenv = push_rec_types recdef env in
      try check_one_cofix cache ?evars fixenv nbfix bodies.(i) types.(i)
      with CoFixGuardError (errenv,err) ->
        error_ill_formed_rec_body errenv (Type_errors.CoFixGuardError err) names i
          fixenv (judgment_of_fixpoint recdef)
    done
  else
    ()

module Template = struct
  let bind_kind = bind_kind
  let template_subst_sort = template_subst_sort
  let max_template_quality = max_template_quality
end
