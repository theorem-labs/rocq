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
open Declarations
open Util

(* ------------------------------------------------------------------ *)
(* The option, off by default.                                         *)
(* ------------------------------------------------------------------ *)

let flag_enabled = ref false
let flag_verbose = ref false

let set_enabled b = flag_enabled := b
let enabled () = !flag_enabled
let set_verbose b = flag_verbose := b
let verbose () = !flag_verbose

(* ------------------------------------------------------------------ *)
(* Comparing two blocks.                                               *)
(* ------------------------------------------------------------------ *)

type umap = {
  fwd : Univ.Level.t Univ.Level.Map.t;
  bwd : Univ.Level.t Univ.Level.Map.t;
}

let empty_umap = { fwd = Univ.Level.Map.empty; bwd = Univ.Level.Map.empty }

let umap_pairs u =
  Univ.Level.Map.fold
    (fun a b acc -> if Univ.Level.equal a b then acc else (a, b) :: acc)
    u.fwd []

type diff =
  | DTerm of Constr.t * Constr.t
  | DSort of Sorts.t * Sorts.t
  | DLevel of Univ.Level.t * Univ.Level.t
  | DQuality of Sorts.Quality.t * Sorts.Quality.t
  | DGlobal of string * string
  | DId of Id.t * Id.t
  | DCount of string * int * int
  | DField of string
  | DIn of string * diff

let rec pr_diff = function
  | DTerm (a, b) ->
    Pp.(str "terms differ: " ++ Constr.debug_print a ++ str " vs "
        ++ Constr.debug_print b)
  | DSort (a, b) ->
    Pp.(str "sorts differ: " ++ Sorts.debug_print a ++ str " vs "
        ++ Sorts.debug_print b)
  | DLevel (a, b) ->
    Pp.(str "universe levels cannot be matched: " ++ Univ.Level.raw_pr a
        ++ str " vs " ++ Univ.Level.raw_pr b)
  | DQuality (a, b) ->
    Pp.(str "sort qualities differ: " ++ Sorts.Quality.raw_pr a ++ str " vs "
        ++ Sorts.Quality.raw_pr b)
  | DGlobal (a, b) ->
    Pp.(str "names differ: " ++ str a ++ str " vs " ++ str b)
  | DId (a, b) ->
    Pp.(str "identifiers differ: " ++ Id.print a ++ str " vs " ++ Id.print b)
  | DCount (what, a, b) ->
    Pp.(str what ++ str " differs: " ++ int a ++ str " vs " ++ int b)
  | DField what -> Pp.(str what ++ str " differs")
  | DIn (where, d) -> Pp.(str "in " ++ str where ++ str ": " ++ pr_diff d)

let ( let* ) r f = match r with Ok x -> f x | Error _ as e -> e

let wrap where = function Ok _ as o -> o | Error d -> Error (DIn (where, d))

let rec fold2 f u l1 l2 err = match l1, l2 with
  | [], [] -> Ok u
  | x1 :: r1, x2 :: r2 -> let* u = f u x1 x2 in fold2 f u r1 r2 err
  | _ -> Error err

let fold_array2 f u a1 a2 err =
  if not (Int.equal (Array.length a1) (Array.length a2)) then Error err
  else
    let rec go u i =
      if Int.equal i (Array.length a1) then Ok u
      else let* u = f u a1.(i) a2.(i) in go u (i + 1)
    in
    go u 0

(* {6 Universes} *)

let unify_level u l1 l2 =
  let bad = Error (DLevel (l1, l2)) in
  match Univ.Level.Map.find_opt l1 u.fwd with
  | Some r -> if Univ.Level.equal r l2 then Ok u else bad
  | None ->
    match Univ.Level.Map.find_opt l2 u.bwd with
    | Some _ -> bad
    | None ->
      Ok { fwd = Univ.Level.Map.add l1 l2 u.fwd;
           bwd = Univ.Level.Map.add l2 l1 u.bwd }

(* A universe is a set of (level, increment) pairs. [Universe.repr] lists them
   in the levels' own order, so for a universe that is not a single level the
   two sides may be listed in different orders and a legitimate match can be
   missed. That loses merges; it never grants one. *)
let unify_universe u v1 v2 =
  let r1 = Univ.Universe.repr v1 and r2 = Univ.Universe.repr v2 in
  fold2 (fun u (l1, n1) (l2, n2) ->
      if not (Int.equal n1 n2) then Error (DLevel (l1, l2))
      else unify_level u l1 l2)
    u r1 r2 (DField "universe")

let unify_sort u s1 s2 = match s1, s2 with
  | Sorts.SProp, Sorts.SProp | Sorts.Prop, Sorts.Prop | Sorts.Set, Sorts.Set ->
    Ok u
  | Sorts.Type v1, Sorts.Type v2 -> unify_universe u v1 v2
  | Sorts.QSort (q1, v1), Sorts.QSort (q2, v2) ->
    if not (Sorts.QVar.equal q1 q2) then Error (DSort (s1, s2))
    else unify_universe u v1 v2
  | (Sorts.SProp | Sorts.Prop | Sorts.Set | Sorts.Type _ | Sorts.QSort _), _ ->
    Error (DSort (s1, s2))

let unify_relevance u r1 r2 =
  if Sorts.relevance_equal r1 r2 then Ok u else Error (DField "relevance")

let unify_instance u i1 i2 =
  let (q1, l1) = UVars.Instance.to_array i1 in
  let (q2, l2) = UVars.Instance.to_array i2 in
  let* u =
    fold_array2 (fun u a b ->
        if Sorts.Quality.equal a b then Ok u else Error (DQuality (a, b)))
      u q1 q2 (DField "universe instance")
  in
  fold_array2 unify_level u l1 l2 (DField "universe instance")

(* {6 Terms} *)

let name_of_const c = Constant.to_string c
let name_of_ind (m, i) = MutInd.to_string m ^ "#" ^ string_of_int i

let rec equal_constr u c1 c2 =
  if c1 == c2 then Ok u else
  let open Constr in
  match kind c1, kind c2 with
  | Rel i, Rel j -> if Int.equal i j then Ok u else Error (DTerm (c1, c2))
  | Var i, Var j -> if Id.equal i j then Ok u else Error (DTerm (c1, c2))
  | Meta i, Meta j -> if Int.equal i j then Ok u else Error (DTerm (c1, c2))
  | Int i, Int j -> if Uint63.equal i j then Ok u else Error (DTerm (c1, c2))
  | Float f, Float g -> if Float64.equal f g then Ok u else Error (DTerm (c1, c2))
  | String s, String t -> if Pstring.equal s t then Ok u else Error (DTerm (c1, c2))
  | Sort s1, Sort s2 -> unify_sort u s1 s2
  | Cast (a1, k1, t1), Cast (a2, k2, t2) ->
    if not (k1 = k2) then Error (DTerm (c1, c2))
    else let* u = equal_constr u a1 a2 in equal_constr u t1 t2
  (* The relevance a binder carries is cached, not recomputed from the type
     beside it, so two declarations can disagree on it while their types
     agree.  Compare it. *)
  | Prod (n1, t1, b1), Prod (n2, t2, b2)
  | Lambda (n1, t1, b1), Lambda (n2, t2, b2) ->
    let* u = unify_relevance u n1.Context.binder_relevance n2.Context.binder_relevance in
    let* u = equal_constr u t1 t2 in equal_constr u b1 b2
  | LetIn (n1, v1, t1, b1), LetIn (n2, v2, t2, b2) ->
    let* u = unify_relevance u n1.Context.binder_relevance n2.Context.binder_relevance in
    let* u = equal_constr u v1 v2 in
    let* u = equal_constr u t1 t2 in
    equal_constr u b1 b2
  | App (f1, a1), App (f2, a2) ->
    let* u = equal_constr u f1 f2 in
    fold_array2 equal_constr u a1 a2 (DTerm (c1, c2))
  | Const (k1, i1), Const (k2, i2) ->
    if not (Constant.CanOrd.equal k1 k2)
    then Error (DGlobal (name_of_const k1, name_of_const k2))
    else unify_instance u i1 i2
  | Ind (n1, i1), Ind (n2, i2) ->
    if not (Ind.CanOrd.equal n1 n2)
    then Error (DGlobal (name_of_ind n1, name_of_ind n2))
    else unify_instance u i1 i2
  | Construct ((n1, j1), i1), Construct ((n2, j2), i2) ->
    if not (Int.equal j1 j2) || not (Ind.CanOrd.equal n1 n2)
    then Error (DGlobal (name_of_ind n1 ^ "/" ^ string_of_int j1,
                         name_of_ind n2 ^ "/" ^ string_of_int j2))
    else unify_instance u i1 i2
  | Proj (p1, r1, t1), Proj (p2, r2, t2) ->
    if not (Projection.CanOrd.equal p1 p2)
    then Error (DGlobal (Projection.to_string p1, Projection.to_string p2))
    else let* u = unify_relevance u r1 r2 in equal_constr u t1 t2
  | Evar (e1, a1), Evar (e2, a2) ->
    if not (Evar.equal e1 e2) then Error (DTerm (c1, c2))
    else
      let l1 = SList.to_list a1 and l2 = SList.to_list a2 in
      fold2 (fun u o1 o2 -> match o1, o2 with
          | None, None -> Ok u
          | Some a, Some b -> equal_constr u a b
          | _ -> Error (DTerm (c1, c2)))
        u l1 l2 (DTerm (c1, c2))
  | Case (ci1, i1, pms1, (p1, pr1), iv1, s1, br1),
    Case (ci2, i2, pms2, (p2, pr2), iv2, s2, br2) ->
    if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind)
    then Error (DGlobal (name_of_ind ci1.ci_ind, name_of_ind ci2.ci_ind))
    else if not (Int.equal ci1.ci_npar ci2.ci_npar)
         || not (Array.equal Int.equal ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls)
         || not (Array.equal Int.equal ci1.ci_cstr_nargs ci2.ci_cstr_nargs)
    then Error (DField "case info")
    else
      let binders u a1 a2 =
        fold_array2 (fun u a b ->
            unify_relevance u a.Context.binder_relevance b.Context.binder_relevance)
          u a1 a2 (DField "case binders")
      in
      let* u = unify_instance u i1 i2 in
      let* u = fold_array2 equal_constr u pms1 pms2 (DTerm (c1, c2)) in
      let* u = unify_relevance u pr1 pr2 in
      let* u = binders u (fst p1) (fst p2) in
      let* u = equal_constr u (snd p1) (snd p2) in
      let* u = match iv1, iv2 with
        | NoInvert, NoInvert -> Ok u
        | CaseInvert { indices = a1 }, CaseInvert { indices = a2 } ->
          fold_array2 equal_constr u a1 a2 (DTerm (c1, c2))
        | (NoInvert | CaseInvert _), _ -> Error (DField "case inversion")
      in
      let* u = equal_constr u s1 s2 in
      fold_array2 (fun u (n1, b1) (n2, b2) ->
          let* u = binders u n1 n2 in equal_constr u b1 b2)
        u br1 br2 (DTerm (c1, c2))
  | Fix ((ln1, i1), (na1, tl1, bl1)), Fix ((ln2, i2), (na2, tl2, bl2)) ->
    if not (Array.equal Int.equal ln1 ln2) || not (Int.equal i1 i2)
    then Error (DField "fixpoint structure")
    else
      let* u = fold_array2 (fun u a b ->
          unify_relevance u a.Context.binder_relevance b.Context.binder_relevance)
          u na1 na2 (DField "fixpoint structure") in
      let* u = fold_array2 equal_constr u tl1 tl2 (DTerm (c1, c2)) in
      fold_array2 equal_constr u bl1 bl2 (DTerm (c1, c2))
  | CoFix (i1, (na1, tl1, bl1)), CoFix (i2, (na2, tl2, bl2)) ->
    if not (Int.equal i1 i2) then Error (DField "cofixpoint structure")
    else
      let* u = fold_array2 (fun u a b ->
          unify_relevance u a.Context.binder_relevance b.Context.binder_relevance)
          u na1 na2 (DField "cofixpoint structure") in
      let* u = fold_array2 equal_constr u tl1 tl2 (DTerm (c1, c2)) in
      fold_array2 equal_constr u bl1 bl2 (DTerm (c1, c2))
  | Array (i1, t1, d1, ty1), Array (i2, t2, d2, ty2) ->
    let* u = unify_instance u i1 i2 in
    let* u = fold_array2 equal_constr u t1 t2 (DTerm (c1, c2)) in
    let* u = equal_constr u d1 d2 in
    equal_constr u ty1 ty2
  | (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Cast _ | Prod _ | Lambda _
    | LetIn _ | App _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Proj _ | Int _ | Float _ | String _ | Array _), _ ->
    Error (DTerm (c1, c2))

(* {6 Blocks} *)

let equal_rel_context u c1 c2 =
  if not (Int.equal (List.length c1) (List.length c2))
  then Error (DCount ("context length", List.length c1, List.length c2))
  else
    let open Context.Rel.Declaration in
    fold2 (fun u d1 d2 -> match d1, d2 with
        | LocalAssum (a1, t1), LocalAssum (a2, t2) ->
          let* u = unify_relevance u a1.Context.binder_relevance
              a2.Context.binder_relevance in
          equal_constr u t1 t2
        | LocalDef (a1, b1, t1), LocalDef (a2, b2, t2) ->
          let* u = unify_relevance u a1.Context.binder_relevance
              a2.Context.binder_relevance in
          let* u = equal_constr u b1 b2 in
          equal_constr u t1 t2
        | (LocalAssum _ | LocalDef _), _ -> Error (DField "context declaration"))
      u c1 c2 (DField "context")

let equal_squash s1 s2 = match s1, s2 with
  | None, None -> true
  | Some AlwaysSquashed, Some AlwaysSquashed -> true
  | Some (SometimesSquashed q1), Some (SometimesSquashed q2) ->
    Sorts.Quality.Set.equal q1 q2
  | _ -> false

let equal_record u r1 r2 = match r1, r2 with
  | NotRecord, NotRecord | FakeRecord, FakeRecord -> Ok u
  | PrimRecord p1, PrimRecord p2 ->
    if not (Id.equal p1.id p2.id) then Error (DId (p1.id, p2.id))
    else if not (Array.equal Id.equal p1.projections p2.projections)
    then Error (DField "projection names")
    else if not (match p1.has_eta, p2.has_eta with
        | AlwaysEta, AlwaysEta | NoEta, NoEta -> true
        | (AlwaysEta | NoEta), _ -> false)
    then Error (DField "record eta")
    else
      let* u = fold_array2 unify_relevance u p1.relevances p2.relevances
          (DField "projection relevances") in
      fold_array2 equal_constr u p1.tys p2.tys (DField "projection types")
  | (NotRecord | FakeRecord | PrimRecord _), _ -> Error (DField "record shape")

(* Every typing flag except the conversion oracle, which is a transparency
   setting, and the three that only pick how reduction is carried out --
   share_reduction, enable_VM, enable_native_compiler. None of the four is
   part of a type's identity, and comparing them would refuse every merge
   between a spec built with, say, -bytecode-compiler yes and an agent built
   without it. What stays compared is check_guarded, check_positive,
   check_universes, check_eliminations where that field exists,
   indices_matter, impredicative_set, sprop_allowed, allow_uip -- and, by the
   record update, any flag added later. *)
let equal_flags f1 f2 =
  let strip f =
    { f with conv_oracle = Conv_oracle.empty; share_reduction = true;
             enable_VM = true; enable_native_compiler = true }
  in
  strip f1 = strip f2

(* Abstract contexts quantify over [Level.var i] and [QVar.make_var i], so
   they are the same in every file and are compared positionally, constraints
   included -- elimination constraints too, not only universe ones. *)
let equal_auctx a1 a2 =
  UVars.eq_sizes (UVars.AbstractContext.size a1) (UVars.AbstractContext.size a2)
  && (let c1 = UVars.AbstractContext.repr a1 in
      let c2 = UVars.AbstractContext.repr a2 in
      Univ.UnivConstraints.equal
        (UVars.UContext.univ_constraints c1) (UVars.UContext.univ_constraints c2)
      && Sorts.ElimConstraints.equal
        (UVars.UContext.elim_constraints c1) (UVars.UContext.elim_constraints c2))

let equal_universes u k1 k2 = match k1, k2 with
  | Monomorphic, Monomorphic -> Ok u
  | Polymorphic a1, Polymorphic a2 ->
    if equal_auctx a1 a2 then Ok u else Error (DField "polymorphic universes")
  | (Monomorphic | Polymorphic _), _ -> Error (DField "universe kind")

let equal_template u t1 t2 = match t1, t2 with
  | None, None -> Ok u
  | Some t1, Some t2 ->
    if not (equal_auctx t1.template_context t2.template_context)
    then Error (DField "template context")
    else
      let* u =
        fold2 (fun u o1 o2 -> match o1, o2 with
            | None, None -> Ok u
            | Some s1, Some s2 -> unify_sort u s1 s2
            | _ -> Error (DField "template parameter"))
          u t1.template_param_arguments t2.template_param_arguments
          (DField "template parameters")
      in
      let* u = unify_sort u t1.template_concl t2.template_concl in
      unify_instance u t1.template_defaults t2.template_defaults
  | (None | Some _), _ -> Error (DField "template polymorphism")

let equal_recargs r1 r2 = Rtree.equal Declareops.eq_recarg r1 r2

let equal_packet u p1 p2 =
  if not (Id.equal p1.mind_typename p2.mind_typename)
  then Error (DId (p1.mind_typename, p2.mind_typename))
  else
    wrap (Id.to_string p1.mind_typename) @@
    if not (Array.equal Id.equal p1.mind_consnames p2.mind_consnames)
    then Error (DField "constructor names")
    else if not (Int.equal p1.mind_nrealargs p2.mind_nrealargs)
    then Error (DCount ("number of indices", p1.mind_nrealargs, p2.mind_nrealargs))
    else if not (Int.equal p1.mind_nrealdecls p2.mind_nrealdecls)
    then Error (DCount ("index context length", p1.mind_nrealdecls, p2.mind_nrealdecls))
    else if not (Array.equal Int.equal p1.mind_consnrealargs p2.mind_consnrealargs)
    then Error (DField "constructor arities")
    else if not (Array.equal Int.equal p1.mind_consnrealdecls p2.mind_consnrealdecls)
    then Error (DField "constructor context lengths")
    else if not (Int.equal p1.mind_nb_constant p2.mind_nb_constant)
         || not (Int.equal p1.mind_nb_args p2.mind_nb_args)
    then Error (DField "VM constructor counts")
    else if not (equal_squash p1.mind_squashed p2.mind_squashed)
    then Error (DField "squash information")
    else if not (equal_recargs p1.mind_recargs p2.mind_recargs)
    then Error (DField "recursive argument tree")
    (* Everything else of the packet: the plain data left once the fields
       holding terms, sorts, relevances, the record shape, the squash
       information and the recursive-argument tree are set aside.  Written
       as a record update so that a field added later is compared without
       this function changing. *)
    else if not (
      { p1 with
        mind_arity_ctxt = p2.mind_arity_ctxt;
        mind_user_arity = p2.mind_user_arity;
        mind_user_lc = p2.mind_user_lc;
        mind_nf_lc = p2.mind_nf_lc;
        mind_record = p2.mind_record;
        mind_sort = p2.mind_sort;
        mind_relevance = p2.mind_relevance;
        mind_squashed = p2.mind_squashed;
        mind_recargs = p2.mind_recargs } = p2)
    then Error (DField "inductive type data")
    else
      let* u = unify_sort u p1.mind_sort p2.mind_sort in
      let* u = unify_relevance u p1.mind_relevance p2.mind_relevance in
      let* u = equal_record u p1.mind_record p2.mind_record in
      let* u = equal_rel_context u p1.mind_arity_ctxt p2.mind_arity_ctxt in
      let* u = equal_constr u p1.mind_user_arity p2.mind_user_arity in
      let* u = fold_array2 equal_constr u p1.mind_user_lc p2.mind_user_lc
          (DField "constructor types") in
      fold_array2 (fun u (c1, t1) (c2, t2) ->
          let* u = equal_rel_context u c1 c2 in equal_constr u t1 t2)
        u p1.mind_nf_lc p2.mind_nf_lc (DField "constructor types")

let eq_mib u _env mib1 mib2 =
  if not (Int.equal (Array.length mib1.mind_packets) (Array.length mib2.mind_packets))
  then Error (DCount ("number of mutual types",
                      Array.length mib1.mind_packets, Array.length mib2.mind_packets))
  else if mib1.mind_finite <> mib2.mind_finite then Error (DField "finiteness")
  else if not (Int.equal mib1.mind_nparams mib2.mind_nparams)
  then Error (DCount ("number of parameters", mib1.mind_nparams, mib2.mind_nparams))
  else if not (Int.equal mib1.mind_nparams_rec mib2.mind_nparams_rec)
  then Error (DCount ("number of uniform parameters",
                      mib1.mind_nparams_rec, mib2.mind_nparams_rec))
  else if not (Option.equal (=) mib1.mind_private mib2.mind_private)
  then Error (DField "privacy")
  (* Everything else of the block: the plain data left once the packets, the
     parameter context, the universes, the template data and the typing
     flags are set aside.  This covers variance, section variance and any
     field added later. *)
  else if not (
    { mib1 with
      mind_packets = mib2.mind_packets;
      mind_params_ctxt = mib2.mind_params_ctxt;
      mind_universes = mib2.mind_universes;
      mind_template = mib2.mind_template;
      mind_typing_flags = mib2.mind_typing_flags;
      mind_hyps = mib2.mind_hyps;
      mind_univ_hyps = mib2.mind_univ_hyps } = mib2)
  then Error (DField "inductive block data")
  else if not (equal_flags mib1.mind_typing_flags mib2.mind_typing_flags)
  then Error (DField "typing flags")
  else if not (List.is_empty mib1.mind_hyps && List.is_empty mib2.mind_hyps)
  then Error (DField "section hypotheses")
  else if not (UVars.Instance.is_empty mib1.mind_univ_hyps
               && UVars.Instance.is_empty mib2.mind_univ_hyps)
  then Error (DField "section universes")
  else
    let* u = equal_universes u mib1.mind_universes mib2.mind_universes in
    let* u = equal_template u mib1.mind_template mib2.mind_template in
    let* u = equal_rel_context u mib1.mind_params_ctxt mib2.mind_params_ctxt in
    fold_array2 equal_packet u mib1.mind_packets mib2.mind_packets
      (DField "mutual block")

(* ------------------------------------------------------------------ *)
(* The shape index: the fast checks, hashed, so that a new block is    *)
(* only ever compared in full with blocks that already agree on all of *)
(* them.  Without it the load step would be quadratic in the number of *)
(* inductives in the session.                                          *)
(* ------------------------------------------------------------------ *)

let index : (string, MutInd.t list ref) Hashtbl.t = Hashtbl.create 509

let shape_key mib =
  let b = Buffer.create 256 in
  let add s = Buffer.add_string b s; Buffer.add_char b '\000' in
  let addi i = add (string_of_int i) in
  addi (Array.length mib.mind_packets);
  addi mib.mind_nparams;
  addi mib.mind_nparams_rec;
  addi (List.length mib.mind_params_ctxt);
  add (match mib.mind_finite with
      | Finite -> "Finite" | CoFinite -> "CoFinite" | BiFinite -> "BiFinite");
  add (match mib.mind_universes with
      | Monomorphic -> "Mono"
      | Polymorphic auctx ->
        let q, l = UVars.AbstractContext.size auctx in
        "Poly" ^ string_of_int q ^ "," ^ string_of_int l);
  add (match mib.mind_template with None -> "NoTemplate" | Some _ -> "Template");
  Array.iter (fun p ->
      add (Id.to_string p.mind_typename);
      addi p.mind_nrealargs;
      addi p.mind_nrealdecls;
      addi (Array.length p.mind_consnames);
      Array.iter (fun c -> add (Id.to_string c)) p.mind_consnames;
      Array.iter addi p.mind_consnrealargs;
      Array.iter addi p.mind_consnrealdecls;
      add (match p.mind_record with
          | NotRecord -> "NotRecord"
          | FakeRecord -> "FakeRecord"
          | PrimRecord { projections; has_eta; _ } ->
            "PrimRecord" ^ string_of_int (Array.length projections)
            ^ (match has_eta with AlwaysEta -> "E" | NoEta -> "e")))
    mib.mind_packets;
  Digest.to_hex (Digest.string (Buffer.contents b))

let index_add key mind =
  match Hashtbl.find_opt index key with
  | Some l -> l := mind :: !l
  | None -> Hashtbl.add index key (ref [mind])

let index_find key =
  match Hashtbl.find_opt index key with Some l -> !l | None -> []

(* The universe context of each library this process has loaded, so that the
   constraints on a level a merge would equate can be compared. *)
let library_univs : Univ.ContextSet.t DirPath.Map.t ref = ref DirPath.Map.empty

(* ------------------------------------------------------------------ *)
(* Undoing, on the way out, every name this process merged.            *)
(* ------------------------------------------------------------------ *)

let merged : KerName.t KerName.Map.t ref = ref KerName.Map.empty

let merge_targets = ref KerName.Set.empty

let record_merge user canon =
  merged := KerName.Map.add user canon !merged;
  merge_targets := KerName.Set.add canon !merge_targets

(* A name whose canonical half this run produced goes back to its own user
   name. A name whose canonical half is one this run merged INTO but whose
   user half is not a merge of ours was acquired some other way -- through
   `Module A := Agent.` or an `Include`, which composes the alias with the
   merged canonical -- and which copy it names cannot be read back out of
   it. That is not guessed: writing the library is refused, with the name in
   the message. The price is that a genuine alias of the library a merge
   pointed at is refused too, in a run that merged; the alternative is
   writing a name the reader never earned. *)
let refuse_alias kn =
  CErrors.user_err
    Pp.(strbrk "-merge-inductives cannot write this library: it mentions " ++
        KerName.print kn ++
        strbrk ", which this run merged into, under another name -- through a \
                module alias or an Include. Compile it without the option \
                (dispatch://BET-895).")

let unmerge_mind mind =
  let u = MutInd.user mind and c = MutInd.canonical mind in
  if KerName.equal u c then mind
  else match KerName.Map.find_opt u !merged with
    | Some c' when KerName.equal c c' -> MutInd.make1 u
    | _ -> if KerName.Set.mem c !merge_targets then refuse_alias c else mind

let unmerge_ind (mind, i as ind) =
  let mind' = unmerge_mind mind in
  if mind' == mind then ind else (mind', i)

let rec unmerge_constr c =
  let c = Constr.map unmerge_constr c in
  match Constr.kind c with
  | Constr.Ind (ind, u) ->
    let ind' = unmerge_ind ind in
    if ind' == ind then c else Constr.mkIndU (ind', u)
  | Constr.Construct ((ind, j), u) ->
    let ind' = unmerge_ind ind in
    if ind' == ind then c else Constr.mkConstructU ((ind', j), u)
  | Constr.Proj (p, r, t) ->
    let p' = Projection.map unmerge_mind p in
    if p' == p then c else Constr.mkProj (p', r, t)
  | Constr.Case (ci, u, pms, p, iv, ct, br) ->
    let ind' = unmerge_ind ci.Constr.ci_ind in
    if ind' == ci.Constr.ci_ind then c
    else Constr.mkCase ({ ci with Constr.ci_ind = ind' }, u, pms, p, iv, ct, br)
  | _ -> c

let unmerge_rel_context ctx = Context.Rel.map unmerge_constr ctx

let unmerge_record r = match r with
  | NotRecord | FakeRecord -> r
  | PrimRecord ({ tys; _ } as info) ->
    let tys' = Array.Smart.map unmerge_constr tys in
    if tys' == tys then r else PrimRecord { info with tys = tys' }

let unmerge_packet p =
  { p with
    mind_arity_ctxt = unmerge_rel_context p.mind_arity_ctxt;
    mind_user_arity = unmerge_constr p.mind_user_arity;
    mind_user_lc = Array.Smart.map unmerge_constr p.mind_user_lc;
    mind_nf_lc =
      Array.Smart.map (fun (ctx, t) -> unmerge_rel_context ctx, unmerge_constr t)
        p.mind_nf_lc;
    mind_record = unmerge_record p.mind_record;
    mind_recargs =
      Rtree.Smart.map (fun ra -> match ra with
          | Norec -> ra
          | Mrec (RecArgInd ind) ->
            let ind' = unmerge_ind ind in
            if ind' == ind then ra else Mrec (RecArgInd ind')
          | Mrec (RecArgPrim _) -> ra)
        p.mind_recargs }

let unmerge_mind_body mib =
  { mib with
    mind_params_ctxt = unmerge_rel_context mib.mind_params_ctxt;
    mind_packets = Array.Smart.map unmerge_packet mib.mind_packets }

let unmerge_const_body cb =
  { cb with
    const_type = unmerge_constr cb.const_type;
    const_body = (match cb.const_body with
        | Def c -> Def (unmerge_constr c)
        | (Undef _ | Primitive _ | Symbol _ | OpaqueDef _) as b -> b);
    const_body_code =
      Option.map (Vmemitcodes.map_body_code unmerge_ind (fun c -> c))
        cb.const_body_code }

(* The same for the targets a delta resolver points at: the resolver of a
   module alias in this library records the merged canonical name, which its
   reader never earned, and which copy the alias names is not recoverable
   from it either. *)
let unmerge_kn kn =
  if KerName.Set.mem kn !merge_targets then refuse_alias kn else kn

let unmerge_delta reso =
  if KerName.Set.is_empty !merge_targets then reso
  else Mod_subst.map_kn_delta_resolver ~fc:unmerge_constr unmerge_kn reso

(* Both sides of a rewrite rule: the right-hand term, and the inductives,
   constructors and projections its left-hand pattern matches on. *)
let rec unmerge_pat_elim e = match e with
  | PEApp args ->
    let args' = Array.Smart.map unmerge_pat_arg args in
    if args' == args then e else PEApp args'
  | PECase (ind, p, br) ->
    let ind' = unmerge_ind ind in
    let p' = unmerge_pat_arg p in
    let br' = Array.Smart.map unmerge_pat_arg br in
    if ind' == ind && p' == p && br' == br then e else PECase (ind', p', br')
  | PEProj p ->
    let p' = Projection.Repr.map unmerge_mind p in
    if p' == p then e else PEProj p'

and unmerge_head h = match h with
  | PHInd (ind, m) ->
    let ind' = unmerge_ind ind in
    if ind' == ind then h else PHInd (ind', m)
  | PHConstr ((ind, j), m) ->
    let ind' = unmerge_ind ind in
    if ind' == ind then h else PHConstr ((ind', j), m)
  | PHLambda (args, he) ->
    let args' = Array.Smart.map unmerge_pat_arg args in
    let he' = unmerge_head_elim he in
    if args' == args && he' == he then h else PHLambda (args', he')
  | PHProd (args, a) ->
    let args' = Array.Smart.map unmerge_pat_arg args in
    let a' = unmerge_pat_arg a in
    if args' == args && a' == a then h else PHProd (args', a')
  | PHRel _ | PHSort _ | PHSymbol _ | PHInt _ | PHFloat _ | PHString _ -> h

and unmerge_head_elim ((h, elims) as he) =
  let h' = unmerge_head h in
  let elims' = List.Smart.map unmerge_pat_elim elims in
  if h' == h && elims' == elims then he else (h', elims')

and unmerge_pat_arg a = match a with
  | EHole _ | EHoleIgnored -> a
  | ERigid he ->
    let he' = unmerge_head_elim he in
    if he' == he then a else ERigid he'

let unmerge_rules rrb =
  let rules = List.Smart.map (fun (c, ({ rhs; lhs_pat = (m, elims); _ } as r) as orig) ->
      let rhs' = unmerge_constr rhs in
      let elims' = List.Smart.map unmerge_pat_elim elims in
      if rhs' == rhs && elims' == elims then orig
      else (c, { r with rhs = rhs'; lhs_pat = (m, elims') }))
      rrb.rewrules_rules
  in
  if rules == rrb.rewrules_rules then rrb else { rewrules_rules = rules }

let unmerge_retro a =
  let open Retroknowledge in
  match a with
  | Register_ind (p, ind) ->
    let ind' = unmerge_ind ind in
    if ind' == ind then a else Register_ind (p, ind')
  | Register_type _ -> a

(* Everything a library writes out goes through this, not only its top-level
   constants and inductives: a merged name inside a Module, a Module Type, a
   functor's signature, a `with Definition`, a module alias's resolver or a
   rewrite rule would otherwise reach the .vo and be taken on trust by a
   reader that never compared anything. *)
let unmerge_name_map = {
  Mod_declarations.nmap_const = unmerge_const_body;
  nmap_mind = unmerge_mind_body;
  nmap_rules = unmerge_rules;
  nmap_constr = unmerge_constr;
  nmap_delta = unmerge_delta;
  nmap_retro = unmerge_retro;
}

let unmerge_structure struc =
  Mod_declarations.map_structure unmerge_name_map struc

let unmerging () = enabled () && not (KerName.Map.is_empty !merged)

let unmerge_exported struc =
  if not (unmerging ()) then struc else unmerge_structure struc

(* ------------------------------------------------------------------ *)
(* The load-time step.                                                 *)
(* ------------------------------------------------------------------ *)

let fields_of_body mb = match Mod_declarations.mod_type mb with
  | MoreFunctor _ -> None
  | NoFunctor struc -> Some struc

(* [mind_private] is forced to [Some true] by [Modops.add_structure] for the
   copy already in the environment, so compare the new block the same way. *)
let as_loaded mib =
  if mib.mind_private != None then { mib with mind_private = Some true } else mib

(* v1 does not merge a universe-polymorphic block, whatever [eq_mib] says
   about it. A template-polymorphic block does merge, on [equal_template]'s
   verdict: an [Inductive w (A : Type)] with no attribute is made template
   automatically (vernac/comInductive.ml), so refusing template blocks would
   refuse every parameterised Type-valued type.

   A PRIVATE block never merges. Its whole point is that only the file that
   declared it may match on it, and two files that declare the same private
   type are two quotients, not one: the first may axiomatise away a
   distinction the second's matches can see. Merging them gives False --
   `Private Inductive pos := mk : nat -> pos.` with `Axiom pos_irr : forall
   n m, mk n = mk m.` on one side, and a match on the other. eq_mib still
   compares them, for the comparator; the refusal is here. *)
let mergeable mib =
  Option.is_empty mib.mind_private
  && (match mib.mind_universes with Monomorphic -> true | Polymorphic _ -> false)

let owned_by dp l = match Univ.Level.name l with
  | Some g -> let (d, _, _) = Univ.UGlobal.repr g in DirPath.equal d dp
  | None -> false

(* Which level pairs this process may turn into equalities: the left level
   must belong to the library being loaded, the right one to the library
   that declared the candidate, and the right one must not belong to the
   library being loaded. A level that belongs to neither -- [Set], [Prop],
   a level of a library the two copies share -- must map to itself, because
   equating it would move a level a third party can name.

   Checking only the first two was not enough in each direction. Without
   the second, the already-loaded copy's level could be equated with a
   THIRD library's level, whenever that is what the candidate's declaration
   mentions. Without the third, two blocks of ONE library (where the
   candidate's library is the library being loaded) could have their levels
   equated, which the first rule alone used to forbid. All three together
   only ever refuse more than any one of them. *)
let pairs_admissible ~new_dp ~cand_dp pairs =
  List.for_all
    (fun (a, b) ->
       owned_by new_dp a && owned_by cand_dp b && not (owned_by new_dp b))
    pairs

(* Every constraint that mentions a level about to be equated must appear, in
   both directions, on the other side too. A constraint between a mapped level
   and a level the two libraries share -- [Set <= u] present on one side and
   not on the other -- is exactly the case this rules out: the declarations
   would be identical and the merge would still import a constraint the other
   copy never had. *)
let constraints_agree ~new_ctx ~old_ctx pairs =
  let fwd =
    List.fold_left (fun m (a, b) -> Univ.Level.Map.add a b m)
      Univ.Level.Map.empty pairs
  in
  let bwd =
    List.fold_left (fun m (a, b) -> Univ.Level.Map.add b a m)
      Univ.Level.Map.empty pairs
  in
  let sigma m l = match Univ.Level.Map.find_opt l m with Some r -> r | None -> l in
  let mentions m (a, _, b) =
    Univ.Level.Map.mem a m || Univ.Level.Map.mem b m
  in
  let restrict m c = Univ.UnivConstraints.filter (mentions m) c in
  let image m c =
    Univ.UnivConstraints.fold
      (fun (a, k, b) acc -> Univ.UnivConstraints.add (sigma m a, k, sigma m b) acc)
      c Univ.UnivConstraints.empty
  in
  let cn = restrict fwd (Univ.ContextSet.constraints new_ctx) in
  let co = restrict bwd (Univ.ContextSet.constraints old_ctx) in
  Univ.UnivConstraints.equal (image fwd cn) co
  && Univ.UnivConstraints.equal cn (image bwd co)

(* Every merge this process has made so far, as one substitution. It is
   applied to EVERY library loaded afterwards, not only to libraries that
   merge something of their own: a .vo is written in its own names, so a later
   library that merely mentions a merged inductive carries the unmerged name
   and has to be rewritten on the way in. Merges are monotone -- a new library
   is always renamed into an already-loaded one, never the other way round --
   so nothing already in the environment ever needs rewriting. *)
let global_subst = ref Mod_subst.empty_subst

(* The merges this process has already made, applied to a library's body
   without looking for new ones. The checker type-checks a library in the
   environment those merges produced, so the body it checks has to name
   them the way that environment does: a checker file naming the statement
   library's inductive directly carries that name unmerged, as it was
   written out, and the declaration it is compared against now has the
   other copy's canonical name. [merge] applies the same substitution again
   afterwards, which is idempotent. *)
let apply_earlier_merges mp mb =
  if not (enabled ()) || Mod_subst.is_empty_subst !global_subst then mb
  else
    Mod_declarations.subst_module Mod_declarations.subst_codom
      !global_subst mp mb

(* A library the checker loads without checking it -- named by -admit, or
   reached as a dependency of a -norec library -- DOES take part in merges,
   as source and as target. This is the grader's ordinary shape: it lists
   only the agent's libraries and the checker files, so our own statement
   library arrives unchecked, and refusing to merge against it would refuse
   the whole use case. It adds no trust: an unchecked library is already
   trusted whole, declarations and all, and the merge still runs the full
   comparison on the declarations it carries and still records the universe
   equalities it uses. *)
let merge env mp univs mb =
  if not (enabled ())
  then (env, Univ.UnivConstraints.empty, mb) else
  let new_dp = ModPath.dp mp in
  let () = library_univs := DirPath.Map.add new_dp univs !library_univs in
  match fields_of_body mb with
  | None -> (env, Univ.UnivConstraints.empty, mb)
  | Some struc ->
    let gsub = !global_subst in
    let news =
      List.filter_map
        (function (l, SFBmind mib) -> Some (l, mib) | _ -> None) struc
    in
    let reso = ref (Mod_subst.empty_delta_resolver mp) in
    let envr = ref env in
    let merged_count = ref 0 in
    (* Every equality an accepted merge rested on. The typing of what this
       library writes out may depend on them, and the names alone do not
       record them, so they go into the library's own constraints. *)
    let used_eqs = ref Univ.UnivConstraints.empty in
    let pending = ref [] in
    let try_block (l, mib) =
      let kn = KerName.make mp l in
      let key = shape_key (as_loaded mib) in
      let rec first = function
        | [] -> None
        | cand :: rest ->
          let ckn = MutInd.canonical cand in
          (* The library whose constraints must be compared is the one that
             DECLARED the candidate, which is its user name's: a candidate
             that was itself merged carries another library's canonical half
             (review finding P1-2). *)
          let cand_dp = ModPath.dp (KerName.modpath (MutInd.user cand)) in
          if not (Id.equal (KerName.label kn) (KerName.label ckn)) then first rest
          else match DirPath.Map.find_opt cand_dp !library_univs with
            | None -> first rest
            | Some old_ctx ->
              let trial = Mod_subst.add_kn_delta_resolver kn ckn !reso in
              let subst = Mod_subst.add_mp mp mp trial gsub in
              let mib' = as_loaded (Declareops.subst_mind_body subst mib) in
              let cmib = Environ.lookup_mind cand !envr in
              (* Defence in depth, and today it cannot fire: [mergeable]
                 has already refused a private block on the loading side,
                 and [eq_mib] refuses a private candidate against the
                 non-private newcomer that is all that reaches here. It
                 states the rule the other two only imply -- a private
                 block never merges, whichever side it is on -- so that
                 weakening either of them cannot quietly allow one. *)
              if not (Option.is_empty cmib.mind_private) then first rest else
              (match eq_mib empty_umap !envr mib' cmib with
               | Error _ -> first rest
               | Ok umap ->
                 let pairs = umap_pairs umap in
                 if not (pairs_admissible ~new_dp ~cand_dp pairs) then first rest
                 else if not (constraints_agree ~new_ctx:univs ~old_ctx pairs)
                 then first rest
                 else if List.is_empty pairs
                 then Some (cand, trial, !envr, Univ.UnivConstraints.empty)
                 else
                   let eqs =
                     List.fold_left (fun acc (a, b) ->
                         Univ.UnivConstraints.add (a, Univ.UnivConstraint.Eq, b) acc)
                       Univ.UnivConstraints.empty pairs
                   in
                   (* Adding the equalities is the step that can fail. A
                      refusal here is a refusal to merge, not an error. *)
                   match
                     Environ.push_context_set ~strict:true
                       (Univ.Level.Set.empty, eqs) !envr
                   with
                   | env' -> Some (cand, trial, env', eqs)
                   | exception UGraph.UniverseInconsistency _ -> first rest)
      in
      match (if mergeable mib then first (index_find key) else None) with
      | Some (cand, trial, env', eqs) ->
        reso := trial;
        envr := env';
        used_eqs := Univ.UnivConstraints.union eqs !used_eqs;
        incr merged_count;
        record_merge kn (MutInd.canonical cand);
        if verbose () then
          Feedback.msg_notice
            Pp.(str "Merged inductive " ++ KerName.print kn ++ str " with "
                ++ MutInd.print cand);
        pending := (key, MutInd.make kn (MutInd.canonical cand)) :: !pending
      | None -> pending := (key, MutInd.make1 kn) :: !pending
    in
    List.iter try_block news;
    List.iter (fun (key, mind) -> index_add key mind) !pending;
    let subst =
      if Int.equal !merged_count 0 then gsub
      else begin
        global_subst := Mod_subst.add_mp mp mp !reso gsub;
        !global_subst
      end
    in
    let mb =
      if Mod_subst.is_empty_subst subst then mb
      else Mod_declarations.subst_module Mod_declarations.subst_codom subst mp mb
    in
    (* The structure now names the merged inductives, so the resolver the
       environment keys its entries with has to agree: [Modops.add_structure]
       reads it to build each entry's name, and [Typeops] refuses any term
       whose canonical half differs from the one the entry records. *)
    let mb =
      if Int.equal !merged_count 0 then mb
      else
        Mod_declarations.set_delta
          (Mod_subst.add_delta_resolver !reso (Mod_declarations.mod_delta mb)) mb
    in
    (!envr, !used_eqs, mb)
