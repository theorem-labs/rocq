(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The following definitions are used by the function
   [assumptions] which gives as an output the set of all
   axioms and sections variables on which a given term depends
   in a context (expectingly the Global context) *)

(* Initial author: Arnaud Spiwack
   Module-traversing code: Pierre Letouzey *)

open Util
open Names
open Declarations
open Mod_declarations

module NamedDecl = Context.Named.Declaration

(** For a constant c in a module sealed by an interface (M:T and
    not M<:T), [Global.lookup_constant] may return a [constant_body]
    without body. We fix this by looking in the implementation
    of the module *)

let modcache = ref (ModPath.Map.empty : structure_body ModPath.Map.t)

let rec search_mod_label lab = function
  | [] -> raise Not_found
  | (l, SFBmodule mb) :: _ when Id.equal l lab -> mb
  | _ :: fields -> search_mod_label lab fields

let rec search_cst_label lab = function
  | [] -> raise Not_found
  | (l, SFBconst cb) :: _ when Id.equal l lab -> cb
  | _ :: fields -> search_cst_label lab fields

let rec search_mind_label lab = function
  | [] -> raise Not_found
  | (l, SFBmind mind) :: _ when Id.equal l lab -> mind
  | _ :: fields -> search_mind_label lab fields

(* TODO: using [empty_delta_resolver] below is probably slightly incorrect. But:
    a) I don't see currently what should be used instead
    b) this shouldn't be critical for Print Assumption. At worse some
       constants will have a canonical name which is non-canonical,
       leading to failures in [Global.lookup_constant], but our own
       [lookup_constant] should work.
*)

let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid,_,e) ->
    let open Mod_subst in
    match args with
    | [] -> assert false (* we should only encounter applied functors *)
    | mpa :: args ->
      let subs = join (map_mbid mbid mpa (empty_delta_resolver mpa) (*TODO*)) subs in
      fields_of_functor f subs mp0 args e

let rec lookup_module_in_impl mp =
    match mp with
    | MPfile _ -> Global.lookup_module mp
    | MPbound _ -> Global.lookup_module mp
    | MPdot (mp',lab') ->
       if ModPath.equal mp' (Global.current_modpath ()) then
         Global.lookup_module mp
       else
         let fields = memoize_fields_of_mp mp' in
         search_mod_label lab' fields

and memoize_fields_of_mp mp =
  try ModPath.Map.find mp !modcache
  with Not_found ->
    let l = fields_of_mp mp in
    modcache := ModPath.Map.add mp l !modcache;
    l

and fields_of_mp mp =
  let open Mod_subst in
  let mb = lookup_module_in_impl mp in
  let fields,inner_mp,subs = fields_of_mb empty_subst mp mb [] in
  let delta_mb = mod_delta mb in
  let subs =
    (* XXX this code makes little sense, adding a delta_mb to subs if the root
       does not coincide with mp used to be equivalent to a no-op and now fails
       with an assertion failure. More likely than not, this means that we have
       no idea about what we are doing. *)
    if ModPath.equal inner_mp mp then subs
    else if has_root_delta_resolver mp delta_mb then
      add_mp inner_mp mp delta_mb subs
    else
      add_mp inner_mp mp (empty_delta_resolver mp) subs
  in
  Modops.subst_structure subs mp fields

and fields_of_mb subs mp mb args = match Mod_declarations.mod_expr mb with
  | Algebraic expr -> fields_of_expression subs mp args (mod_type mb) expr
  | Struct (_, sign) ->
    let sign = Modops.annotate_struct_body sign (mod_type mb) in
    fields_of_signature subs mp args sign
  | Abstract|FullStruct -> fields_of_signature subs mp args (mod_type mb)

(** The Abstract case above corresponds to [Declare Module] *)

and fields_of_signature x =
  fields_of_functor
    (fun subs mp0 args struc ->
      assert (List.is_empty args);
      (struc, mp0, subs)) x

and fields_of_expr subs mp0 args = function
  | MEident mp ->
    let mp = Mod_subst.subst_mp subs mp in
    let mb = lookup_module_in_impl mp in
    fields_of_mb subs mp mb args
  | MEapply (me1,mp2) -> fields_of_expr subs mp0 (mp2::args) me1
  | MEwith _ -> assert false (* no 'with' in [mod_expr] *)

and fields_of_expression subs mp args mty me =
  let me = Modops.annotate_module_expression me mty in
  fields_of_functor fields_of_expr subs mp args me

let lookup_constant_in_impl cst fallback =
  try
    let mp,lab = KerName.repr (Constant.canonical cst) in
    let fields = memoize_fields_of_mp mp in
    (* A module found this way is necessarily closed, in particular
       our constant cannot be in an opened section : *)
    search_cst_label lab fields
  with Not_found ->
    (* Either:
       - The module part of the constant isn't registered yet :
         we're still in it, so the [constant_body] found earlier
         (if any) was a true axiom.
       - The label has not been found in the structure. This is an error *)
    match fallback with
      | Some cb -> cb
      | None ->
        CErrors.anomaly
          Pp.(str "Print Assumption: unknown constant "
            ++ Constant.print cst ++ str ".")

let lookup_constant cst =
  let env = Global.env() in
  if not (Environ.mem_constant cst env)
  then lookup_constant_in_impl cst None
  else
    let cb = Environ.lookup_constant cst env in
    if Declareops.constant_has_body cb then cb
    else lookup_constant_in_impl cst (Some cb)

let lookup_mind_in_impl mind =
  try
    let mp,lab = KerName.repr (MutInd.canonical mind) in
    let fields = memoize_fields_of_mp mp in
      search_mind_label lab fields
  with Not_found ->
    CErrors.anomaly
      Pp.(str "Print Assumption: unknown inductive "
        ++ MutInd.print mind ++ str ".")

let lookup_mind mind =
  let env = Global.env() in
  if Environ.mem_mind mind env then Environ.lookup_mind mind env
  else lookup_mind_in_impl mind

(** Graph traversal of an object, collecting on the way the dependencies of
    traversed objects *)

let fold_with_full_binders g f n acc c =
  let open Context.Rel.Declaration in
  let open Constr in
  match kind c with
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _  | Int _ | Float _ | String _ -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_,_,c) -> f n acc c
  | Evar _ -> assert false
  | Case (ci, u, pms, p, iv, c, bl) ->
    let mib = lookup_mind (fst ci.ci_ind) in
    let (ci, (p,_), iv, c, bl) = Inductive.expand_case_specif mib (ci, u, pms, p, iv, c, bl) in
    Array.fold_left (f n) (f n (fold_invert (f n) (f n acc p) iv) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | Array(_u,t,def,ty) -> f n (f n (Array.fold_left (f n) acc t) def) ty

(** Reuse of traversals across queries.

    A query walks the body and type of every object it reaches. A file that
    runs many queries in one environment (one per lemma, say) walks the same
    objects again and again, so the walk of an object is recorded and later
    queries replay it.

    Soundness invariant: for every object [o] and environment [E], the entry
    for [o] under [E] is the pair of stock's [data] value for [o] and the edge
    set of [o]:
    - for an object with a body, its direct references (its value's set);
    - for an axiom, the direct references of its type, which stock walks but
      does not keep;
    - for a member of a mutual block, the block's direct references plus
      every inductive and constructor of the block.
    An object is never recorded when its walk, including every walk nested in
    it, records an empty-match context in [ax2ty] or meets an opaque body that
    cannot be forced; a member of a mutual block is recorded only together
    with its whole block. It is also recorded only once each of its edges has
    an entry, since a replay that reaches an object without one is abandoned.

    Replaying [o] writes [o]'s value into the query's [data], then replays
    each edge, stopping at objects already in [data] as stock does. A replay
    either completes, adding exactly the keys and values stock's walk of [o]
    adds from the same [data] (the closure of [o] through edges, avoiding what
    [data] holds, whatever the query visited first), or reaches an object
    without an entry and is abandoned, keeping nothing, and [o] is walked the
    stock way. A recorded object's walk never touches [ax2ty]. So every
    query's final [data] and [ax2ty] equal stock's, by induction over the
    traversal order, and so does the output of {!assumptions}, a fold over
    them.

    Entries hold for one environment, compared by physical equality of
    [Global.env ()], plus the current module path (it decides how constants of
    sealed modules are looked up, see [lookup_module_in_impl]) and the
    opaque-proof accessor. Any difference clears every entry. *)

let debug_memo = CDebug.create ~name:"assumptions-memo" ()

type memo_entry = {
  memo_obj : GlobRef.t;
  memo_value : GlobRef.Set_env.t option;
  memo_edges : GlobRef.Set_env.t;
}

let memo_key : (Environ.env * ModPath.t * Global.indirect_accessor) option ref = ref None

let memo_entries = ref (GlobRef.Map_env.empty : memo_entry GlobRef.Map_env.t)

(** Counts the traversal steps whose effect depends on the query rather than
    on the object walked: an empty-match context recorded in [ax2ty], and an
    opaque body that cannot be forced. A walk during which it changes is not
    recorded. *)
let query_dependent = ref 0

let sync_memo access =
  let env = Global.env () in
  let mp = Global.current_modpath () in
  match !memo_key with
  | Some (env', mp', access') when env' == env && ModPath.equal mp' mp && access' == access -> ()
  | _ ->
    memo_key := Some (env, mp, access);
    memo_entries := GlobRef.Map_env.empty

(* [Map_env] compares user names only: the entry is [obj]'s when the
   canonical names agree too. *)
let find_entry obj =
  match GlobRef.Map_env.find_opt obj !memo_entries with
  | Some e when GlobRef.CanOrd.equal e.memo_obj obj -> Some e
  | _ -> None

let has_entry obj = Option.has_some (find_entry obj)

let add_entry value edges obj =
  let e = { memo_obj = obj; memo_value = value; memo_edges = edges } in
  memo_entries := GlobRef.Map_env.add obj e !memo_entries

let record_block mind mib contents =
  let members = Array.fold_left_i (fun n members oib ->
      let ind = (mind, n) in
      Array.fold_left_i (fun k members _ ->
          GlobRef.Set_env.add (GlobRef.ConstructRef (ind, k+1)) members)
        (GlobRef.Set_env.add (GlobRef.IndRef ind) members) oib.mind_consnames)
      GlobRef.Set_env.empty mib.mind_packets
  in
  let cached r = GlobRef.Set_env.mem r members || has_entry r in
  if GlobRef.Set_env.for_all cached contents then
    let edges = GlobRef.Set_env.union contents members in
    GlobRef.Set_env.iter (add_entry (Some contents) edges) members

exception Miss

(* [data0] is the query's [data] before the replay. An object in it is
   skipped, as stock skips it. Every other object reached needs an entry for
   that very object, canonical name included, even when this replay already
   added an object with the same user name: so the objects a completed replay
   reaches outside [data0] have one canonical name per user name, and the
   order in which it reaches them cannot matter. *)
let rec replay_into data0 obj data =
  if GlobRef.Map_env.mem obj data0 then data
  else match find_entry obj with
  | None -> raise Miss
  | Some e ->
    if GlobRef.Map_env.mem obj data then data
    else
      GlobRef.Set_env.fold (replay_into data0) e.memo_edges
        (GlobRef.Map_env.add obj e.memo_value data)

(** [Some data'] when every object the replay reaches has an entry, where
    [data'] is [data] plus the closure of [obj] with stock's values; [None]
    otherwise. *)
let replay obj data =
  match replay_into data obj data with
  | data ->
    debug_memo Pp.(fun () -> str "replayed " ++ GlobRef.print obj);
    Some data
  | exception Miss -> None

let get_constant_body access kn =
  let cb = lookup_constant kn in
  match cb.const_body with
  | Undef _ | Primitive _ | Symbol _ -> None
  | Def c -> Some c
  | OpaqueDef o ->
    match Global.force_proof access o with
    | c, _ -> Some c
    | exception e when CErrors.noncritical e ->
      (* missing delayed body, e.g. in vok mode *)
      incr query_dependent;
      None

let rec traverse access (current:GlobRef.t) ctx accu t =
  let open GlobRef in
  let open Constr in
  match Constr.kind t with
| Var id ->
  let body () = id |> Global.lookup_named |> NamedDecl.get_value in
  traverse_object access accu body (VarRef id)
| Const (kn, _) ->
  let body () = get_constant_body access kn in
  traverse_object access accu body (ConstRef kn)
| Ind ((mind, _) as ind, _) ->
  traverse_inductive access accu mind (IndRef ind)
| Construct (((mind, _), _) as cst, _) ->
  traverse_inductive access accu mind (ConstructRef cst)
| Meta _ | Evar _ -> assert false
| Case (_, _, _, (([|_|], oty),_), _, c, [||]) when Vars.noccurn 1 oty ->
    (* non dependent match on an inductive with no constructors *)
    begin match Constr.kind c with
    | Const (kn, _) when not (Declareops.constant_has_body (lookup_constant kn)) ->
      let () = incr query_dependent in
      let (curr, data, ax2ty) = accu in
      let obj = ConstRef kn in
      let already_in = GlobRef.Map_env.mem obj data in
      let data = if not already_in then GlobRef.Map_env.add obj None data else data in
      let ty = (current, ctx, Vars.subst1 mkProp oty) in
      let ax2ty =
        try let l = GlobRef.Map_env.find obj ax2ty in GlobRef.Map_env.add obj (ty::l) ax2ty
        with Not_found -> GlobRef.Map_env.add obj [ty] ax2ty in
      (GlobRef.Set_env.add obj curr, data, ax2ty)
    | _ ->
        fold_with_full_binders
          Context.Rel.add (traverse access current) ctx accu t
    end
| _ -> fold_with_full_binders
          Context.Rel.add (traverse access current) ctx accu t

and traverse_object access (curr, data, ax2ty) body obj =
  let data, ax2ty =
    let already_in = GlobRef.Map_env.mem obj data in
    if already_in then data, ax2ty
    else match replay obj data with
    | Some data -> data, ax2ty
    | None -> walk_object access data ax2ty body obj
  in
  (GlobRef.Set_env.add obj curr, data, ax2ty)

and walk_object access data ax2ty body obj =
  let mark = !query_dependent in
  let value, edges, data, ax2ty =
    match body () (* Beware: this can be very costly *) with
    | None ->
      (* This is an axiom. Always traverse its type to find dependencies *)
      let data = GlobRef.Map_env.add obj None data in
      begin match obj with
      | GlobRef.ConstRef kn ->
        let cb = lookup_constant kn in
        let typ = cb.Declarations.const_type in
        let type_refs, data, ax2ty =
          traverse access obj Context.Rel.empty
                   (GlobRef.Set_env.empty, data, ax2ty) typ in
        None, type_refs, data, ax2ty
      (* VarRef, IndRef and ConstructRef don't need recursive type traversal.
         For VarRef (section variables), the dependencies are already tracked.
         For IndRef and ConstructRef, dependencies are handled by traverse_inductive *)
      | GlobRef.VarRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _ ->
        None, GlobRef.Set_env.empty, data, ax2ty end
    | Some body ->
      let contents,data,ax2ty =
        traverse access obj Context.Rel.empty
                 (GlobRef.Set_env.empty,data,ax2ty) body in
      (* Also traverse the type of globals, which may mention unrelated
         references depending on axioms even if they convert to something else. *)
      let contents,data,ax2ty = match obj with
        | GlobRef.ConstRef kn ->
          let cb = lookup_constant kn in
          let typ = cb.Declarations.const_type in
          traverse access obj Context.Rel.empty
                   (contents,data,ax2ty) typ
        | _ -> (contents,data,ax2ty)
      in
      Some contents, contents, GlobRef.Map_env.add obj (Some contents) data, ax2ty
  in
  let () =
    if Int.equal mark !query_dependent && GlobRef.Set_env.for_all has_entry edges
    then add_entry value edges obj
  in
  data, ax2ty

(** Collects the references occurring in the declaration of mutual inductive
    definitions. All the constructors and names of a mutual inductive
    definition share exactly the same dependencies. Also, there is no explicit
    dependency between mutually defined inductives and constructors. *)
and traverse_inductive access (curr, data, ax2ty) mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  let data, ax2ty =
   (* Invariant : I_0 \in data iff I_i \in data iff c_ij \in data
      where I_0, I_1, ... are in the same mutual definition and c_ij
      are all their constructors. *)
   if
     (* recursive call: *) GlobRef.Set_env.mem firstind_ref curr ||
     (* already in: *) GlobRef.Map_env.mem firstind_ref data
   then data, ax2ty
   else match replay obj data with
   | Some data -> data, ax2ty
   | None -> walk_inductive access data ax2ty mind obj
  in
  (GlobRef.Set_env.add obj curr, data, ax2ty)

and walk_inductive access data ax2ty mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  let mark = !query_dependent in
  (* Take into account potential recursivity of ind in itself *)
  let curr = GlobRef.Set_env.add firstind_ref GlobRef.Set_env.empty in
  let accu = (curr, data, ax2ty) in
  let mib = lookup_mind mind in
  (* Collects references of parameters *)
  let param_ctx = mib.mind_params_ctxt in
  let nparam = List.length param_ctx in
  let accu = traverse_context access obj Context.Rel.empty accu param_ctx in
  (* For each inductive, collects references in their arity and in the type
     of constructors*)
  let (contents, data, ax2ty) = Array.fold_left (fun accu oib ->
      let arity_wo_param =
        List.rev (List.skipn nparam (List.rev oib.mind_arity_ctxt))
      in
      let accu =
        traverse_context
          access obj param_ctx accu arity_wo_param
      in
      Array.fold_left (fun accu cst_typ ->
         let param_ctx, cst_typ_wo_param = Term.decompose_prod_n_decls nparam cst_typ in
         traverse access obj param_ctx accu cst_typ_wo_param)
        accu oib.mind_user_lc)
    accu mib.mind_packets
  in
  (* Maps all these dependencies to inductives and constructors*)
  let contents = GlobRef.Set_env.remove firstind_ref contents in
  let data =
    Array.fold_left_i (fun n data oib ->
    let ind = (mind, n) in
    let data = GlobRef.Map_env.add (GlobRef.IndRef ind) (Some contents) data in
    Array.fold_left_i (fun k data _ ->
      GlobRef.Map_env.add (GlobRef.ConstructRef (ind, k+1)) (Some contents) data
    ) data oib.mind_consnames) data mib.mind_packets
  in
  let () = if Int.equal mark !query_dependent then record_block mind mib contents in
  (data, ax2ty)

(** Collects references in a rel_context. *)
and traverse_context access current ctx accu ctxt =
  snd (Context.Rel.fold_outside (fun decl (ctx, accu) ->
    match decl with
     | Context.Rel.Declaration.LocalDef (_,c,t) ->
          let accu = traverse access current ctx (traverse access current ctx accu t) c in
          let ctx = Context.Rel.add decl ctx in
          ctx, accu
     | Context.Rel.Declaration.LocalAssum (_,t) ->
          let accu = traverse access current ctx accu t in
          let ctx = Context.Rel.add decl ctx in
           ctx, accu) ctxt ~init:(ctx, accu))

let traverse access grs =
  let () = modcache := ModPath.Map.empty in
  let () = sync_memo access in
  let env = Global.env () in
  List.fold_left (fun accu gr ->
    let t, _ = UnivGen.fresh_global_instance env gr in
    traverse access gr Context.Rel.empty accu t
  ) (GlobRef.Set_env.empty, GlobRef.Map_env.empty, GlobRef.Map_env.empty) grs

(** Hopefully bullet-proof function to recover the type of a constant. It just
    ignores all the universe stuff. There are many issues that can arise when
    considering terms out of any valid environment, so use with caution. *)
let type_of_constant cb = cb.Declarations.const_type

let uses_uip mib =
  Array.exists (fun mip ->
      Option.is_empty mip.mind_squashed
      && mip.mind_relevance == Sorts.Irrelevant
      && Array.length mip.mind_nf_lc = 1
      && List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt)
    mib.mind_packets

let assumptions ?(add_opaque=false) ?(add_transparent=false) access st grs =
  let open Printer in
  (* Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse access grs in
  let open GlobRef in
  let has_impredicative_set = ref false in
  let has_rewrite_rules = ref false in
  let has_type_in_type = ref false in
  let has_unchecked_eliminations = ref false in
  let collect_theory_flags (tf : Declarations.typing_flags) =
    if tf.impredicative_set then has_impredicative_set := true;
    if not tf.check_universes then has_type_in_type := true;
    if not tf.check_eliminations then has_unchecked_eliminations := true
  in
  let fold obj contents accu = match obj with
  | VarRef id ->
    let decl = Global.lookup_named id in
    if Context.Named.Declaration.is_local_assum decl then
      let t = Context.Named.Declaration.get_type decl in
      ContextObjectMap.add (Variable id) t accu
    else accu
  | ConstRef kn ->
      let cb = lookup_constant kn in
      collect_theory_flags cb.const_typing_flags;
      begin match cb.const_body with
        | Symbol _ -> has_rewrite_rules := true
        | _ -> ()
      end;
      let accu =
        if cb.const_typing_flags.check_guarded then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded obj, l)) Constr.mkProp accu
      in
      let accu =
        if cb.const_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
      let accu =
        if cb.const_typing_flags.check_eliminations then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (UncheckedEliminations obj, l)) Constr.mkProp accu
      in
    if not (Option.has_some contents) then
      let t = type_of_constant cb in
      let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
      ContextObjectMap.add (Axiom (Constant kn,l)) t accu
    else if add_opaque && (Declareops.is_opaque cb || not (Structures.PrimitiveProjections.is_transparent_constant st kn)) then
      let t = type_of_constant cb in
      ContextObjectMap.add (Opaque kn) t accu
    else if add_transparent then
      let t = type_of_constant cb in
      ContextObjectMap.add (Transparent kn) t accu
    else
      accu
  | IndRef (m,_) | ConstructRef ((m,_),_) ->
      let mind = lookup_mind m in
      collect_theory_flags mind.mind_typing_flags;
      let accu =
        if mind.mind_typing_flags.check_positive then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Positive m, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_guarded then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded obj, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_eliminations then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (UncheckedEliminations obj, l)) Constr.mkProp accu
      in
      let accu =
        if not (uses_uip mind) then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (UIP m, l)) Constr.mkProp accu
      in
      let accu =
        if not (Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mind.mind_packets) then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (IndicesNotMattering m, l)) Constr.mkProp accu
      in
      accu
  in
  let map = GlobRef.Map_env.fold fold graph ContextObjectMap.empty in
  let theory = {
    has_impredicative_set = !has_impredicative_set;
    has_rewrite_rules = !has_rewrite_rules;
    has_type_in_type = !has_type_in_type;
    has_unchecked_eliminations = !has_unchecked_eliminations;
  } in
  (theory, map)
