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

module NamedDecl = Context.Named.Declaration

(** For a constant c in a module sealed by an interface (M:T and
    not M<:T), [Global.lookup_constant] may return a [constant_body]
    without body. We fix this by looking in the implementation
    of the module *)

let modcache = ref (MPmap.empty : structure_body MPmap.t)

let rec search_mod_label lab = function
  | [] -> raise Not_found
  | (l, SFBmodule mb) :: _ when Label.equal l lab -> mb
  | _ :: fields -> search_mod_label lab fields

let rec search_cst_label lab = function
  | [] -> raise Not_found
  | (l, SFBconst cb) :: _ when Label.equal l lab -> cb
  | _ :: fields -> search_cst_label lab fields

let rec search_mind_label lab = function
  | [] -> raise Not_found
  | (l, SFBmind mind) :: _ when Label.equal l lab -> mind
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
      let subs = join (map_mbid mbid mpa empty_delta_resolver (*TODO*)) subs in
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
  try MPmap.find mp !modcache
  with Not_found ->
    let l = fields_of_mp mp in
    modcache := MPmap.add mp l !modcache;
    l

and fields_of_mp mp =
  let open Mod_subst in
  let mb = lookup_module_in_impl mp in
  let fields,inner_mp,subs = fields_of_mb empty_subst mb [] in
  let subs =
    if ModPath.equal inner_mp mp then subs
    else add_mp inner_mp mp mb.mod_delta subs
  in
  Modops.subst_structure subs fields

and fields_of_mb subs mb args = match Declareops.mod_expr mb with
  | Algebraic expr -> fields_of_expression subs mb.mod_mp args mb.mod_type expr
  | Struct sign ->
    let sign = Modops.annotate_struct_body sign mb.mod_type in
    fields_of_signature subs mb.mod_mp args sign
  | Abstract|FullStruct -> fields_of_signature subs mb.mod_mp args mb.mod_type

(** The Abstract case above corresponds to [Declare Module] *)

and fields_of_signature x =
  fields_of_functor
    (fun subs mp0 args struc ->
      assert (List.is_empty args);
      (struc, mp0, subs)) x

and fields_of_expr subs mp0 args = function
  | MEident mp ->
    let mb = lookup_module_in_impl (Mod_subst.subst_mp subs mp) in
    fields_of_mb subs mb args
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

let label_of = let open GlobRef in function
  | ConstRef kn -> Constant.label kn
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> MutInd.label kn
  | VarRef id -> Label.of_id id

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

(** Reuse of traversals across queries (port of the theorem-labs/rocq
    Print Assumptions cache, sami/print-assumptions-memo at 3cb8d4d0b, to
    V9.0.1).

    A query walks the body of every object it reaches. A file that runs many
    queries in one environment walks the same objects again and again, so the
    walk of an object is recorded and later queries replay it.

    In V9.0.1 the walk reads no type: a constant without a body (axiom,
    parameter, primitive, symbol, [Admitted] lemma) and a section variable
    are added to [data] with the value [None] and nothing else is visited,
    and a constant with a body is walked through its body only. (Walking
    types came with upstream 693577ea94, first released in V9.2; the fork's
    replay of types, [Type_of], [fold_refs_of_type] and [WalkedTerm], exists
    for that walk and has no counterpart here.)

    Soundness invariant: for every object [o] and environment [E], the entry
    for [o] under [E] is the pair of the [data] value the walk gives [o] and
    the edge set of [o]:
    - for an object with a body, its direct references (its value's set, the
      very set [data] holds);
    - for an object without a body, the empty set;
    - for a member of a mutual block, the block's direct references plus
      every inductive and constructor of the block.
    An object is never recorded when its walk, including every walk nested in
    it, records an empty-match context in [ax2ty] or meets an opaque body that
    cannot be forced (an entry stores no [ax2ty]; excluding the second is a
    precaution that only costs reuse). A member of a mutual block is recorded
    only together with its whole block. An object is also recorded only once
    each of its edges has an entry, and only while no entry has its user name.
    Entries are never replaced, so every edge of every entry keeps an entry
    until the entries are cleared, and a replay can miss only at the object it
    starts from.

    Replaying [o] writes [o]'s value into the query's [data], then replays
    each edge, stopping at objects already in [data] as the walk does. A
    replay either completes, adding exactly the keys and values the walk of
    [o] adds from the same [data], or reaches an object without an entry and
    is abandoned, keeping nothing, and [o] is walked. So every query's final
    [data] and [ax2ty] equal those of the walk without reuse, and so does the
    output of {!assumptions}, a fold over them.

    Entries hold for one environment, compared by physical equality of
    [Global.env ()], plus the current module path, the opaque-proof accessor,
    and the generation of the opaque tables of loaded libraries
    ([Library.opaque_tables_generation]). Those tables are not part of the
    environment: a Require that fails, because the file it finds holds another
    library, replaces the opaque proofs of that library when it is loaded, and
    leaves [Global.env ()] as it was. Any difference clears every entry. The
    entries are also cleared, at the start of a query, when they weigh more
    than [memo_factor] times the heaviest query so far in the environment (an
    entry weighs one plus the size of its edge set; a block's set counts
    once). *)

(* ROCQ_DEBUG_ASSUMPTIONS_MEMO=1, read once at startup, reports each completed
   replay, and each clearing of the entries by the weight bound, on standard
   error. *)
let debug_memo = Sys.getenv_opt "ROCQ_DEBUG_ASSUMPTIONS_MEMO" = Some "1"

type memo_entry = {
  memo_obj : GlobRef.t;
  memo_value : GlobRef.Set_env.t option;
  memo_edges : GlobRef.Set_env.t;
  memo_size : int;  (** the cardinal of [memo_edges] *)
}

let memo_key : (Environ.env * ModPath.t * Global.indirect_accessor * int) option ref = ref None

let memo_factor = 2

(** The entries and their weight, in one immutable value that is assigned
    once per update: an interrupted update leaves both as they were. *)
type memo = {
  entries : memo_entry GlobRef.Map_env.t;
  weight : int;
}

let fresh_memo () = { entries = GlobRef.Map_env.empty; weight = 0 }

let memo = ref (fresh_memo ())

(** The weight of the heaviest query in the environment before the current
    one, and of the current query. They only decide when the entries are
    cleared. *)
let memo_heaviest = ref 0
let query_weight = ref 0

(** Counts the traversal steps an entry cannot reproduce: an empty-match
    context recorded in [ax2ty], and an opaque body that cannot be forced. A
    walk during which it changes is not recorded. *)
let unreplayable_steps = ref 0

(** [!unreplayable_steps] at the start of each [walk_inductive] in progress,
    innermost first, kept on the heap rather than in the walk's frame. *)
let inductive_marks = ref ([] : int list)

let sync_memo access =
  let env = Global.env () in
  let mp = Global.current_modpath () in
  let opaques = Library.opaque_tables_generation () in
  match !memo_key with
  | Some (env', mp', access', opaques') when
      env' == env && ModPath.equal mp' mp && access' == access && Int.equal opaques' opaques ->
    memo_heaviest := max !memo_heaviest !query_weight;
    query_weight := 0;
    if !memo.weight > memo_factor * !memo_heaviest then begin
      memo := fresh_memo ();
      if debug_memo then Printf.eprintf "[assumptions-memo] cleared\n%!"
    end
  | _ ->
    memo := fresh_memo ();
    memo_heaviest := 0;
    query_weight := 0;
    memo_key := Some (env, mp, access, opaques)

(* [Map_env] compares user names only: the entry is [obj]'s when the
   canonical names agree too. *)
let find_entry obj =
  match GlobRef.Map_env.find_opt obj !memo.entries with
  | Some e when GlobRef.CanOrd.equal e.memo_obj obj -> Some e
  | _ -> None

let has_entry obj = Option.has_some (find_entry obj)

(* An object whose user name already has an entry, under another canonical
   name, is not recorded: entries are never replaced until the environment
   changes. Unlike [has_entry], this compares user names only. *)
let user_name_unrecorded obj = not (GlobRef.Map_env.mem obj !memo.entries)

let[@inline never] make_entry value edges obj =
  { memo_obj = obj; memo_value = value; memo_edges = edges;
    memo_size = GlobRef.Set_env.cardinal edges }

let[@inline always] add_entry value edges obj =
  let e = make_entry value edges obj in
  let weight = 1 + e.memo_size in
  query_weight := !query_weight + weight;
  let m = !memo in
  memo := { entries = GlobRef.Map_env.add obj e m.entries; weight = m.weight + weight }

let[@inline never] edges_have_entries edges = GlobRef.Set_env.for_all has_entry edges

(* The members are added to a new map, which is assigned once, with the
   weight: a block recorded in part would keep its other members from ever
   being recorded. *)
let record_block mind mib contents =
  let members = Array.fold_left_i (fun n members oib ->
      let ind = (mind, n) in
      Array.fold_left_i (fun k members _ ->
          GlobRef.Set_env.add (GlobRef.ConstructRef (ind, k+1)) members)
        (GlobRef.Set_env.add (GlobRef.IndRef ind) members) oib.mind_consnames)
      GlobRef.Set_env.empty mib.mind_packets
  in
  let cached r = GlobRef.Set_env.mem r members || has_entry r in
  if GlobRef.Set_env.for_all user_name_unrecorded members
     && GlobRef.Set_env.for_all cached contents then
    let edges = GlobRef.Set_env.union contents members in
    let size = GlobRef.Set_env.cardinal edges in
    let weight = GlobRef.Set_env.cardinal members + size in
    query_weight := !query_weight + weight;
    let m = !memo in
    let entries = GlobRef.Set_env.fold (fun obj entries ->
        let e = { memo_obj = obj; memo_value = Some contents; memo_edges = edges; memo_size = size } in
        GlobRef.Map_env.add obj e entries) members m.entries
    in
    memo := { entries; weight = m.weight + weight }

exception Miss

(** The weight of the replay in progress. *)
let replay_weight = ref 0

(* [data0] is the query's [data] before the replay. An object in it is
   skipped, as the walk skips it. Every other object reached needs an entry
   for that very object, canonical name included. The objects still to visit
   are kept in a list rather than on the stack. The members of a mutual block
   share one edge set, which holds every member: it is pushed once per
   replay ([pushed]). *)
let replay_into data0 obj data =
  let rec loop pushed data = function
    | [] -> data
    | obj :: todo ->
      if GlobRef.Map_env.mem obj data0 then loop pushed data todo
      else match find_entry obj with
      | None -> raise Miss
      | Some e ->
        if GlobRef.Map_env.mem obj data then loop pushed data todo
        else
          let () = incr replay_weight in
          let data = GlobRef.Map_env.add obj e.memo_value data in
          let block = match obj with
            | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> Some mind
            | GlobRef.VarRef _ | GlobRef.ConstRef _ -> None
          in
          match block with
          | Some mind when Mindmap_env.Set.mem mind pushed -> loop pushed data todo
          | _ ->
            let pushed = match block with
              | Some mind -> Mindmap_env.Set.add mind pushed
              | None -> pushed
            in
            let () = replay_weight := !replay_weight + e.memo_size in
            loop pushed data (GlobRef.Set_env.fold (fun r todo -> r :: todo) e.memo_edges todo)
  in
  loop Mindmap_env.Set.empty data [obj]

(** [Some data'] when every object the replay reaches outside [data] has an
    entry, where [data'] is [data] plus the closure of [obj], stopping at
    objects already in [data], with the values the walk would add; [None]
    otherwise. *)
let replay obj data =
  let () = replay_weight := 0 in
  match replay_into data obj data with
  | data ->
    query_weight := !query_weight + !replay_weight;
    if debug_memo then
      Printf.eprintf "[assumptions-memo] replayed %s\n%!"
        (Pp.string_of_ppcmds (Pp.h (GlobRef.print obj)));
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
      incr unreplayable_steps;
      None

let rec traverse access current ctx accu t =
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
      let () = incr unreplayable_steps in
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

(* [walk_object] and [walk_inductive] are entered by tail calls: a walk holds
   one frame per object, as it would without reuse. *)
and traverse_object access (curr, data, ax2ty) body obj =
  let curr = GlobRef.Set_env.add obj curr in
  if GlobRef.Map_env.mem obj data then (curr, data, ax2ty)
  else match replay obj data with
  | Some data -> (curr, data, ax2ty)
  | None -> (walk_object [@ocaml.tailcall]) access curr data ax2ty body obj

and walk_object access curr data ax2ty body obj =
  let mark = !unreplayable_steps in
  let value, edges, data, ax2ty =
    match body () (* Beware: this can be very costly *) with
    | None ->
      None, GlobRef.Set_env.empty, GlobRef.Map_env.add obj None data, ax2ty
    | Some body ->
      let contents,data,ax2ty =
        traverse access (label_of obj) Context.Rel.empty
                 (GlobRef.Set_env.empty,data,ax2ty) body in
      Some contents, contents, GlobRef.Map_env.add obj (Some contents) data, ax2ty
  in
  let () =
    if Int.equal mark !unreplayable_steps && user_name_unrecorded obj
       && edges_have_entries edges
    then add_entry value edges obj
  in
  (curr, data, ax2ty)

(** Collects the references occurring in the declaration of mutual inductive
    definitions. All the constructors and names of a mutual inductive
    definition share exactly the same dependencies. Also, there is no explicit
    dependency between mutually defined inductives and constructors. *)
and traverse_inductive access (curr, data, ax2ty) mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  (* Invariant : I_0 \in data iff I_i \in data iff c_ij \in data
     where I_0, I_1, ... are in the same mutual definition and c_ij
     are all their constructors. *)
  let recursive = GlobRef.Set_env.mem firstind_ref curr in
  let curr = GlobRef.Set_env.add obj curr in
  if
    (* recursive call: *) recursive ||
    (* already in: *) GlobRef.Map_env.mem firstind_ref data
  then (curr, data, ax2ty)
  else match replay obj data with
  | Some data -> (curr, data, ax2ty)
  | None -> (walk_inductive [@ocaml.tailcall]) access curr data ax2ty mind obj

and walk_inductive access curr data ax2ty mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  let label = label_of obj in
  let () = inductive_marks := !unreplayable_steps :: !inductive_marks in
  (* Take into account potential recursivity of ind in itself *)
  let accu = (GlobRef.Set_env.add firstind_ref GlobRef.Set_env.empty, data, ax2ty) in
  let mib = lookup_mind mind in
  (* Collects references of parameters *)
  let param_ctx = mib.mind_params_ctxt in
  let nparam = List.length param_ctx in
  let accu = traverse_context access label Context.Rel.empty accu param_ctx in
  (* For each inductive, collects references in their arity and in the type
     of constructors*)
  let (contents, data, ax2ty) = Array.fold_left (fun accu oib ->
      let arity_wo_param =
        List.rev (List.skipn nparam (List.rev oib.mind_arity_ctxt))
      in
      let accu =
        traverse_context
          access label param_ctx accu arity_wo_param
      in
      Array.fold_left (fun accu cst_typ ->
         let param_ctx, cst_typ_wo_param = Term.decompose_prod_n_decls nparam cst_typ in
         traverse access label param_ctx accu cst_typ_wo_param)
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
  let mark = match !inductive_marks with
    | mark :: marks -> inductive_marks := marks; mark
    | [] -> assert false
  in
  let () = if Int.equal mark !unreplayable_steps then record_block mind mib contents in
  (curr, data, ax2ty)

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

let traverse access current t =
  let () = modcache := MPmap.empty in
  let () = inductive_marks := [] in
  let () = sync_memo access in
  traverse access current Context.Rel.empty (GlobRef.Set_env.empty, GlobRef.Map_env.empty, GlobRef.Map_env.empty) t

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

let assumptions ?(add_opaque=false) ?(add_transparent=false) access st gr t =
  let open Printer in
  (* Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse access (label_of gr) t in
  let open GlobRef in
  let fold obj contents accu = match obj with
  | VarRef id ->
    let decl = Global.lookup_named id in
    if Context.Named.Declaration.is_local_assum decl then
      let t = Context.Named.Declaration.get_type decl in
      ContextObjectMap.add (Variable id) t accu
    else accu
  | ConstRef kn ->
      let cb = lookup_constant kn in
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
        if not (uses_uip mind) then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (UIP m, l)) Constr.mkProp accu
      in
      accu
  in GlobRef.Map_env.fold fold graph ContextObjectMap.empty
