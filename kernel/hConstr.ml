(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Context

(** Provide caching and hashconsing dependent on the local context used by a term.

    We want to cache the results of typechecking a term (at constant
    global environment).

    To do this, we need a map [constr -> result of typechecking], and

    - it must distinguish alpha equal terms (to get the desired names
      in the result of checking "fun x:nat => eq_refl x" and
      "fun y:nat => eq_refl y").

    - it must distinguish terms which only differ in "cached" data
      like relevance marks (if we typecheck "fun x :(*Relevant*) nat => x",
      cache the result then check "fun x :(*Irrelevant*) nat => x" we must fail).

    - actually the map should be [(rel_context * constr) -> result] as
      the result of checking a bound variable depends on the context.

      To be more precise we only need to depend on the minimal context
      needed for the term, ie the context filtered to only the
      variables which appear in the term and recursively in the types
      and bodies of needed variables.

      Also note that we don't care about the names of local variables
      here, they only appear in error messages and since we stop at
      the first error there is no caching issue.

      (NB we need bodies as while the result of checking [Rel 1] does
      not depend on the body of rel 1, checking [eq_refl (Rel 1) : Rel 1 = 0]
      does need the body.)

    - the map should be fast.

    The first 2 points just mean we need a sufficiently precise equality test.

    To distinguish terms according to their context, we annotate each
    [Rel] subterm with their corresponding (recursively annotated)
    binder (ignoring the name).

    In practice we have an indirection such that each annotated binder
    is associated with a unique [int]. It's not clear how useful this
    is vs annotating with the actual binder data but it does allow
    handling unknow binders by just generating a fresh int (cf [push_unknown_rel]).

    While annotating [Rel]s we also share identical (for our equality)
    subterms and annotate each subterm with its hash, ie we hashcons
    according to our finer-than-[Constr.equal] equality. This means we
    can lookup by hash, and since identical subterms are shared we can
    compare them by [(==)] (in practice [hasheq_kind] which does
    [(==)] on immediate subterms) instead of structural equality
    (which would be O(size of term)).

    Finally we keep a reference count so that we can avoid caching
    subterms which aren't repeated.
*)

module Self = struct

type t = {
  self : constr;
  kind : (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term;
  isRel : int (* 0 -> not a rel, otherwise unique identifier of that binder *);
  hash : int;
  mutable refcount : int;
}

(* XXX possibly should be just physical equality since we use
   [raw_equal] on not-yet-hashconsed terms *)
let equal a b =
  a.isRel == b.isRel
  && hasheq_kind a.kind b.kind

let hash x = x.hash

end

include Self

let raw_equal a ~isRel ~kind =
  a.isRel == isRel
  && hasheq_kind a.kind kind

let self x = x.self

let refcount x = x.refcount

module Tbl = struct
  type key = t

  (* The API looks like Hashtbl, but a table maps each [hash] to the list of
     every binding whose key has that hash, newest first, and a lookup scans
     that list for the first binding whose key passes a predicate. [raw_find]
     lets [of_constr] look up a term that is not hashconsed yet (and a leaf
     before its subterms are converted) by its hash and a predicate.

     Upstream kept this map in an [Int.Map.t ref]: it measured that a balanced
     tree beat [Hashtbl] on an artificial example (a balanced binary tree of
     distinct primitive ints, with no sharing), and was a bit slower in the
     real world. On a whole-tree coqchk run the tree walk ([Int.find_opt]) and
     the path copy of every [add] ([Map.bal], [update]) cost 218 of the 610
     CPU-seconds of [of_constr], plus the minor GC that promotes the copies.

     So the map is an open-addressing table with linear probing: two arrays
     indexed by slot, one with the hash and one with that hash's list. The
     list [[]] marks a free slot, as no hash in the table has an empty list.
     Slot [i] of a hash is the top bits of that hash times an odd constant
     (Fibonacci hashing), so every bit of the hash moves the slot.

     A walk of more than a slot or two means hashes that share a home slot,
     and the multiplier is invertible: a term can carry hashes chosen so that
     every one of them has the same home at every size the table takes, and
     then each insertion and each lookup walks the whole cluster. The hash of
     a primitive integer literal is the literal plus 126 ([hash_kind] below,
     [Uint63.hash], [Hashset.Combine.combinesmall]), so a .v file can hold
     them; the cross-family review of speed-6 measured 65,536 such hashes at
     4.62 s against 0.095 s for the tree this table replaced, 48.6 times
     (dispatch://BET-241).

     So a probe walks a hash's home slot and at most [max_probe] slots after
     it, and a hash with no free slot among them is kept in [spill], an
     [Int.Map] of the same lists, where a lookup costs what the tree cost.
     The array keeps the cost of every hash a term gives it in the ordinary
     way, and no input makes a lookup walk further than the bound. Termination
     is the bound's, not the load factor's: [grow] puts spilled hashes back
     into the array, so more than half of the slots can be in use.

     The lists, their order and the predicates are the ones the [Int.Map]
     held, so every lookup returns the binding it returned: the slot only
     decides where a hash's list is kept, never which list or binding a
     lookup finds. *)
  type 'a t = {
    mutable slot_hashes : int array;
    mutable slot_bindings : (key * 'a) list array;
    (* [Sys.int_size] minus log2 of the number of slots *)
    mutable shift : int;
    (* slots whose list is not empty *)
    mutable used : int;
    (* the lists of the hashes the array has no room for, by hash *)
    mutable spill : (key * 'a) list Int.Map.t;
  }

  let initial_bits = 3

  let create () =
    let n = 1 lsl initial_bits in
    { slot_hashes = Array.make n 0; slot_bindings = Array.make n [];
      shift = Sys.int_size - initial_bits; used = 0; spill = Int.Map.empty }

  (* 2^63 divided by the golden ratio, rounded to odd. [Int64.to_int] takes it
     modulo the width of an [int], which keeps it odd. *)
  let golden = Int64.to_int 0x4F1BBCDCBFA53E0BL

  let home shift h = (h * golden) lsr shift

  (* How many slots after a hash's home a probe walks before it gives the hash
     to [spill]. With the hashes a term gives the table this is rare but not
     unheard of: measured with [Set Debug "hconstr"] on six stdlib files, 0 to 3
     hashes of between 4,579 and 119,022 spilled, about one in 84,000, and each
     of those pays the tree's cost for its own lookups and nothing more. With
     hashes chosen to share a home, all but [max_probe] + 1 of them spill,
     which is the point. *)
  let max_probe = 16

  (* The slot that holds hash [h], the free slot where it would go, or -1 when
     neither is its home or one of the [max_probe] slots after it. *)
  let rec probe hashes bindings mask h i fuel =
    match Array.unsafe_get bindings i with
    | [] -> i
    | _ :: _ ->
      if Int.equal (Array.unsafe_get hashes i) h then i
      else if Int.equal fuel 0 then -1
      else probe hashes bindings mask h ((i + 1) land mask) (fuel - 1)

  let slot tbl h =
    let bindings = tbl.slot_bindings in
    probe tbl.slot_hashes bindings (Array.length bindings - 1) h
      (home tbl.shift h) max_probe

  let spilled_bindings tbl h = Option.default [] (Int.Map.find_opt h tbl.spill)

  (* The list of hash [h], empty when the table has none. *)
  let bindings_of tbl h =
    let i = slot tbl h in
    if i < 0 then spilled_bindings tbl h
    else Array.unsafe_get tbl.slot_bindings i

  (* Growing re-inserts the spilled hashes as well: once the slots move, a hash
     that had no free slot within the bound may have one, and a lookup that
     meets a free slot within the bound concludes the hash is not in the table.
     So a hash sits outside the array only while its home has no free slot
     within [max_probe] slots, which is what makes that conclusion sound. *)
  let grow tbl =
    let old_hashes = tbl.slot_hashes and old_bindings = tbl.slot_bindings in
    let old_spill = tbl.spill in
    let n = 2 * Array.length old_bindings in
    let shift = tbl.shift - 1 in
    let hashes = Array.make n 0 and bindings = Array.make n [] in
    let used = ref 0 in
    let spill = ref Int.Map.empty in
    let insert h l =
      let j = probe hashes bindings (n - 1) h (home shift h) max_probe in
      if j < 0 then spill := Int.Map.add h l !spill
      else begin
        hashes.(j) <- h;
        bindings.(j) <- l;
        incr used
      end
    in
    Array.iteri (fun i l -> match l with
        | [] -> ()
        | _ :: _ -> insert old_hashes.(i) l)
      old_bindings;
    Int.Map.iter insert old_spill;
    tbl.slot_hashes <- hashes;
    tbl.slot_bindings <- bindings;
    tbl.shift <- shift;
    tbl.used <- !used;
    tbl.spill <- !spill

  let add tbl key v =
    let h = key.hash in
    let i = slot tbl h in
    if i < 0 then
      tbl.spill <- Int.Map.update h (function
          | None -> Some [(key, v)]
          | Some l -> Some ((key, v) :: l))
          tbl.spill
    else match tbl.slot_bindings.(i) with
    | [] ->
      tbl.slot_hashes.(i) <- h;
      tbl.slot_bindings.(i) <- [(key,v)];
      tbl.used <- tbl.used + 1;
      if 2 * tbl.used > Array.length tbl.slot_bindings then grow tbl
    | l -> tbl.slot_bindings.(i) <- (key,v) :: l

  let raw_find tbl h p =
    match bindings_of tbl h with
    | [] -> None
    | l -> List.find_map (fun (k,v) -> if p k then Some v else None) l

  let find_opt tbl key =
    match bindings_of tbl key.hash with
    | [] -> None
    | l ->
      List.find_map (fun (k',v) ->
          if equal key k' then Some v else None)
        l

  type stats = {
    hashes : int;
    bindings : int;
    most_collisions : int;
    (* hashes kept outside the array *)
    spilled : int;
  }

  let empty_stats = {
    hashes = 0;
    bindings = 0;
    most_collisions = 0;
    spilled = 0;
  }

  let count_list acc l =
    let len = List.length l in
    {
      acc with
      hashes = acc.hashes + 1;
      bindings = acc.bindings + len;
      most_collisions = max acc.most_collisions len;
    }

  let stats tbl =
    let acc =
      Array.fold_left (fun acc l ->
          match l with
          | [] -> acc
          | _ :: _ -> count_list acc l)
        empty_stats
        tbl.slot_bindings
    in
    Int.Map.fold (fun _ l acc -> { (count_list acc l) with spilled = acc.spilled + 1 })
      tbl.spill acc

end

type henv = {
  (* only used for globals, rel context is not correct *)
  globals : Environ.env;
  (* table of reified terms *)
  tbl : t Tbl.t;
  (* debug counter *)
  steps : int ref;
  (* unique identifiers for each binder crossed *)
  rels : int Range.t;
  (* counter to generate uids for binders *)
  binder_cnt : int ref;
  (* how many unknown_rel we have seen *)
  unknown_cnt : int ref;
  assum_uids : int Tbl.t;
  (* the surrounding table is for the body, the inner table for the type *)
  letin_uids : int Tbl.t Tbl.t;
}

let empty_env env = {
  globals = env;
  tbl = Tbl.create ();
  steps = ref 0;
  rels = Range.empty;
  binder_cnt = ref 0;
  unknown_cnt = ref 0;
  assum_uids = Tbl.create ();
  letin_uids = Tbl.create ();
}

(* still used in fixpoint *)
let push_unknown_rel env =
  incr env.binder_cnt;
  incr env.unknown_cnt;
  { env with rels = Range.cons !(env.binder_cnt) env.rels }

let push_assum t env =
  let uid = match Tbl.find_opt env.assum_uids t with
  | Some uid -> uid
  | None ->
    incr env.binder_cnt;
    let uid = !(env.binder_cnt) in
    Tbl.add env.assum_uids t uid;
    uid
  in
  { env with rels = Range.cons uid env.rels }

let push_rec ts env =
  (* handling the lifting for mutual fixpoints doesn't seem worth the effort *)
  Array.fold_left_i (fun i env t ->
      if i = 0 then push_assum t env
      else push_unknown_rel env)
    env
    ts

let push_letin ~body ~typ env =
  let uid = match Tbl.find_opt env.letin_uids body with
    | Some tbl -> begin match Tbl.find_opt tbl typ with
        | Some uid -> uid
        | None ->
          incr env.binder_cnt;
          let uid = !(env.binder_cnt) in
          Tbl.add tbl typ uid;
          uid
      end
    | None ->
      incr env.binder_cnt;
      let uid = !(env.binder_cnt) in
      let tbl = Tbl.create () in
      Tbl.add tbl typ uid;
      Tbl.add env.letin_uids body tbl;
      uid
  in
  { env with rels = Range.cons uid env.rels }

module RelDecl = Context.Rel.Declaration

let push_decl d env = match d with
  | RelDecl.LocalAssum (_,t) -> push_assum t env
  | RelDecl.LocalDef (_,body,typ) -> push_letin ~body ~typ env

let hash_annot = hash_annot Name.hash

let hash_array hashf a = Array.fold_left (fun hash x -> Hashset.Combine.combine hash (hashf x)) 0 a

let hash_kind = let open Hashset.Combine in function
  | Var i -> combinesmall 1 (Id.hash i)
  | Sort s -> combinesmall 2 (Sorts.hash s)
  | Cast (c,k,t) -> combinesmall 3 (combine3 c.hash (hash_cast_kind k) t.hash)
  | Prod (na,t,c) -> combinesmall 4 (combine3 (hash_annot na) t.hash c.hash)
  | Lambda (na,t,c) -> combinesmall 5 (combine3 (hash_annot na) t.hash c.hash)
  | LetIn (na,b,t,c) -> combinesmall 6 (combine4 (hash_annot na) b.hash t.hash c.hash)
  | App (h,args) -> combinesmall 7 (Array.fold_left (fun hash c -> combine hash c.hash) h.hash args)
  | Evar _ -> assert false
  | Const (c,u) -> combinesmall 9 (combine (Constant.UserOrd.hash c) (UVars.Instance.hash u))
  | Ind (ind,u) -> combinesmall 10 (combine (Ind.UserOrd.hash ind) (UVars.Instance.hash u))
  | Construct (c,u) -> combinesmall 11 (combine (Construct.UserOrd.hash c) (UVars.Instance.hash u))
  | Case (_,u,pms,(p,_),_,c,bl) ->
    let hash_ctx (bnd,c) =
      Array.fold_left (fun hash na -> combine (hash_annot na) hash) c.hash bnd
    in
    let hpms = hash_array hash pms in
    let hbl = hash_array hash_ctx bl in
    let h = combine5 (UVars.Instance.hash u)
        c.hash hpms (hash_ctx p) hbl
    in
    combinesmall 12 h
  | Fix (_,(lna,tl,bl)) ->
    combinesmall 13 (combine3 (hash_array hash_annot lna) (hash_array hash tl) (hash_array hash bl))
  | CoFix (_,(lna,tl,bl)) ->
    combinesmall 14 (combine3 (hash_array hash_annot lna) (hash_array hash tl) (hash_array hash bl))
  | Meta _ -> assert false
  | Rel n -> combinesmall 16 n
  | Proj (p,_,c) -> combinesmall 17 (combine (Projection.UserOrd.hash p) c.hash)
  | Int i -> combinesmall 18 (Uint63.hash i)
  | Float f -> combinesmall 19 (Float64.hash f)
  | String s -> combinesmall 20 (Pstring.hash s)
  | Array (u,t,def,ty) -> combinesmall 21 (combine4 (UVars.Instance.hash u) (hash_array hash t) def.hash ty.hash)

let kind_to_constr = function
  | Rel n -> mkRel n
  | Var i -> mkVar i
  | Meta _ | Evar _ -> assert false
  | Sort s -> mkSort s
  | Cast (c,k,t) -> mkCast (c.self,k,t.self)
  | Prod (na,t,c) -> mkProd (na,t.self,c.self)
  | Lambda (na,t,c) -> mkLambda (na,t.self,c.self)
  | LetIn (na,b,t,c) -> mkLetIn (na,b.self,t.self,c.self)
  | App (h,args) -> mkApp (h.self, Array.map self args)
  | Const cu -> mkConstU cu
  | Ind iu -> mkIndU iu
  | Construct cu -> mkConstructU cu
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    let to_ctx (bnd,c) = bnd, c.self in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert x -> CaseInvert {indices=Array.map self x.indices}
    in
    mkCase (ci,u,Array.map self pms,(to_ctx p,r),iv,c.self,Array.map to_ctx bl)
  | Fix (ln,(lna,tl,bl)) ->
    mkFix (ln,(lna,Array.map self tl,Array.map self bl))
  | CoFix (ln,(lna,tl,bl)) ->
    mkCoFix (ln,(lna,Array.map self tl,Array.map self bl))
  | Proj (p,r,c) -> mkProj (p,r,c.self)
  | Int i -> mkInt i
  | Float f -> mkFloat f
  | String s -> mkString s
  | Array (u,t,def,ty) -> mkArray (u,Array.map self t,def.self,ty.self)

let of_kind_nohashcons = function
  | App (c, [||]) -> c
  | kind ->
  let self = kind_to_constr kind in
  let hash = hash_kind kind in
  let () = match kind with
    | Rel _ -> assert false
    | _ -> ()
  in
  { self; kind; hash; isRel = 0; refcount = 1 }

let eq_leaf c c' = match kind c, c'.kind with
  | Var i, Var i' -> Id.equal i i'
  | Const (c,u), Const (c',u') -> Constant.UserOrd.equal c c' && UVars.Instance.equal u u'
  | Ind (i,u), Ind (i',u') -> Ind.UserOrd.equal i i' && UVars.Instance.equal u u'
  | Construct (c,u), Construct (c',u') -> Construct.UserOrd.equal c c' && UVars.Instance.equal u u'
  | _ -> false

let nonrel_leaf tbl c = match kind c with
  | Rel _ -> None
  | Var _ | Const _ | Ind _ | Construct _ as k ->
    let h = hash_kind k in
    Tbl.raw_find tbl h (fun c' -> eq_leaf c c')
  | _ -> None

let rec of_constr henv c =
  incr henv.steps;
  match nonrel_leaf henv.tbl c with
  | Some v -> v
  | None ->
    let kind = of_constr_aux henv c in
    let hash = hash_kind kind in
    let isRel, hash = match kind with
      | Rel n ->
        let uid = Range.get henv.rels (n-1) in
        assert (uid <> 0);
        uid, Hashset.Combine.combine uid hash
      | _ -> 0, hash
    in
    match Tbl.raw_find henv.tbl hash (fun c' -> raw_equal c' ~isRel ~kind) with
    | Some c' -> c'.refcount <- c'.refcount + 1; c'
    | None ->
      let c =
        let self = kind_to_constr kind in
        let self = if hasheq_kind (Constr.kind self) (Constr.kind c) then c else self in
        { self; kind; hash; isRel; refcount = 1 }
      in
    Tbl.add henv.tbl c c; c

and of_constr_aux henv c =
  match kind c with
  | Var i ->
    let _, i = Id.hcons i in
    Var i
  | Rel _ as t -> t
  | Sort s ->
    let _, s = Sorts.hcons s in
    Sort s
  | Cast (c,k,t) ->
    let c = of_constr henv c in
    let t = of_constr henv t in
    Cast (c, k, t)
  | Prod (na,t,c) ->
    let _, na = hcons_annot na in
    let t = of_constr henv t in
    let c = of_constr (push_assum t henv) c in
    Prod (na, t, c)
  | Lambda (na, t, c) ->
    let _, na = hcons_annot na in
    let t = of_constr henv t in
    let c = of_constr (push_assum t henv) c in
    Lambda (na,t,c)
  | LetIn (na,b,t,c) ->
    let _, na = hcons_annot na in
    let b = of_constr henv b in
    let t = of_constr henv t in
    let c = of_constr (push_letin ~body:b ~typ:t henv) c in
    LetIn (na,b,t,c)
  | App (h,args) ->
    let h = of_constr henv h in
    let args = Array.map (of_constr henv) args in
    App (h, args)
  | Evar _ -> CErrors.anomaly Pp.(str "evar in typeops")
  | Meta _ -> CErrors.anomaly Pp.(str "meta in typeops")
  | Const (c,u) ->
    let _, c = hcons_con c in
    let _, u = UVars.Instance.hcons u in
    Const (c,u)
  | Ind (ind,u) ->
    let _, ind = hcons_ind ind in
    let _, u = UVars.Instance.hcons u in
    Ind (ind,u)
  | Construct (c,u) ->
    let _, c = hcons_construct c in
    let _, u = UVars.Instance.hcons u in
    Construct (c,u)
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    let pctx, blctx =
      let specif = Inductive.lookup_mind_specif henv.globals ci.ci_ind in
      let pctx = Inductive.expand_arity specif (ci.ci_ind,u) pms (fst p) in
      let blctx = Inductive.expand_branch_contexts specif u pms bl in
      pctx, blctx
    in
    let of_ctx (bnd, c) bnd' =
      let _, bnd = Hashcons.hashcons_array hcons_annot bnd in
      let henv = push_rel_context henv bnd' in
      let c = of_constr henv c in
      bnd, c
    in
    let _, ci = hcons_caseinfo ci in
    let _, u = UVars.Instance.hcons u in
    let pms = Array.map (of_constr henv) pms in
    let p = of_ctx p pctx in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert {indices} -> CaseInvert {indices=Array.map (of_constr henv) indices}
    in
    let c = of_constr henv c in
    let bl = Array.map2 of_ctx bl blctx in
    Case (ci,u,pms,(p,r),iv,c,bl)
  | Fix (ln,(lna,tl,bl)) ->
    let _, lna = Hashcons.hashcons_array hcons_annot lna in
    let tl = Array.map (of_constr henv) tl in
    let body_env = push_rec tl henv in
    let bl = Array.map (of_constr body_env) bl in
    Fix (ln,(lna,tl,bl))
  | CoFix (ln,(lna,tl,bl)) ->
    let _, lna = Hashcons.hashcons_array hcons_annot lna in
    let tl = Array.map (of_constr henv) tl in
    let body_env = push_rec tl henv in
    let bl = Array.map (of_constr body_env) bl in
    CoFix (ln,(lna,tl,bl))
  | Proj (p,r,c) ->
    let _, p = Projection.hcons p in
    let c = of_constr henv c in
    Proj (p,r,c)
  | Int _ as t -> t
  | Float _ as t -> t
  | String _ as t -> t
  | Array (u,t,def,ty) ->
    let _, u = UVars.Instance.hcons u in
    let t = Array.map (of_constr henv) t in
    let def = of_constr henv def in
    let ty = of_constr henv ty in
    Array (u,t,def,ty)

and push_rel_context henv ctx =
  List.fold_right (fun d henv ->
      let d = RelDecl.map_constr_het (fun r -> r) (of_constr henv) d in
      push_decl d henv)
    ctx
    henv

let dbg = CDebug.create ~name:"hconstr" ()

let tree_size c =
  let rec aux size c =
    Constr.fold aux (size+1) c
  in
  aux 0 c

let of_constr env c =
  let henv = empty_env env in
  let henv = iterate push_unknown_rel (Environ.nb_rel env) henv in
  let c = NewProfile.profile "HConstr.of_constr" (fun () -> of_constr henv c) () in
  dbg Pp.(fun () ->
      let stats = Tbl.stats henv.tbl in
      let tree_size = tree_size (self c) in
      v 0 (
        str "steps = " ++ int !(henv.steps) ++ spc() ++
        str "rel cnt = " ++ int !(henv.binder_cnt) ++ spc() ++
        str "unknwown rels = " ++ int !(henv.unknown_cnt) ++ spc() ++
        str "hashes = " ++ int stats.Tbl.hashes ++ spc() ++
        str "bindings = " ++ int stats.Tbl.bindings ++ spc() ++
        str "tree size = " ++ int tree_size ++ spc() ++
        str "most_collisions = " ++ int stats.Tbl.most_collisions ++ spc() ++
        str "spilled = " ++ int stats.Tbl.spilled
    )
    );
  c

let kind x = x.kind

let hcons x =
  let tbl = Tbl.create () in
  let module HCons = GenHCons(struct
      type nonrec t = t
      let kind = kind
      let self = self
      let refcount = refcount
        let via_hconstr = true
      module Tbl = struct
        let find_opt x = Tbl.find_opt tbl x
        let add x y = Tbl.add tbl x y
      end
    end) in
  HCons.hcons x
