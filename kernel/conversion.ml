(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created under Benjamin Werner account by Bruno Barras to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Irreversibility of opacity by Bruno Barras *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Equal inductive types by Jacek Chrzaszcz as part of the module
   system, Aug 2002 *)

open CErrors
open Util
open Names
open Constr
open Declarations
open Environ
open CClosure
open Esubst

let rec is_empty_stack = function
  [] -> true
  | Zupdate _::s -> is_empty_stack s
  | Zshift _::s -> is_empty_stack s
  | _ -> false

(* Compute the lift to be performed on a term placed in a given stack *)
let el_stack el stk =
  let n =
    List.fold_left
      (fun i z ->
        match z with
            Zshift n -> i+n
          | _ -> i)
      0
      stk in
  el_shft n el

let compare_stack_shape stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> Int.equal bal 0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zproj _::s1, Zproj _::s2) ->
        Int.equal bal 0 && compare_rec 0 s1 s2
    | (ZcaseT(_c1,_,_,_,_,_)::s1, ZcaseT(_c2,_,_,_,_,_)::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | Zprimitive(op1,_,rargs1, _kargs1)::s1, Zprimitive(op2,_,rargs2, _kargs2)::s2 ->
        bal=0 && op1=op2 && List.length rargs1=List.length rargs2 &&
        compare_rec 0 s1 s2
    | [], _ :: _
    | (Zproj _ | ZcaseT _ | Zfix _ | Zprimitive _) :: _, _ -> false
  in
  compare_rec 0 stk1 stk2

type lft_fconstr = lift * fconstr

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlproj of Projection.Repr.t * lift
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * UVars.Instance.t * constr array * case_return * case_branch array * usubs
  | Zlprimitive of
     CPrimitives.t * pconstant * lft_fconstr list * lft_fconstr next_native_args
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation. Type annotation is required to tell OCaml that the array does
    not contain floats. *)
let map_lift (l : lift) (v : fconstr array) = match v with
| [||] -> assert false
| [|c0|] -> [|(l, c0)|]
| [|c0; c1|] -> [|(l, c0); (l, c1)|]
| [|c0; c1; c2|] -> [|(l, c0); (l, c1); (l, c2)|]
| [|c0; c1; c2; c3|] -> [|(l, c0); (l, c1); (l, c2); (l, c3)|]
| v -> Array.Fun1.map (fun l t -> (l, t)) l v

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (map_lift l a) pstk)
            | (Zproj (p,_), (l,pstk)) ->
                (l, Zlproj (p,l)::pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (ZcaseT(ci,u,pms,p,br,e),(l,pstk)) ->
                (l,Zlcase(ci,l,u,pms,p,br,e)::pstk)
            | (Zprimitive(op,c,rargs,kargs),(l,pstk)) ->
                (l,Zlprimitive(op,c,List.map (fun t -> (l,t)) rargs,
                            List.map (fun (k,t) -> (k,(l,t))) kargs)::pstk))
  in
  snd (pure_rec lfts stk)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)

(* functions of this type are called from the kernel *)
type 'a kernel_conversion_function = env -> 'a -> 'a -> (unit, unit) result

(* functions of this type can be called from outside the kernel *)
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:TransparentState.t -> env ->
  ?evars:evar_handler ->
  'a -> 'a -> (unit, unit) result

type payload = ..

exception NotConvertible
exception NotConvertibleTrace of payload

(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb =
  | CONV
  | CUMUL

type ('a, 'err) universe_compare = {
  compare_sorts : conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
  compare_cumul_instances : conv_pb -> UVars.variances ->
    UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare

type ('a, 'err) generic_conversion_function = ('a, 'err) universe_state -> constr -> constr -> ('a, 'err option) result

let sort_cmp_universes pb s0 s1 (u, check) =
  (check.compare_sorts pb s0 s1 u, check)

(* [flex] should be true for constants, false for inductive types and
   constructors. *)
let convert_instances ~flex u u' (s, check) =
  (check.compare_instances ~flex u u' s, check)

exception MustExpand

let convert_instances_cumul pb var u u' (s, check) =
  (check.compare_cumul_instances pb var u u' s, check)

let get_cumulativity_constraints cv_pb variance u u' =
  match cv_pb with
  | CONV ->
    UVars.enforce_eq_variance_instances variance u u' UVars.empty_unif_constraints
  | CUMUL ->
    UVars.enforce_leq_variance_instances variance u u' UVars.empty_unif_constraints

let inductive_cumulativity_arguments (mind,ind) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs

let convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,ind) nargs u1 u2 s =
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some variances ->
    let num_param_arity = inductive_cumulativity_arguments (mind,ind) in
    if not (Int.equal num_param_arity nargs) then
      (* shortcut, not sure if worth doing, could use perf data *)
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      cmp_cumul cv_pb variances u1 u2 s

(* Conversion result cache. Within one top-level conv/conv_leq call the same
   pair of closures is often compared many times, because beta-substitution
   shares payload cells across every occurrence of a bound variable: the
   reduction machine has no memory of this and re-derives each
   convertibility subproblem from scratch. A per-session (i.e. per-call)
   table maps a pair of cell ids (CClosure.get_fid), together with the
   exact pair of lifts applied to each side and the conversion problem
   kind (CONV/CUMUL), to the outcome.

   Only sound for CHECKED conversion ([gen_conv], used by the kernel's own
   re-verification in Typeops/Safe_typing -- the same kernel code coqc and
   coqchk both link against unmodified): that path is a deterministic
   function of a FIXED environment and universe graph, and accumulates no
   universe constraints to replay. Never enabled for the tactic engine's
   inference-mode conversion ([generic_conv]), which backtracks and
   discards constraints.

   The cache is created fresh for each top-level call (see
   [clos_gen_conv]) and discarded at the end of it: it never persists
   across declarations, across files, or across coqchk/coqc sessions, so
   it cannot leak a result computed against one environment/universe state
   into a check against a different one. It never reads
   Conv_oracle/Strategy/Opaque settings -- those influence only the
   reduction ORDER of the underlying complete decision procedure, never
   its outcome, so the cached boolean is still the answer an uncached
   comparison would reach regardless of Strategy. *)
module ConvCache = struct
  module Key = struct
    (* ids of the two cells, and whether the problem is cumulativity *)
    type t = int * int * bool
    let equal (u1, v1, b1) (u2, v2, b2) =
      Int.equal u1 u2 && Int.equal v1 v2 && Bool.equal b1 b2
    let hash (u, v, b) =
      let h = u * 0x3B9ACA07 + v in
      let h = h lxor (h lsr 16) in
      if b then h lxor 0x5BF03635 else h
  end
  module Tbl = Hashtbl.Make(Key)

  type t = {
    tbl : (lift * lift * bool) list ref Tbl.t;
    mutable size : int;
  }

  (* Diagnostic counters, process-lifetime (NOT per-cache, so they survive
     across the many short-lived per-call caches in one coqc/coqchk run):
     how many times a conv/conv_leq entry point consulted the cache, and
     how many of those probes were already recorded. Printed when
     ROCQ_CONV_CACHE_STATS=1, to measure the repeat rate on a real tree
     before committing to the full design. *)
  let probes = ref 0
  let hits = ref 0

  (* Optional cap on cached entries per session (ROCQ_CONV_CACHE_MAX; 0 or
     unset means unlimited: like the per-call [clos_tab]s, the table's
     lifetime already bounds its memory). *)
  let max_size =
    match int_of_string (Sys.getenv "ROCQ_CONV_CACHE_MAX") with
    | 0 -> max_int
    | n -> n
    | exception _ -> max_int

  (* Enabled by default; ROCQ_CONV_CACHE=0 disables it (e.g. for a coqchk
     invocation that must stay byte-for-byte on the stock decision path). *)
  let enabled =
    match Sys.getenv "ROCQ_CONV_CACHE" with
    | "0" -> false
    | _ -> true
    | exception Not_found -> true

  let create () = if enabled then Some { tbl = Tbl.create 16; size = 0 } else None

  let rec strip_flift k v = match fterm_of v with
    | FLIFT (n, v') -> strip_flift (k + n) v'
    | _ -> (k, v)

  (* [probe] and [record] renormalize the pair independently: nothing probe
     computes needs to stay live across the comparison run between the two
     calls. *)
  let probe cache ~cumul lft1 t1 lft2 t2 =
    incr probes;
    let (k1, v1) = strip_flift 0 t1 in
    let (k2, v2) = strip_flift 0 t2 in
    let l1 = el_shft k1 lft1 in
    let l2 = el_shft k2 lft2 in
    let key = (get_fid v1, get_fid v2, cumul) in
    match Tbl.find_opt cache.tbl key with
    | None -> None
    | Some entries ->
      let rec find = function
        | [] -> None
        | (l1', l2', r) :: rest ->
          if eq_lift l1' l1 && eq_lift l2' l2 then (incr hits; Some r)
          else find rest
      in
      find !entries

  let record cache ~cumul lft1 t1 lft2 t2 r =
    if cache.size < max_size then begin
      let (k1, v1) = strip_flift 0 t1 in
      let (k2, v2) = strip_flift 0 t2 in
      let l1 = el_shft k1 lft1 in
      let l2 = el_shft k2 lft2 in
      let key = (get_fid v1, get_fid v2, cumul) in
      cache.size <- cache.size + 1;
      match Tbl.find_opt cache.tbl key with
      | Some entries -> entries := (l1, l2, r) :: !entries
      | None -> Tbl.add cache.tbl key (ref [(l1, l2, r)])
    end

  let () =
    let want_stats =
      match Sys.getenv "ROCQ_CONV_CACHE_STATS" with
      | "1" -> true | _ -> false | exception Not_found -> false
    in
    if want_stats then at_exit (fun () ->
      Printf.eprintf "ROCQ_CONV_CACHE_STATS probes=%d hits=%d\n%!" !probes !hits)
end

(* Cross-declaration conversion cache COUNTING ONLY (binary-equivalence-taiga
   issue #874, version 3). This never changes any verdict and is not
   consulted by [ccnv]: it is a diagnostic side-table, hooked at the exact
   same point [ConvCache] probes (just above), that answers "how many of
   these conversion problems would a cache keyed on the closed term pair,
   surviving ACROSS top-level clos_gen_conv calls, have hit, and how many
   of those hits are safe to share" (closed term, no bound universe/quality
   variable, every constant already imported from a library other than the
   one currently being checked). Gated by ROCQ_CONV_XDECL_STATS=1; wired
   only into the checked-conversion path (see [cnv_xdecl] below), never
   into [generic_conv] or the [CClosure.set_conv] callback.

   Memory bound (binary-equivalence-taiga#874, the A6 OOM): the first cut
   of this counter keyed the table on the two full reified [Constr.t]
   terms, so every first-seen keyable probe permanently retained both
   whole term graphs for the rest of the process -- on A6's much larger
   tree that grows without bound and exhausted a 24G cap in under five
   minutes. This version keys on two independent structural hashes plus
   the term's node count instead ([HKey.t] below); a table entry is now a
   handful of fixed-size ints regardless of how big the compared terms
   are, so table memory is bounded by the number of *distinct* keyable
   pairs, not by their content. A reification is also capped at
   [max_nodes] nodes: a cheap pre-check walks the raw (unsubstituted)
   [fconstr] shape before calling [CClosure.to_constr] at all, so a term
   whose own surface already exceeds the cap is never reified; the
   post-reification hash/size walk re-checks the realized term as a
   backstop (substitution can expand a shared sub-closure past what the
   surface walk saw), discarding it as soon as it crosses the cap. That
   backstop still allocates the realized term before discarding it -- a
   one-shot, never-retained, GC-collectible spike, not the unbounded
   permanent retention the old version had. *)
module XDeclCache = struct
  let enabled =
    match Sys.getenv "ROCQ_CONV_XDECL_STATS" with
    | "1" -> true | _ -> false | exception Not_found -> false

  (* Node-count cap for both the fconstr surface pre-check and the
     post-reification backstop. Overridable for experiments; the default
     is generous enough to rarely trip on an ordinary compared subterm
     while still bounding the one-shot reification cost of a pathological
     giant term. *)
  let max_nodes =
    match Sys.getenv "ROCQ_CONV_XDECL_MAX_NODES" with
    | s -> (try int_of_string s with _ -> 100_000)
    | exception Not_found -> 100_000

  (* Last-resort safety valve, independent of [max_nodes]: that cap prices
     a term's own SURFACE shape (the compact, unsubstituted fconstr graph,
     or after reification its node count), but [CClosure.to_constr] can
     still expand a small-surface term combinatorially when a shared
     sub-closure is substituted into several places that are each
     themselves substituted again -- a real case hit on the A6 tree (a
     single declaration whose compared terms stayed under a 5,000-node
     surface cap still drove the process from ~5GB to past a 24G cap in
     the few probes between two 2,000,000-probe progress checkpoints).
     No per-term size check can see that coming since the blowup only
     exists in the fully-substituted form [to_constr] materializes. Once
     the live heap crosses [max_heap_words], every later probe is treated
     as unkeyable (reason [HeapGuard]) without attempting reification at
     all: the real conversion check this counter rides on is unaffected
     either way, so the diagnostic degrades instead of taking the host
     process down with it. *)
  let max_heap_words =
    match Sys.getenv "ROCQ_CONV_XDECL_MAX_HEAP_WORDS" with
    | s -> (try int_of_string s with _ -> 2_000_000_000)
    | exception Not_found -> 2_000_000_000
  let heap_guard_tripped = ref false
  let heap_guard_trips = ref 0
  let heap_guard_ok () =
    if !heap_guard_tripped then false
    else if (Gc.quick_stat ()).Gc.heap_words > max_heap_words then begin
      heap_guard_tripped := true;
      incr heap_guard_trips;
      false
    end else true

  (* One id per top-level clos_gen_conv call. A table entry remembers the
     call id it was first recorded under, so [record] can tell a same-call
     repeat (already ConvCache's own territory, within one declaration's
     check) from a cross-call repeat (what a process-lifetime cache would
     actually save). *)
  let call_id = ref 0
  let new_call () = incr call_id

  (* The library currently being checked (DirPath.t of the .vo file whose
     declarations are presently going through Mod_checking.check_module),
     and the set of libraries that finished being loaded (checked OR
     admitted) strictly before it. Set from checker/checkLibrary.ml. *)
  let current_library : DirPath.t option ref = ref None
  let imported : DirPath.Set.t ref = ref DirPath.Set.empty
  let set_current_library dp = current_library := Some dp
  let mark_library_done dp = imported := DirPath.Set.add dp !imported

  exception Not_shareable
  exception Over_cap

  (* Root DirPath.t of a ModPath.t, or None for a bound (functor-parameter)
     module path: that never denotes a sealed, already-imported library. *)
  let rec root_dirpath = function
    | ModPath.MPfile dp -> Some dp
    | ModPath.MPdot (mp, _) -> root_dirpath mp
    | ModPath.MPbound _ -> None

  (* Raises Not_shareable if [t] has a free Rel, a Var, a Meta or an Evar
     anywhere; otherwise returns every Const/Ind/Construct/Proj ModPath.t it
     mentions. Same [iter_with_binders]-based depth tracking as
     [Vars.closedn]. *)
  let scan t =
    let refs = ref [] in
    let rec walk depth c =
      (match kind c with
       | Rel m -> if m > depth then raise Not_shareable
       | Var _ | Meta _ | Evar _ -> raise Not_shareable
       | Const (cst, _) -> refs := Constant.modpath cst :: !refs
       | Ind (ind, _) -> refs := Ind.modpath ind :: !refs
       | Construct (ctor, _) -> refs := Construct.modpath ctor :: !refs
       | Proj (p, _, _) -> refs := MutInd.modpath (Projection.mind p) :: !refs
       | _ -> ());
      Constr.iter_with_binders succ walk depth c
    in
    walk 0 t;
    !refs

  let has_bound_univs t =
    let qs, us = Vars.sort_and_universes_of_constr t in
    Sorts.QVar.Set.exists (fun q -> Sorts.QVar.var_index q <> None) qs
    || Univ.Level.Set.exists (fun l -> Univ.Level.var_index l <> None) us

  (* Every mentioned name is rooted at a library other than the one
     currently being checked, and that library already finished loading. *)
  let refs_shareable refs =
    List.for_all (fun mp ->
        match root_dirpath mp with
        | None -> false
        | Some dp ->
          (match !current_library with
           | Some cur when DirPath.equal dp cur -> false
           | _ -> DirPath.Set.mem dp !imported))
      refs

  (* [to_constr] walks the WHOLE term, including subterms the comparison
     algorithm has not forced to whnf (ccnv only peeks at heads before
     recursing); on such an unforced closure it can hit an internal
     esubst.ml invariant (lift/subst depth) that only holds for the
     already-whnf-reduced forms [to_constr] is normally applied to
     elsewhere (kl/norm_head). This is a diagnostic side-table, never
     consulted by the real check, so it fails open: an unreifiable probe
     still counts toward [probes] but is excluded from repeat tracking,
     same as an open term or one with a bound universe variable. *)
  let safe_to_constr lft t =
    match CClosure.to_constr lft t with
    | v -> Some v
    | exception _ -> None

  (* Cheap node-count walk over a PLAIN [Constr.t], no hashing: used by the
     fconstr surface pre-check below to price embedded (not-yet-forced)
     subterms without materializing anything new. *)
  let rec constr_nodes_budget budget c =
    if budget <= 0 then raise Over_cap;
    Constr.fold constr_nodes_budget (budget - 1) c

  (* Surface node count of the raw, unsubstituted [fconstr] shape -- the
     same case split [CClosure.to_constr] uses, but counting instead of
     building, and never composing a substitution (an FCLOS/FLIFT/binder
     boundary is priced via the cheap embedded-Constr.t count above, not
     expanded). This can UNDERESTIMATE the fully-substituted size when a
     shared closure is referenced from many places (exactly the sharing
     [to_constr]'s own doc comment describes) -- the post-reification
     backstop in [classify_side] catches that rarer case. *)
  let rec fterm_nodes budget t =
    if budget <= 0 then raise Over_cap;
    let budget = budget - 1 in
    match fterm_of t with
    | FRel _ | FInd _ | FInt _ | FFloat _ | FString _
    | FIrrelevant | FLOCKED | FFlex _ -> budget
    | FAtom c -> constr_nodes_budget budget c
    | FConstruct (_, args) -> Array.fold_left fterm_nodes budget args
    | FApp (f, ve) -> Array.fold_left fterm_nodes (fterm_nodes budget f) ve
    | FProj (_, _, c) -> fterm_nodes budget c
    | FFix ((_, (_, tys, bds)), _) | FCoFix ((_, (_, tys, bds)), _) ->
      let budget = Array.fold_left constr_nodes_budget budget tys in
      Array.fold_left constr_nodes_budget budget bds
    | FCaseT (_, _, pms, p, c, ve, _) ->
      let budget = Array.fold_left constr_nodes_budget budget pms in
      let budget = constr_nodes_budget budget (snd (fst p)) in
      let budget = fterm_nodes budget c in
      Array.fold_left (fun b br -> constr_nodes_budget b (snd br)) budget ve
    | FCaseInvert (_, _, pms, p, indices, c, ve, _) ->
      let budget = Array.fold_left constr_nodes_budget budget pms in
      let budget = constr_nodes_budget budget (snd (fst p)) in
      let budget = Array.fold_left fterm_nodes budget (get_invert indices) in
      let budget = fterm_nodes budget c in
      Array.fold_left (fun b br -> constr_nodes_budget b (snd br)) budget ve
    | FLambda (_, tys, f, _) ->
      let budget = List.fold_left (fun b (_, c) -> constr_nodes_budget b c) budget tys in
      constr_nodes_budget budget f
    | FProd (_, t, c, _) -> constr_nodes_budget (fterm_nodes budget t) c
    | FLetIn (_, b, t, f, _) ->
      constr_nodes_budget (fterm_nodes (fterm_nodes budget b) t) f
    | FEvar (_, args, _, _) -> List.fold_left constr_nodes_budget budget args
    | FLIFT (_, a) -> fterm_nodes budget a
    | FCLOS (c, _) -> constr_nodes_budget budget c
    | FArray (_, arr, ty) ->
      let budget = budget - Parray.length_int arr in
      if budget <= 0 then raise Over_cap else fterm_nodes budget ty

  (* Second, independent structural hash over the realized [Constr.t],
     combined in one budgeted walk with an exact node count (the [size]
     component of the key): a different traversal/mixing scheme from
     whatever [Constr.hash] does internally, built from [Hashtbl.hash] on
     each node's own small payload (a generic, unrelated algorithm) tagged
     by constructor. Raises [Over_cap] as the reification-size backstop. *)
  let hash_and_size cap c =
    let rec go (budget, h) c =
      if budget <= 0 then raise Over_cap;
      let budget = budget - 1 in
      let tag = match kind c with
        | Rel i -> 0x1 lxor Hashtbl.hash i
        | Var id -> 0x2 lxor Hashtbl.hash id
        | Meta m -> 0x3 lxor Hashtbl.hash m
        | Evar (e, _) -> 0x4 lxor Hashtbl.hash e
        | Sort s -> 0x5 lxor Hashtbl.hash s
        | Cast _ -> 0x6
        | Prod _ -> 0x7
        | Lambda _ -> 0x8
        | LetIn _ -> 0x9
        | App _ -> 0xA
        | Const (cst, _) -> 0xB lxor Hashtbl.hash cst
        | Ind (ind, _) -> 0xC lxor Hashtbl.hash ind
        | Construct (ctor, _) -> 0xD lxor Hashtbl.hash ctor
        | Case _ -> 0xE
        | Fix _ -> 0xF
        | CoFix _ -> 0x10
        | Proj (p, _, _) -> 0x11 lxor Hashtbl.hash p
        | Int i -> 0x12 lxor Hashtbl.hash i
        | Float f -> 0x13 lxor Hashtbl.hash f
        | Array _ -> 0x14
        | String s -> 0x15 lxor Hashtbl.hash s
      in
      let h = (h * 1000003) lxor tag in
      Constr.fold go (budget, h) c
    in
    let (remaining, h) = go (cap, 0x9E3779B1) c in
    (h, cap - remaining)

  type reason = Open | BoundUniv | ReifyFailed | OverCap | HeapGuard | StackOverflow

  let unkeyable_open = ref 0
  let unkeyable_bound_univ = ref 0
  let unkeyable_reify_failed = ref 0
  let unkeyable_over_cap = ref 0
  let unkeyable_heap_guard = ref 0
  let unkeyable_stack_overflow = ref 0
  let record_unkeyable = function
    | Open -> incr unkeyable_open
    | BoundUniv -> incr unkeyable_bound_univ
    | ReifyFailed -> incr unkeyable_reify_failed
    | OverCap -> incr unkeyable_over_cap
    | HeapGuard -> incr unkeyable_heap_guard
    | StackOverflow -> incr unkeyable_stack_overflow

  type side_keyed = { h1 : int; h2 : int; sz : int; refs : ModPath.t list }
  type side_result = Keyed of side_keyed | Unkeyable of reason

  (* None: not even keyable (open term, carries a bound universe/sort-
     quality variable, fails to reify, or crosses the node cap) -- it
     can't mean the same thing in two different declarations, so it is
     excluded from the repeat-counting table entirely, not just from the
     shareable subset. Some: keyable; [refs] is every
     Const/Ind/Construct/Proj ModPath.t the term mentions, still to be
     checked against the library-import criterion by [refs_shareable]. *)
  let classify_side_inner lft t =
    if not (heap_guard_ok ()) then Unkeyable HeapGuard
    else match (try `Ok (fterm_nodes max_nodes t) with Over_cap -> `Cap) with
    | `Cap -> Unkeyable OverCap
    | `Ok _ ->
      (match safe_to_constr lft t with
       | None -> Unkeyable ReifyFailed
       | Some c ->
         (match scan c with
          | refs ->
            if has_bound_univs c then Unkeyable BoundUniv
            else
              (match (try `Ok (hash_and_size max_nodes c) with Over_cap -> `Cap) with
               | `Cap -> Unkeyable OverCap
               | `Ok (h2, sz) -> Keyed { h1 = Constr.hash c; h2; sz; refs })
          | exception Not_shareable -> Unkeyable Open))

  (* A term whose compact shape is small but whose nesting is very deep
     (e.g. a long chain of sequential updates -- the same PlainInit shape
     that drives the heap guard) can overflow the native OCaml stack in
     [fterm_nodes]/[hash_and_size]/[scan]/[CClosure.to_constr] itself,
     none of which are tail-recursive. Caught here, once per probe,
     rather than left to kill the whole process: real case on A6 (64G
     heap guard run, ~64,000,000 probes in). *)
  let classify_side lft t =
    try classify_side_inner lft t with Stack_overflow -> Unkeyable StackOverflow


  type entry = { verdict : bool; call : int }

  (* Lightweight key: two independent hashes plus the exact node count of
     each side, never the terms themselves -- a table entry is now a fixed
     handful of ints regardless of how big the compared terms are. A false
     match (both hashes AND both sizes coinciding for two actually-
     different term pairs) only blurs this diagnostic's counts, never a
     real verdict; see the issue comment for the assumed collision bound. *)
  module HKey = struct
    type t = {
      h1a : int; h2a : int; sz1 : int;
      h1b : int; h2b : int; sz2 : int;
      cumul : bool;
    }
    let equal a b =
      Int.equal a.h1a b.h1a && Int.equal a.h2a b.h2a && Int.equal a.sz1 b.sz1
      && Int.equal a.h1b b.h1b && Int.equal a.h2b b.h2b && Int.equal a.sz2 b.sz2
      && Bool.equal a.cumul b.cumul
    let hash a =
      let h = a.h1a in
      let h = h * 1000003 + a.h2a in
      let h = h * 1000003 + a.sz1 in
      let h = h * 1000003 + a.h1b in
      let h = h * 1000003 + a.h2b in
      let h = h * 1000003 + a.sz2 in
      if a.cumul then h lxor 0x5BF03635 else h
  end
  module Tbl = Hashtbl.Make(HKey)

  let table : entry Tbl.t = Tbl.create 65536

  let probes = ref 0
  let repeats = ref 0
  let repeats_success = ref 0
  let shareable_repeats_success = ref 0

  (* Top-10-by-shareable-repeats report: bucketed by the library currently
     being checked when the repeat was observed (the only library-grained
     fact a probe carries about where the saving would land; not the
     library that originally supplied the cached content). *)
  module DPTbl = Hashtbl.Make(struct
    type t = DirPath.t
    let equal = DirPath.equal
    let hash = DirPath.hash
  end)
  let per_library : int DPTbl.t = DPTbl.create 256
  let bump_library dp =
    match DPTbl.find_opt per_library dp with
    | Some n -> DPTbl.replace per_library dp (n + 1)
    | None -> DPTbl.add per_library dp 1

  (* Allocation and CPU spent computing keys (reification, surface/
     backstop size walks, both hashes) -- over EVERY probe, keyable or
     not. Gc.counters is three field reads, no allocation; Sys.time is a
     getrusage-class call. [ccnv] snapshots both at a window's start and
     end and subtracts the delta from that window's own raw Gc/CPU delta,
     so a nested probe's OWN classification cost -- paid again every time
     [record] runs for it, strictly inside whichever ancestor window is
     currently open -- is excluded from the ceiling: that cost is diagnostic
     overhead a real cache would not need to pay the way this counter does
     (it classifies shareability in full; a real cache only hashes), and
     without the subtraction an ancestor's measured window silently
     includes every descendant's reification work, which is how an
     earlier version of this measurement priced "repeats" above the
     process's own total allocation. *)
  let key_cost_words = ref 0.
  let key_cost_cpu_seconds = ref 0.
  let key_cost_snapshot () = (!key_cost_words, !key_cost_cpu_seconds)

  let gc_words () =
    let (minor, promoted, major) = Gc.counters () in
    minor +. major -. promoted


  (* How many ancestor probes (recursive ccnv calls inside the SAME
     eqappr) are currently running. Purely structural -- incremented and
     decremented in [ccnv] around every xdecl-gated [eqappr] call,
     regardless of reification or classification, so checking it never
     requires reifying a term early. (An earlier version of this counter
     reified to classify BEFORE calling [eqappr], to decide whether to
     time that call; that meant reifying pre-reduction, not-yet-forced
     terms on every single probe instead of only the post-reduction forms
     [eqappr]'s own in-place WHNF memoization leaves behind -- the surface
     node cap here cannot see that blowup, since it undercounts exactly
     the substitution expansion a pre-reduction term is still carrying,
     and materializing it anyway OOMed a 24G cap in under two minutes on
     the Coturn tree. Keeping reification where the original, safe v3
     counter had it -- after [eqappr] runs -- avoids that regression.) *)
  let measuring_depth = ref 0
  let outermost () = Int.equal !measuring_depth 0
  let enter_measure () = incr measuring_depth
  let exit_measure () = decr measuring_depth

  let repeat_alloc_words = ref 0.
  let repeat_cpu_seconds = ref 0.
  let repeat_outermost_count = ref 0
  let record_measure alloc cpu =
    repeat_alloc_words := !repeat_alloc_words +. alloc;
    repeat_cpu_seconds := !repeat_cpu_seconds +. cpu;
    incr repeat_outermost_count

  (* Called once per probe, AFTER [eqappr] has run and mutated term1/term2's
     closures in place to their WHNF form (the same point the committed v3
     counter reified at) -- reifies and classifies both sides (paying, and
     metering, the key-computation cost over every probe), looks the key
     up, and updates/inserts it. [outermost] and [timing] come from [ccnv]:
     whether this probe's own [eqappr] call was itself nested inside
     another one already being weighed, and if not, the Gc/CPU delta that
     call cost -- recorded only if this turns out to be a genuine
     shareable successful repeat, so the ceiling sum never double-counts a
     subtree a real cache hit would have skipped entirely. *)
  let record ~cumul ~outermost ~timing lft1 term1 lft2 term2 verdict =
    incr probes;
    if Int.equal (!probes mod 2_000_000) 0 then begin
      let st = Gc.quick_stat () in
      Printf.eprintf
        "ROCQ_CONV_XDECL_PROGRESS probes=%d table_entries=%d heap_words=%d minor_words=%.0f major_words=%.0f lib=%s\n%!"
        !probes (Tbl.length table) st.Gc.heap_words st.Gc.minor_words st.Gc.major_words
        (match !current_library with Some dp -> DirPath.to_string dp | None -> "?")
    end;
    let a0 = gc_words () in
    let c0 = Sys.time () in
    let s1 = classify_side lft1 term1 in
    let s2 = classify_side lft2 term2 in
    let a1 = gc_words () in
    let c1 = Sys.time () in
    key_cost_words := !key_cost_words +. (a1 -. a0);
    key_cost_cpu_seconds := !key_cost_cpu_seconds +. (c1 -. c0);
    (match s1 with Unkeyable r -> record_unkeyable r | Keyed _ -> ());
    (match s2 with Unkeyable r -> record_unkeyable r | Keyed _ -> ());
    match s1, s2 with
    | Keyed k1, Keyed k2 ->
      let key = { HKey.h1a = k1.h1; h2a = k1.h2; sz1 = k1.sz;
                  h1b = k2.h1; h2b = k2.h2; sz2 = k2.sz; cumul } in
      (match Tbl.find_opt table key with
       | Some old when old.call <> !call_id ->
         incr repeats;
         if old.verdict then begin
           incr repeats_success;
           if refs_shareable k1.refs && refs_shareable k2.refs then begin
             incr shareable_repeats_success;
             (match !current_library with
              | Some dp -> bump_library dp
              | None -> ());
             if outermost then
               (match timing with
                | Some (alloc, cpu) -> record_measure alloc cpu
                | None -> ())
           end
         end
       | Some _ -> ()
       | None -> Tbl.add table key { verdict; call = !call_id })
    | _ -> ()

  let approx_table_words () =
    (* One Hashtbl bucket cons cell (key, data, next + header: 4 words)
       plus the HKey.t record (7 fields + header: 8 words) plus the entry
       record (2 fields + header: 3 words) -- fixed per entry regardless
       of how big the compared terms were, unlike the first cut of this
       counter which stored the terms themselves. *)
    Tbl.length table * (4 + 8 + 3)

  let () =
    if enabled then at_exit (fun () ->
      let top =
        DPTbl.fold (fun dp n acc -> (DirPath.to_string dp, n) :: acc) per_library []
        |> List.sort (fun (_,a) (_,b) -> Int.compare b a)
      in
      let top10 = List.filteri (fun i _ -> i < 10) top in
      Printf.eprintf
        "ROCQ_CONV_XDECL_STATS probes=%d repeats=%d repeats_success=%d shareable_repeats_success=%d table_entries=%d table_words=%d max_nodes=%d max_heap_words=%d heap_guard_tripped=%b unkeyable_open=%d unkeyable_bound_univ=%d unkeyable_reify_failed=%d unkeyable_over_cap=%d unkeyable_heap_guard=%d unkeyable_stack_overflow=%d\n%!"
        !probes !repeats !repeats_success !shareable_repeats_success
        (Tbl.length table) (approx_table_words ()) max_nodes max_heap_words !heap_guard_tripped
        !unkeyable_open !unkeyable_bound_univ !unkeyable_reify_failed !unkeyable_over_cap !unkeyable_heap_guard
        !unkeyable_stack_overflow;
      Printf.eprintf
        "ROCQ_CONV_XDECL_WEIGHT key_cost_words=%.0f key_cost_cpu_seconds=%.6f repeat_outermost_count=%d repeat_alloc_words=%.0f repeat_cpu_seconds=%.6f\n%!"
        !key_cost_words !key_cost_cpu_seconds !repeat_outermost_count !repeat_alloc_words !repeat_cpu_seconds;
      List.iter (fun (name, n) ->
          Printf.eprintf "ROCQ_CONV_XDECL_STATS top_library %s %d\n%!" name n)
        top10)
end

type 'e conv_tab = {
  cnv_inf : clos_infos;
  cnv_typ : bool; (* true if the input terms were well-typed *)
  lft_tab : clos_tab;
  rgt_tab : clos_tab;
  err_ret : 'e -> payload;
  cnv_cache : ConvCache.t option;
  (* true only for the checked-conversion ([gen_conv]) top-level call that
     created this conv_tab, and only when ROCQ_CONV_XDECL_STATS=1; gates
     the XDeclCache hook in [ccnv]'s cache-disabled branch. Never true for
     [generic_conv] or the [CClosure.set_conv] callback. *)
  cnv_xdecl : bool;
}
(** Invariant: for any tl ∈ lft_tab and tr ∈ rgt_tab, there is no mutable memory
    location contained both in tl and in tr. *)

let fail_check (infos : 'err conv_tab) (state, check) = match state with
| Result.Ok state -> (state, check)
| Result.Error None -> raise NotConvertible
| Result.Error (Some err) -> raise (NotConvertibleTrace (infos.err_ret err))

let convert_inductives cv_pb ind nargs u1 u2 (s, check) =
  convert_inductives_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    cv_pb ind nargs u1 u2 s, check

let constructor_cumulativity_arguments (mind, ind, ctor) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1)

let convert_constructors_gen cmp_instances cmp_cumul (mind, ind, cns) nargs u1 u2 s =
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some _ ->
    let num_cnstr_args = constructor_cumulativity_arguments (mind,ind,cns) in
    if not (Int.equal num_cnstr_args nargs) then
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      (** By invariant, both constructors have a common supertype,
          so they are convertible _at that type_. *)
      let qvariance = Array.make (fst (UVars.Instance.length u1)) UVars.Variance.Irrelevant in
      let uvariance = Array.make (snd (UVars.Instance.length u1)) UVars.Variance.Irrelevant in
      cmp_cumul CONV (qvariance,uvariance) u1 u2 s

let convert_constructors ctor nargs u1 u2 (s, check) =
  convert_constructors_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    ctor nargs u1 u2 s, check

let conv_table_key infos ~nargs k1 k2 cuniv =
  if k1 == k2 then cuniv else
  match k1, k2 with
  | ConstKey (cst, u), ConstKey (cst', u') when Constant.CanOrd.equal cst cst' ->
    if UVars.Instance.equal u u' then cuniv
    else if Int.equal nargs 1 && is_array_type (info_env infos.cnv_inf) cst then cuniv
    else
      let flex = evaluable_constant cst (info_env infos.cnv_inf)
        && RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST cst)
      in fail_check infos @@ convert_instances ~flex u u' cuniv
  | VarKey id, VarKey id' when Id.equal id id' -> cuniv
  | RelKey n, RelKey n' when Int.equal n n' -> cuniv
  | _ -> raise NotConvertible

let same_args_size sk1 sk2 =
  let n = CClosure.stack_args_size sk1 in
  if Int.equal n (CClosure.stack_args_size sk2) then n
  else raise NotConvertible

(** The same heap separation invariant must hold for the fconstr arguments
    passed to each respective side of the conversion function below. *)

let push_relevance infos r =
  { infos with cnv_inf = CClosure.push_relevance infos.cnv_inf r }

let push_relevances infos nas =
  { infos with cnv_inf = CClosure.push_relevances infos.cnv_inf nas }

let identity_of_ctx (ctx:Constr.rel_context) =
  Context.Rel.instance mkRel 0 ctx

(* ind -> fun args => ind args *)
let eta_expand_ind env (ind,u as pind) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context u mip.mind_arity_ctxt in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkIndU pind, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let eta_expand_constructor env ((ind,ctor),u as pctor) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context u (fst mip.mind_nf_lc.(ctor-1)) in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkConstructU pctor, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let esubst_of_context ctx args e =
  let rec aux lft e args ctx = match ctx with
  | [] -> lft, e
  | None :: ctx -> aux (lft + 1) (usubs_lift e) (usubs_lift args) ctx
  | Some c :: ctx ->
    let c = mk_clos args c in
    aux lft (usubs_cons c e) (usubs_cons c args) ctx
  in
  aux 0 e args (List.rev ctx)

let irr_flex infos = function
  | ConstKey (con,u) -> is_irrelevant infos @@ UVars.subst_instance_relevance u @@ Environ.constant_relevance con (info_env infos)
  | VarKey x -> is_irrelevant infos @@ Context.Named.Declaration.get_relevance (Environ.lookup_named x (info_env infos))
  | RelKey x -> is_irrelevant infos @@ Context.Rel.Declaration.get_relevance (Environ.lookup_rel x (info_env infos))

let eq_universes (_,e1) (_,e2) u1 u2 =
  let subst e u = if UVars.Instance.is_empty e then u else UVars.subst_instance_instance e u in
  UVars.Instance.equal (subst e1 u1) (subst e2 u2)

let rec compare_under e1 c1 e2 c2 =
  match Constr.kind c1, Constr.kind c2 with
  | Cast (c1, _, _), _ -> compare_under e1 c1 e2 c2
  | _, Cast (c2, _, _) -> compare_under e1 c1 e2 c2
  | Rel i, Rel j -> begin match Esubst.expand_rel i (fst e1) with
      | Inl _ -> false
      | Inr (k, _) -> begin match Esubst.expand_rel j (fst e2) with
          | Inl _ -> false
          | Inr (k', _) -> Int.equal k k'
        end
    end
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | String s1, String s2 -> Pstring.equal s1 s2
  | Sort s1, Sort s2 ->
    let subst_instance_sort u s =
      if UVars.Instance.is_empty u then s else UVars.subst_instance_sort u s
    in
    let s1 = subst_instance_sort (snd e1) s1
    and s2 = subst_instance_sort (snd e2) s2 in
    Sorts.equal s1 s2
  | Prod (_,t1,c1), Prod (_,t2,c2) ->
    compare_under e1 t1 e2 t2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
    compare_under e1 t1 e2 t2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | LetIn (_,b1,_,c1), LetIn (_,b2,_,c2) ->
    (* don't care about types when bodies are equal *)
    compare_under e1 b1 e2 b2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2)
    && compare_under e1 c1 e2 c2
    && Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) l1 l2
  | Proj (p1,_,c1), Proj (p2,_,c2) ->
    Projection.CanOrd.equal p1 p2 && compare_under e1 c1 e2 c2
  | Evar _, Evar _ -> false
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.CanOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> Ind.CanOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    Construct.CanOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Case _, Case _ | Fix _, Fix _ | CoFix _, CoFix _ -> false (* todo some other time *)
  | Array(_,t1,def1,ty1), Array(_,t2,def2,ty2) ->
    Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) t1 t2
    && compare_under e1 def1 e2 def2
    && compare_under e1 ty1 e2 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false


let rec fast_test lft1 term1 lft2 term2 = match fterm_of term1, fterm_of term2 with
  | FLIFT (i, term1), (FLIFT _ | FCLOS _) -> fast_test (el_shft i lft1) term1 lft2 term2
  | FCLOS _, FLIFT (j, term2) -> fast_test lft1 term1 (el_shft j lft2) term2
  | FCLOS (c1, (e1,u1)), FCLOS (c2, (e2,u2)) ->
    eq_lift lft1 lft2 &&
    compare_under (e1, u1) c1 (e2, u2) c2
  | _ -> false

let assert_reduced_constructor s =
  if not @@ CList.is_empty s then
    CErrors.anomaly Pp.(str "conversion was given unreduced term (FConstruct).")

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  let fast = fast_test lft1 term1 lft2 term2 in
  if fast then cuniv
  else
    match infos.cnv_cache with
    | None ->
      if not infos.cnv_xdecl then
        eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv
      else begin
        let cumul = match cv_pb with CONV -> false | CUMUL -> true in
        let is_outermost = XDeclCache.outermost () in
        XDeclCache.enter_measure ();
        let snap0 =
          if is_outermost then
            Some (XDeclCache.gc_words (), Sys.time (), XDeclCache.key_cost_snapshot ())
          else None
        in
        let settle verdict =
          XDeclCache.exit_measure ();
          let timing = match snap0 with
            | Some (g0, t0, (kw0, kc0)) ->
              let g1 = XDeclCache.gc_words () in
              let t1 = Sys.time () in
              let (kw1, kc1) = XDeclCache.key_cost_snapshot () in
              (* Exclude every nested probe's own key-computation cost
                 (accrued into [key_cost_words]/[key_cost_cpu_seconds] by
                 its own [record] call, strictly inside this window): that
                 cost is this diagnostic's own classification overhead, not
                 real conversion work, and left in, it is exactly what made
                 an earlier version of this measurement exceed the run's
                 own total allocation. *)
              Some (g1 -. g0 -. (kw1 -. kw0), t1 -. t0 -. (kc1 -. kc0))
            | None -> None
          in
          XDeclCache.record ~cumul ~outermost:is_outermost ~timing lft1 term1 lft2 term2 verdict
        in
        match eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv with
        | cuniv -> settle true; cuniv
        | exception NotConvertible -> settle false; raise NotConvertible
      end
    | Some cache ->
      let cumul = match cv_pb with CONV -> false | CUMUL -> true in
      match ConvCache.probe cache ~cumul lft1 term1 lft2 term2 with
      | Some true -> cuniv
      | Some false -> raise NotConvertible
      | None ->
        match eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv with
        | cuniv ->
          ConvCache.record cache ~cumul lft1 term1 lft2 term2 true; cuniv
        | exception NotConvertible ->
          ConvCache.record cache ~cumul lft1 term1 lft2 term2 false; raise NotConvertible

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let appr1 = whd_stack ninfos infos.lft_tab (fst st1) (snd st1) in
  let appr2 = whd_stack ninfos infos.rgt_tab (fst st2) (snd st2) in
  eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv

(* assumes that appr1 and appr2 are in whnf *)
and eqwhnf cv_pb l2r infos (lft1, (hd1, v1) as appr1) (lft2, (hd2, v2) as appr2) cuniv =
  (** We delay the computation of the lifts that apply to the head of the term
      with [el_stack] inside the branches where they are actually used. *)
  (** Irrelevant terms are guaranteed to be [FIrrelevant], except for [FFlex],
      [FRel] and [FLambda]. Those ones are handled specifically below. *)
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
        (match kind a1, kind a2 with
           | (Sort s1, Sort s2) ->
               if not (is_empty_stack v1 && is_empty_stack v2) then
                 (* May happen because we convert application right to left *)
                 raise NotConvertible;
              fail_check infos @@ sort_cmp_universes cv_pb s1 s2 cuniv
           | (Meta n, Meta m) ->
               if Int.equal n m
               then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
           | _ -> raise NotConvertible)
    | (FEvar (ev1, args1, env1, _), FEvar (ev2, args2, env2, _)) ->
        if Evar.equal ev1 ev2 then
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_stacks l2r infos lft1 lft2 v1 v2 cuniv in
          convert_list l2r infos el1 el2
            (List.map (mk_clos env1) args1)
            (List.map (mk_clos env2) args2) cuniv
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let n = reloc_rel n el1 in
        let m = reloc_rel m el2 in
        let rn = Range.get (info_relevances infos.cnv_inf) (n - 1) in
        let rm = Range.get (info_relevances infos.cnv_inf) (m - 1) in
        if is_irrelevant infos.cnv_inf rn && is_irrelevant infos.cnv_inf rm then
          let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
          let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else if Int.equal n m then
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      (try
         let nargs = same_args_size v1 v2 in
         let cuniv = conv_table_key infos ~nargs fl1 fl2 cuniv in
         let () = if irr_flex infos.cnv_inf fl1 then raise NotConvertible (* trigger the fallback *) in
         let mask = if infos.cnv_typ then match fl1 with
         | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
         | RelKey _ | VarKey _ -> [||]
         else [||]
         in
         convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
       with NotConvertible | NotConvertibleTrace _ ->
        let r1 = unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 in
        let r2 = unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 in
        match r1, r2 with
        | None, None -> raise NotConvertible
        | Some (t1, v1), Some (t2, v2) ->
          (* else the oracle tells which constant is to be expanded *)
          let oracle = CClosure.oracle_of_infos infos.cnv_inf in
          let to_er fl =
            match fl with
            | ConstKey (c, _) -> Some (Conv_oracle.EvalConstRef c)
            | VarKey id -> Some (Conv_oracle.EvalVarRef id)
            | RelKey _ -> None
          in
          let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
          let () = Control.check_for_interrupt () in
          if Conv_oracle.oracle_order oracle l2r (to_er fl1) (to_er fl2) then
            let appr1 = whd_stack ninfos infos.lft_tab t1 v1 in
            eqwhnf cv_pb l2r infos (lft1, appr1) appr2 cuniv
          else
            let appr2 = whd_stack ninfos infos.rgt_tab t2 v2 in
            eqwhnf cv_pb l2r infos appr1 (lft2, appr2) cuniv
        | Some (t1, v1), None ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab t1 v1 in
          eqwhnf cv_pb l2r infos (lft1, t1) appr2 cuniv
        | None, Some (t2, v2) ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab t2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, t2) cuniv
        )

    | (FProj (p1,r1,c1), FProj (p2, r2, c2)) ->
      (* Projections: prefer unfolding to first-order unification,
         which will happen naturally if the terms c1, c2 are not in constructor
         form *)
      (match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
      | None ->
        match unfold_projection infos.cnv_inf p2 r2 with
        | Some s2 ->
          eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
        | None ->
          if Projection.Repr.CanOrd.equal (Projection.repr p1) (Projection.repr p2)
             && compare_stack_shape v1 v2 then
            let el1 = el_stack lft1 v1 in
            let el2 = el_stack lft2 v2 in
            let u1 = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
              convert_stacks l2r infos lft1 lft2 v1 v2 u1
          else (* Two projections in WHNF: unfold *)
            raise NotConvertible)

    | (FProj (p1,r1,c1), t2) ->
      begin match unfold_projection infos.cnv_inf p1 r1 with
       | Some s1 ->
         eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
       | None ->
         begin match t2 with
          | FFlex fl2 ->
            begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
             | Some t2 ->
               eqappr cv_pb l2r infos appr1 (lft2, t2) cuniv
             | None -> raise NotConvertible
            end
          | _ -> raise NotConvertible
         end
      end

    | (t1, FProj (p2,r2,c2)) ->
      begin match unfold_projection infos.cnv_inf p2 r2 with
       | Some s2 ->
         eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
       | None ->
         begin match t1 with
          | FFlex fl1 ->
            begin match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
             | Some t1 ->
               eqappr cv_pb l2r infos (lft1, t1) appr2 cuniv
             | None -> raise NotConvertible
            end
          | _ -> raise NotConvertible
         end
      end

    (* other constructors *)
    | (FLambda _, FLambda _) ->
        (* Inconsistency: we tolerate that v1, v2 contain shift and update but
           we throw them away *)
        if not (is_empty_stack v1 && is_empty_stack v2) then
          anomaly (Pp.str "conversion was given ill-typed terms (FLambda).");
        let (x1,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV l2r (push_relevance infos x1) (el_lift el1) (el_lift el2) bd1 bd2 cuniv

    | (FProd (x1, c1, c2, e), FProd (_, c'1, c'2, e')) ->
        if not (is_empty_stack v1 && is_empty_stack v2) then
          (* May happen because we convert application right to left *)
          raise NotConvertible;
        (* Luo's system *)
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 c1 c'1 cuniv in
        let x1 = usubst_binder e x1 in
        ccnv cv_pb l2r (push_relevance infos x1) (el_lift el1) (el_lift el2) (mk_clos (usubs_lift e) c2) (mk_clos (usubs_lift e') c'2) cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x1,_ty1,bd1) = destFLambda mk_clos hd1 in
        let infos = push_relevance infos x1 in
        eqappr CONV l2r infos
          (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack infos.cnv_inf x1 v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x2,_ty2,bd2) = destFLambda mk_clos hd2 in
        let infos = push_relevance infos x2 in
        eqappr CONV l2r infos
          (el_lift lft1, (hd1, eta_expand_stack infos.cnv_inf x2 v1)) (el_lift lft2, (bd2, [])) cuniv

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
      begin match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
        | Some (def1,v1) ->
          (** By virtue of the previous case analyses, we know [c2] is rigid.
              Conversion check to rigid terms eventually implies full weak-head
              reduction, so instead of repeatedly performing small-step
              unfoldings, we perform reduction with all flags on. *)
            let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
            let r1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab def1 v1 in
            eqwhnf cv_pb l2r infos (lft1, r1) appr2 cuniv
        | None ->
          (match c2 with
           | FConstruct (((ind2,1),u2),_) ->
             let () = assert_reduced_constructor v2 in
             (try
                let v2, v1 =
                  eta_expand_ind_stack (info_env infos.cnv_inf) (ind2,u2) hd2 (snd appr1)
                in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
              with Not_found -> raise NotConvertible)
           | _ -> raise NotConvertible)
      end

    | (c1, FFlex fl2)      ->
       begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
        | Some (def2, v2) ->
          (** Symmetrical case of above. *)
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let r2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab def2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, r2) cuniv
        | None ->
          match c1 with
          | FConstruct (((ind1,1),u1),_) ->
            let () = assert_reduced_constructor v1 in
            (try let v1, v2 =
                   eta_expand_ind_stack (info_env infos.cnv_inf) (ind1,u1) hd1 (snd appr2)
               in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
             with Not_found -> raise NotConvertible)
          | _ -> raise NotConvertible
       end

    (* Inductive types:  MutInd MutConstruct Fix Cofix *)
    | (FInd (ind1,u1 as pind1), FInd (ind2,u2 as pind2)) ->
      if Ind.CanOrd.equal ind1 ind2 then
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          let nargs = same_args_size v1 v2 in
          match fail_check infos @@ convert_inductives cv_pb (mind, snd ind1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | exception MustExpand ->
            let env = info_env infos.cnv_inf in
            let hd1 = eta_expand_ind env pind1 in
            let hd2 = eta_expand_ind env pind2 in
            eqappr cv_pb l2r infos (lft1,(hd1,v1)) (lft2,(hd2,v2)) cuniv
      else raise NotConvertible

    | (FConstruct (((ind1,j1),u1 as pctor1,args1)), FConstruct (((ind2,j2),u2 as pctor2),args2)) ->
      let () = assert_reduced_constructor v1 in
      let () = assert_reduced_constructor v2 in
      let nargs = Array.length args1 in
      let () = if not @@ Int.equal nargs (Array.length args2) then raise NotConvertible in
      let v1 = append_stack args1 v1 in
      let v2 = append_stack args2 v2 in
      if Int.equal j1 j2 && Ind.CanOrd.equal ind1 ind2 then
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          match fail_check infos @@ convert_constructors (mind, snd ind1, j1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | exception MustExpand ->
            let env = info_env infos.cnv_inf in
            let hd1 = eta_expand_constructor env pctor1 in
            let hd2 = eta_expand_constructor env pctor2 in
            eqappr cv_pb l2r infos (lft1,(hd1,v1)) (lft2,(hd2,v2)) cuniv
      else raise NotConvertible

    (* Eta expansion of records *)
    | (FConstruct (((ind1,j1),u1), _),_) ->
      let () = assert_reduced_constructor v1 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j1 1 then raise NotConvertible in
      (try
         let v1, v2 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind1,u1) hd1 (snd appr2)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (_, FConstruct (((ind2,j2),u2),_)) ->
      let () = assert_reduced_constructor v2 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j2 1 then raise NotConvertible in
      (try
         let v2, v1 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind2,u2) hd2 (snd appr1)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (FFix (((op1, i1),(na1,tys1,cl1)),e1), FFix(((op2, i2),(_,tys2,cl2)),e2)) ->
        if Int.equal i1 i2 && Array.equal Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let cuniv =
            let na1 = Array.map (usubst_binder e1) na1 in
            let infos = push_relevances infos na1 in
            convert_vect l2r infos
                         (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | (FCoFix ((op1,(na1,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
        if Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let cuniv =
            let na1 = Array.map (usubst_binder e1) na1 in
            let infos = push_relevances infos na1 in
            convert_vect l2r infos
                         (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FInt i1, FInt i2 ->
       if Uint63.equal i1 i2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       else raise NotConvertible

    | FFloat f1, FFloat f2 ->
        if Float64.equal f1 f2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FString s1, FString s2 ->
        if Pstring.equal s1 s2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FCaseInvert (ci1,u1,pms1,p1,iv1,_,br1,e1), FCaseInvert (ci2,u2,pms2,p2,iv2,_,br2,e2) ->
      (if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then raise NotConvertible);
      let el1 = el_stack lft1 v1 and el2 = el_stack lft2 v2 in
      let fold c1 c2 cuniv = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
      (** FIXME: cache the presence of let-bindings in the case_info *)
      let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
      let mip = mind.Declarations.mind_packets.(snd ci1.ci_ind) in
      let cuniv =
        let ind = (mind,snd ci1.ci_ind) in
        let nargs = inductive_cumulativity_arguments ind in
        let u1 = CClosure.usubst_instance e1 u1 in
        let u2 = CClosure.usubst_instance e2 u2 in
        fail_check infos @@ convert_inductives CONV ind nargs u1 u2 cuniv
      in
      let pms1 = mk_clos_vect e1 pms1 in
      let pms2 = mk_clos_vect e2 pms2 in
      let cuniv = Array.fold_right2 fold pms1 pms2 cuniv in
      let cuniv = Array.fold_right2 fold (get_invert iv1) (get_invert iv2) cuniv in
      let cuniv = convert_return_clause mind mip l2r infos e1 e2 el1 el2 u1 u2 pms1 pms2 p1 p2 cuniv in
      (* not clear if we need to pass both u1 and u2 as
         convert_inductives should have enforced that they are
         equivalent when used to instantiate this inductive's
         components, but we may as well *)
      let cuniv = convert_branches mind mip l2r infos e1 e2 el1 el2 u1 u2 pms1 pms2 br1 br2 cuniv in
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

    | FArray (u1,t1,ty1), FArray (u2,t2,ty2) ->
      let len = Parray.length_int t1 in
      if not (Int.equal len (Parray.length_int t2)) then raise NotConvertible;
      let cuniv = fail_check infos @@ convert_instances_cumul CONV UVars.prim_array_variance u1 u2 cuniv in
      let el1 = el_stack lft1 v1 in
      let el2 = el_stack lft2 v2 in
      let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
      let cuniv = Parray.fold_left2 (fun u v1 v2 -> ccnv CONV l2r infos el1 el2 v1 v2 u) cuniv t1 t2 in
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

    | (FRel n1, FIrrelevant) ->
      let n1 = reloc_rel n1 (el_stack lft1 v1) in
      let r1 = Range.get (info_relevances infos.cnv_inf) (n1 - 1) in
      if is_irrelevant infos.cnv_inf r1 then
        let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | (FIrrelevant, FRel n2) ->
      let n2 = reloc_rel n2 (el_stack lft2 v2) in
      let r2 = Range.get (info_relevances infos.cnv_inf) (n2 - 1) in
      if is_irrelevant infos.cnv_inf r2 then
        let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | FIrrelevant, FIrrelevant ->
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCaseT _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCaseT _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) -> assert false

     | (FRel _ | FAtom _ | FInd _ | FFix _ | FCoFix _ | FCaseInvert _
       | FProd _ | FEvar _ | FInt _ | FFloat _ | FString _
       | FArray _ | FIrrelevant), _ -> raise NotConvertible

and convert_stacks ?(mask = [||]) l2r infos lft1 lft2 stk1 stk2 cuniv =
  let f (l1, t1) (l2, t2) cuniv = ccnv CONV l2r infos l1 l2 t1 t2 cuniv in
  let rec cmp_rec nargs pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          (* Stacks are known to have the same argument size *)
          let rnargs = match z1 with
          | Zlapp a -> if nargs < 0 then -1 else nargs + Array.length a
          | Zlproj _ | Zlfix _ | Zlcase _ | Zlprimitive _ -> -1
          in
          let cu1 = cmp_rec rnargs s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) ->
              if nargs < 0 then
               Array.fold_right2 f a1 a2 cu1
              else
                let rec fold i cu =
                  if i < 0 then cu
                  else if nargs + i < Array.length mask && not mask.(nargs + i) then
                    fold (i - 1) cu (* skip runtime irrelevant argument *)
                  else
                    let cu = f a1.(i) a2.(i) cu in
                    fold (i - 1) cu
                in
                fold (Array.length a1 - 1) cu1
            | (Zlproj (c1,_l1),Zlproj (c2,_l2)) ->
              if not (Projection.Repr.CanOrd.equal c1 c2) then
                raise NotConvertible
              else cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec (-1) a1 a2 cu2
            | (Zlcase(ci1,l1,u1,pms1,p1,br1,e1),Zlcase(ci2,l2,u2,pms2,p2,br2,e2)) ->
                if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then
                  raise NotConvertible;
                let cu = cu1 in
                (** FIXME: cache the presence of let-bindings in the case_info *)
                let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
                let mip = mind.Declarations.mind_packets.(snd ci1.ci_ind) in
                let cu =
                  if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
                    convert_instances ~flex:false u1 u2 cu
                  else
                    let u1 = CClosure.usubst_instance e1 u1 in
                    let u2 = CClosure.usubst_instance e2 u2 in
                    match mind.Declarations.mind_variance with
                    | None -> convert_instances ~flex:false u1 u2 cu
                    | Some variances -> convert_instances_cumul CONV variances u1 u2 cu
                in
                let cu = fail_check infos cu in
                let pms1 = mk_clos_vect e1 pms1 in
                let pms2 = mk_clos_vect e2 pms2 in
                let fold_params c1 c2 accu = f (l1, c1) (l2, c2) accu in
                let cu = Array.fold_right2 fold_params pms1 pms2 cu in
                let cu = convert_return_clause mind mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 p1 p2 cu in
                convert_branches mind mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 br1 br2 cu
            | (Zlprimitive(op1,_,rargs1,kargs1),Zlprimitive(op2,_,rargs2,kargs2)) ->
              if not (CPrimitives.equal op1 op2) then raise NotConvertible else
                let cu2 = List.fold_right2 f rargs1 rargs2 cu1 in
                let fk (_,a1) (_,a2) cu = f a1 a2 cu in
                List.fold_right2 fk kargs1 kargs2 cu2
            | ((Zlapp _ | Zlproj _ | Zlfix _| Zlcase _| Zlprimitive _), _) -> assert false)
      | _ -> cuniv in
  if compare_stack_shape stk1 stk2 then
    let nargs = if Array.is_empty mask then -1 else 0 in
    cmp_rec nargs (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
  else raise NotConvertible

and convert_vect l2r infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if Int.equal lv1 lv2
  then
    let rec fold n cuniv =
      if n >= lv1 then cuniv
      else
        let cuniv = ccnv CONV l2r infos lft1 lft2 v1.(n) v2.(n) cuniv in
        fold (n+1) cuniv in
    fold 0 cuniv
  else raise NotConvertible

and convert_under_context l2r infos e1 e2 lft1 lft2 ctx (nas1, c1) (nas2, c2) cu =
  let n = Array.length nas1 in
  let () = assert (Int.equal n (Array.length nas2)) in
  let n, e1, e2 = match ctx with
  | None -> (* nolet *)
    let e1 = usubs_liftn n e1 in
    let e2 = usubs_liftn n e2 in
    (n, e1, e2)
  | Some (ctx, args1, args2) ->
    let n1, e1 = esubst_of_context ctx args1 e1 in
    let n2, e2 = esubst_of_context ctx args2 e2 in
    let () = assert (Int.equal n1 n2) in
    n1, e1, e2
  in
  let lft1 = el_liftn n lft1 in
  let lft2 = el_liftn n lft2 in
  let infos = push_relevances infos (Array.map (usubst_binder e1) nas1) in
  ccnv CONV l2r infos lft1 lft2 (mk_clos e1 c1) (mk_clos e2 c2) cu

and convert_return_clause mib mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 p1 p2 cu =
  let ctx =
    if Int.equal mip.mind_nrealargs mip.mind_nrealdecls then None
    else
      let ctx, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
      let pms1 = inductive_subst mib u1 pms1 in
      let pms2 = inductive_subst mib u2 pms2 in
      let open Context.Rel.Declaration in
      (* Add the inductive binder *)
      let ctx = None :: List.map get_value ctx in
      Some (ctx, pms1, pms2)
  in
  convert_under_context l2r infos e1 e2 l1 l2 ctx (fst p1) (fst p2) cu

and convert_branches mib mip l2r infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 br1 br2 cuniv =
  let fold i (ctx, _) cuniv =
    let ctx =
      if Int.equal mip.mind_consnrealdecls.(i) mip.mind_consnrealargs.(i) then None
      else
        let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
        let ctx = List.map Context.Rel.Declaration.get_value ctx in
        let pms1 = inductive_subst mib u1 pms1 in
        let pms2 = inductive_subst mib u2 pms2 in
        Some (ctx, pms1, pms2)
    in
    let c1 = br1.(i) in
    let c2 = br2.(i) in
    convert_under_context l2r infos e1 e2 lft1 lft2 ctx c1 c2 cuniv
  in
  Array.fold_right_i fold mip.mind_nf_lc cuniv

and convert_list l2r infos lft1 lft2 v1 v2 cuniv = match v1, v2 with
| [], [] -> cuniv
| c1 :: v1, c2 :: v2 ->
  let cuniv = ccnv CONV l2r infos lft1 lft2 c1 c2 cuniv in
  convert_list l2r infos lft1 lft2 v1 v2 cuniv
| _, _ -> raise NotConvertible

let clos_gen_conv (type err) ~typed ~use_cache trans cv_pb l2r evars env graph univs t1 t2 =
  NewProfile.profile "Conversion" begin fun () ->
      let reds = RedFlags.red_add_transparent RedFlags.betaiotazeta trans in
      let infos = create_conv_infos ~univs:graph ~evars reds env in
      let module Error = struct type payload += Error of err end in
      let box e = Error.Error e in
      let cache = if use_cache then ConvCache.create () else None in
      let xdecl = use_cache && XDeclCache.enabled in
      if xdecl then XDeclCache.new_call ();
      let infos = {
        cnv_inf = infos;
        cnv_typ = typed;
        lft_tab = create_tab ();
        rgt_tab = create_tab ();
        err_ret = box;
        cnv_cache = cache;
        cnv_xdecl = xdecl;
      } in
      try Result.Ok (ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs)
      with
      | NotConvertible -> Result.Error None
      | NotConvertibleTrace (Error.Error e) -> Result.Error (Some e)
      | NotConvertibleTrace _ -> assert false
  end ()

let check_eq qeq state u u' =
  if UGraph.check_eq_sort qeq state u u'
  then Result.Ok state
  else Result.Error None

let check_leq qeq state u u' =
  if UGraph.check_leq_sort qeq state u u'
  then Result.Ok state
  else Result.Error None

let checked_sort_cmp_universes qeq = (); fun pb s0 s1 state ->
  match pb with
  | CUMUL -> check_leq qeq state s0 s1
  | CONV -> check_eq qeq state s0 s1

let check_convert_instances qeq = (); fun ~flex:_ u u' state ->
  if UGraph.check_eq_instances qeq state u u' then Result.Ok state
  else Result.Error None

(* general conversion and inference functions *)
let check_inductive_instances qeq = (); fun cv_pb variance u1 u2 state ->
  let qcsts, ucsts = get_cumulativity_constraints cv_pb variance u1 u2 in
  if UVars.QUnifConstraints.is_trivial_gen qeq qcsts && UGraph.check_constraints ucsts state
  then Result.Ok state
  else Result.Error None

let checked_universes_gen qeq =
  { compare_sorts = checked_sort_cmp_universes qeq;
    compare_instances = check_convert_instances qeq;
    compare_cumul_instances = check_inductive_instances qeq; }

let checked_universes = checked_universes_gen Sorts.Quality.equal

let () =
  let conv infos tab a b =
    try
      let box = Empty.abort in
      let state = info_univs infos in
      let qual_equal q1 q2 = CClosure.eq_quality infos q1 q2 in
      let infos = { cnv_inf = infos; cnv_typ = true; lft_tab = tab; rgt_tab = tab; err_ret = box; cnv_cache = None; cnv_xdecl = false } in
      let state', _ = ccnv CONV false infos el_id el_id a b (state, checked_universes_gen qual_equal) in
      assert (state==state');
      true
    with
    | NotConvertible -> false
    | NotConvertibleTrace _ -> assert false
  in
  CClosure.set_conv conv

let gen_conv ~typed cv_pb ?(l2r=false) ?(reds=TransparentState.full) env ?(evars=default_evar_handler env) t1 t2 =
  let univs = Environ.universes env in
  let state = univs in
  let b =
    if cv_pb = CUMUL then leq_constr_univs univs t1 t2
    else eq_constr_univs univs t1 t2
  in
    if b then Result.Ok ()
    else match clos_gen_conv ~typed ~use_cache:true reds cv_pb l2r evars env univs (state, checked_universes) t1 t2 with
    | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare)-> Result.Ok ()
    | Result.Error None -> Result.Error ()
    | Result.Error (Some e) -> Empty.abort e

let conv = gen_conv ~typed:false CONV
let conv_leq = gen_conv ~typed:false CUMUL

let generic_conv cv_pb ~l2r reds env ?(evars=default_evar_handler env) state t1 t2 =
  let graph = Environ.universes env in
  match clos_gen_conv ~typed:false ~use_cache:false reds cv_pb l2r evars env graph state t1 t2 with
  | Result.Ok (s, _) -> Result.Ok s
  | Result.Error e -> Result.Error e

let default_conv cv_pb env t1 t2 =
    gen_conv ~typed:true cv_pb env t1 t2

let default_conv_leq = default_conv CUMUL

type graph_inconsistency = Univ of UGraph.univ_inconsistency | Qual of QGraph.elimination_error
