(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Dyn = Dyn.Make ()

type substitutivity = Dispose | Substitute | Keep | Escape | Anticipate

type object_name = Libnames.full_path * Names.KerName.t

type open_filter =
  | Unfiltered
  | Filtered of CString.Pred.t

type category = string

let known_cats = ref CString.Set.empty

let create_category s =
  let cats' = CString.Set.add s !known_cats in
  if !known_cats == cats' then CErrors.anomaly Pp.(str "create_category called twice on " ++ str s);
  known_cats := cats';
  s

let unfiltered = Unfiltered
let make_filter ~finite cats =
  if CList.is_empty cats then CErrors.anomaly Pp.(str "Libobject.make_filter got an empty list.");
  let cats = List.fold_left
      (fun cats CAst.{v=cat;loc} ->
         if not (CString.Set.mem cat !known_cats)
         then CErrors.user_err ?loc Pp.(str "Unknown import category " ++ str cat ++ str".");
         CString.Pred.add cat cats)
      CString.Pred.empty
      cats
  in
  let cats = if finite then cats else CString.Pred.complement cats in
  Filtered cats

let in_filter ~cat f =
  match cat, f with
  | _, Unfiltered -> true
  | None, Filtered f -> not (CString.Pred.is_finite f)
  | Some cat, Filtered f -> CString.Pred.mem cat f

let filtered_open ?cat f filter i o = if in_filter ~cat filter then f i o

let simple_open ?cat f filter i o = if in_filter ~cat filter && Int.equal i 1 then f o

let filter_eq f1 f2 = match f1, f2 with
  | Unfiltered, Unfiltered -> true
  | Unfiltered, _ | _, Unfiltered -> false
  | Filtered f1, Filtered f2 -> CString.Pred.equal f1 f2

let filter_and f1 f2 = match f1, f2 with
  | Unfiltered, f | f, Unfiltered -> Some f
  | Filtered f1, Filtered f2 ->
    let f = CString.Pred.inter f1 f2 in
    if CString.Pred.is_empty f then None
    else Some (Filtered f)

let filter_or f1 f2 = match f1, f2 with
  | Unfiltered, f | f, Unfiltered -> Unfiltered
  | Filtered f1, Filtered f2 -> Filtered (CString.Pred.union f1 f2)

type ('a,'b,'discharged) object_declaration = {
  object_name : string;
  object_stage : Summary.Stage.t;
  cache_function : 'b -> unit;
  load_function : int -> 'b -> unit;
  open_function : open_filter -> int -> 'b -> unit;
  classify_function : 'a -> substitutivity;
  subst_function :  Mod_subst.substitution * 'a -> 'a;
  discharge_function : 'a -> 'discharged option;
  rebuild_function : 'discharged -> 'a;
}

let default_object ?(stage=Summary.Stage.Interp) s = {
  object_name = s;
  object_stage = stage;
  cache_function = (fun _ -> ());
  load_function = (fun _ _ -> ());
  open_function = (fun _ _ _ -> ());
  subst_function = (fun _ ->
    CErrors.anomaly Pp.(str "The object " ++ str s
      ++ str " does not know how to substitute!"));
  classify_function = (fun _ -> CErrors.anomaly Pp.(str "no classify function for " ++ str s));
  discharge_function = (fun _ -> None);
  rebuild_function = (fun x -> x);
}


(* The suggested object declaration is the following:

   declare_object { (default_object "MY OBJECT") with
       cache_function = fun (sp,a) -> Mytbl.add sp a}

   and the listed functions are only those which definitions actually
   differ from the default.

   This helps introducing new functions in objects.
*)

let ident_subst_function (_,a) = a


type obj = Dyn.t (* persistent dynamic objects *)

(** {6 Substitutive objects}

    - The list of bound identifiers is nonempty only if the objects
      are owned by a functor

    - Then comes either the object segment itself (for interactive
      modules), or a compact way to store derived objects (path to
      a earlier module + substitution).
*)

module ExportObj = struct
  type t = { mpl : (open_filter * Names.ModPath.t) list } [@@unboxed]
end

type ('subs, 'alg, 'keep, 'escape) object_view =
| ModuleObject of Names.Id.t * 'subs
| ModuleTypeObject of Names.Id.t * 'subs
| IncludeObject of 'alg
| KeepObject of Names.Id.t * 'keep
| EscapeObject of Names.Id.t * 'escape
| ExportObject of ExportObj.t
| AtomicObject of obj

type t = (substitutive_objects, algebraic_objects, keep_objects, escape_objects) object_view

and algebraic_objects =
| Objs of t list
| Ref of Names.ModPath.t * Mod_subst.substitution

and substitutive_objects = Names.MBId.t list * algebraic_objects

and keep_objects = { keep_objects : t list }

and escape_objects = { escape_objects : t list }

type object_prefix = {
  obj_path : Libnames.full_path;
  obj_mp  : Names.ModPath.t;
}

let eq_object_prefix op1 op2 =
  Libnames.eq_full_path op1.obj_path op2.obj_path &&
  Names.ModPath.equal op1.obj_mp  op2.obj_mp

type 'a stored_decl = O : ('a, object_prefix * 'a, 'd) object_declaration -> 'a stored_decl

module DynMap = Dyn.Map (struct type 'a t = 'a stored_decl end)

let cache_tab = ref DynMap.empty

let declare_object_gen odecl =
  let na = odecl.object_name in
  let tag = Dyn.create na in
  let () = cache_tab := DynMap.add tag (O odecl) !cache_tab in
  tag

let make_oname { obj_path; obj_mp } id =
  Libnames.add_path_suffix obj_path id, Names.KerName.make obj_mp id

let declare_named_object_full odecl =
  let odecl =
    let oname = make_oname in
    { object_name = odecl.object_name;
      object_stage = odecl.object_stage;
      cache_function = (fun (p, (id, o)) -> odecl.cache_function (oname p id, o));
      load_function = (fun i (p, (id, o)) -> odecl.load_function i (oname p id, o));
      open_function = (fun f i (p, (id, o)) -> odecl.open_function f i (oname p id, o));
      classify_function = (fun (id, o) -> odecl.classify_function o);
      subst_function = (fun (subst, (id, o)) -> id, odecl.subst_function (subst, o));
      discharge_function = (fun (id, o) -> Option.map (fun x -> id, x) (odecl.discharge_function o));
      rebuild_function = Util.on_snd odecl.rebuild_function;
    }
  in
  declare_object_gen odecl

let declare_named_object odecl =
  let tag = declare_named_object_full odecl in
  let infun id v = Dyn.Dyn (tag, (id, v)) in
  infun

let declare_named_object_gen odecl =
  let tag = declare_object_gen odecl in
  let infun v = Dyn.Dyn (tag, v) in
  infun

let declare_object_full odecl =
  let odecl =
    { odecl with
      cache_function = (fun (_,o) -> odecl.cache_function o);
      load_function = (fun i (_,o) -> odecl.load_function i o);
      open_function = (fun f i (_,o) -> odecl.open_function f i o);
    }
  in
  declare_object_gen odecl

let declare_object odecl =
  let tag = declare_object_full odecl in
  let infun v = Dyn.Dyn (tag, v) in
  infun

let cache_object (sp, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.cache_function (sp, v)

let load_object i (sp, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.load_function i (sp, v)

let open_object f i (sp, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.open_function f i (sp, v)

let subst_object (subs, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  Dyn.Dyn (tag, decl.subst_function (subs, v))

let classify_object (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.classify_function v

type discharged_obj = Discharged : 'a Dyn.tag * 'd * ('d -> 'a) -> discharged_obj

let discharge_object (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  match decl.discharge_function v with
  | None -> None
  | Some v -> Some (Discharged (tag, v, decl.rebuild_function))

let rebuild_object (Discharged (tag, v, rebuild)) =
  Dyn.Dyn (tag, rebuild v)

let object_stage (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.object_stage

let object_name (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.object_name

let dump = Dyn.dump

(** binary-equivalence-taiga#841 Review841 G1. A registry, NOT a direct
    module reference: [vernac/declaremods.ml]'s objects-digest partition
    needs to ask "is this atomic object one of the kinds whose semantic
    identity is independently covered elsewhere (so it can be EXCLUDED
    from every digest here), or one whose non-presentational fields need
    a narrower SUBSET-checked digest" for objects declared in
    [vernac/declare.ml] (CONSTANT) and [vernac/declareInd.ml]
    (INDUCTIVE/PRIMPROJS) -- but [vernac/declaremods.ml] cannot reference
    those modules directly (a real `dune build` dependency-cycle error,
    confirmed empirically: `declare.ml`/`declareInd.ml` already sit on a
    path back to `declaremods.ml` through other vernac modules). Each
    declaring module instead registers, at its OWN top-level
    initialization (guaranteed to run before any vernacular command is
    processed, since every one of these modules is linked into the final
    binary regardless), a classifier KEYED BY ITS OWN REGISTERED TAG
    STRING; [cutoff_classify] below dispatches to at most one registered
    classifier per object, by that same tag. The classifier itself still
    does its OWN typed [Dyn.Easy.prj] check before answering (Lean attack
    shape (b), binary-equivalence-taiga#841 Review841 G1 self-audit): a
    tag string match alone only decides WHICH classifier to try, never
    the answer, so an object that merely shares a display name with a
    registered tag but isn't structurally that kind (impossible for
    today's declaration sites, future-proofing only) correctly gets
    [None] here and falls through to the EXACT-equality bucket in the
    caller, never silently dropped from every digest. *)
type cutoff_classification =
  | CutoffExcluded
  | CutoffKeyed of (Names.GlobRef.t * Names.Id.t * Digest.t) list
  (** binary-equivalence-taiga#841 Review841 round 3 (l1/d1) + round 5
      (g1 inductive/constructor coverage, ind1/ind2/forg). One entry per
      target [GlobRef.t] this atomic object concerns (a CONSTANT yields
      exactly one; an INDUCTIVE block yields one for the type plus one
      per constructor, g7ctor/ind1/ind2), each paired with a base digest
      covering ONLY the fields of that declaration NOT independently
      covered elsewhere (for CONSTANT: [cst_locl]/[cst_warn] --
      [cst_kind]/[cst_loc] are presentation-only, the kernel's own
      [iface_table] covers type/body/universes; for INDUCTIVE/
      constructors: a fixed marker, since [ind_names]' own [Loc.t]s are
      the only non-kernel-covered field and those are presentational
      too). The caller ([Declaremods.G1Partition]) combines this with the
      target's EFFECTIVE, resolved implicits/argument-scopes
      (`Impargs.implicits_of_global`/`Notation.find_arguments_scope`,
      queried directly against the supplied [GlobRef.t] -- no [DirPath.t]
      reconstruction needed, unlike the predecessor of this type which
      carried a bare [Id.t]) into ONE per-name entry in a KEYED table,
      checked like the kernel [iface_table] (every name the dependent
      used must still match; an ADDED name is ignored) -- never a flat,
      unkeyed SET (round 3's own finding: an override or reorder of
      Arguments/Implicits for an EXISTING name must still be caught,
      which a "new digest = ignorable addition" SET check cannot do). *)

let cutoff_classifiers : (string, obj -> cutoff_classification option) Hashtbl.t =
  Hashtbl.create 8

let register_cutoff_classifier tag f =
  Hashtbl.replace cutoff_classifiers tag f

let cutoff_classify (obj : obj) : cutoff_classification option =
  match Hashtbl.find_opt cutoff_classifiers (object_name obj) with
  | Some f -> f obj
  | None -> None


let local_object_nodischarge ?stage s ~cache =
  { (default_object ?stage s) with
    cache_function = cache;
    classify_function = (fun _ -> Dispose);
  }

let local_object ?stage s ~cache ~discharge =
  { (local_object_nodischarge ?stage s ~cache) with
    discharge_function = discharge;
  }

let global_object_nodischarge ?cat ?stage s ~cache ~subst =
  { (default_object ?stage s) with
    cache_function = cache;
    open_function = simple_open ?cat cache;
    subst_function = (match subst with
        | None -> fun _ ->
            CErrors.anomaly Pp.(str "The object " ++ str s
              ++ str " does not know how to substitute!")
        | Some subst -> subst;
      );
    classify_function =
      if Option.has_some subst then (fun _ -> Substitute) else (fun _ -> Keep);
  }

let global_object ?cat ?stage s ~cache ~subst ~discharge =
  { (global_object_nodischarge ?cat s ~cache ~subst) with
    discharge_function = discharge }

let superglobal_object_nodischarge ?stage s ~cache ~subst =
  { (default_object ?stage s) with
    load_function = (fun _ x -> cache x);
    cache_function = cache;
    subst_function = (match subst with
        | None -> fun _ ->
            CErrors.anomaly Pp.(str "The object " ++ str s
              ++ str " does not know how to substitute!")
        | Some subst -> subst;
      );
    classify_function =
      if Option.has_some subst then (fun _ -> Substitute) else (fun _ -> Keep);
  }

let superglobal_object ?stage s ~cache ~subst ~discharge =
  { (superglobal_object_nodischarge ?stage s ~cache ~subst) with
    discharge_function = discharge }

type locality = Local | Export | SuperGlobal

let object_with_locality ?stage ?cat s ~cache ~subst ~discharge =
  { (default_object ?stage s) with
    cache_function = (fun (_,v) -> cache v);
    load_function = (fun _ (locality,v) -> match locality with
        | Local -> assert false
        | Export -> ()
        | SuperGlobal -> cache v);
    open_function = simple_open ?cat (fun (locality,v) -> match locality with
        | Local -> assert false
        | Export -> cache v
        | SuperGlobal -> ());
    subst_function = (match subst with
        | None -> fun _ -> assert false (* Keep *)
        | Some subst -> fun (s,(locality,v)) -> locality, subst (s,v);
      );
    classify_function = (fun (locality, _) -> match locality with
        | Local -> Dispose
        | Export | SuperGlobal -> if Option.has_some subst then Substitute else Keep);
    discharge_function =
      (fun (locality,v) -> match locality with
         | Local -> None
         | Export | SuperGlobal ->
           let v = discharge v in
           Some (locality, v));
  }
