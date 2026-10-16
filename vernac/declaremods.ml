(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Declarations
open Mod_declarations
open Entries
open Libnames
open Libobject
open Mod_subst

(** {6 Inlining levels} *)

(** Rigid / flexible module signature *)

type 'a module_signature =
  | Enforce of 'a (** ... : T *)
  | Check of 'a list (** ... <: T1 <: T2, possibly empty *)

(** Which module inline annotations should we honor,
    either None or the ones whose level is less or equal
    to the given integer *)

type inline =
  | NoInline
  | DefaultInline
  | InlineAt of int

let default_inline_level = 100

let { Goptions.get = default_inline_level } =
  Goptions.declare_int_option_and_ref ~key:["Inline";"Level"] ~value:default_inline_level ()

let default_inline_level () = Some (default_inline_level())

let inl2intopt = function
  | NoInline -> None
  | InlineAt i -> Some i
  | DefaultInline -> default_inline_level ()

(** These functions register the visibility of the module and iterates
    through its components. They are called by plenty of module functions *)

let consistency_checks exists dir =
  if exists then
    let _ =
      try Nametab.locate_module (qualid_of_path dir)
      with Not_found ->
        user_err
          (pr_path dir ++ str " should already exist!")
    in
    ()
  else
    if Nametab.exists_module dir then
      user_err
        (pr_path dir ++ str " already exists.")

let rec get_module_path = function
  | MEident mp -> mp
  | MEwith (me,_) -> get_module_path me
  | MEapply (me,_) -> get_module_path me

let type_of_mod mp env = function
  | true -> mod_type (Environ.lookup_module mp env)
  | false -> mod_type (Environ.lookup_modtype mp env)

(** {6 Name management}

    Auxiliary functions to transform full_path and kernel_name given
    by Lib into ModPath.t and DirPath.t needed for modules
*)

let mp_of_kn kn =
  let mp,l = KerName.repr kn in
  MPdot (mp,l)

let pop_path sp =
  path_pop_suffix sp, basename sp

let path_of_file dp =
  match DirPath.repr dp with
  | x :: dp -> make_path (DirPath.make dp) x
  | [] -> CErrors.anomaly Pp.(str "Cannot start library with empty dirpath")

(* Avoid generating a KeepObject for nothing *)
let keep_objects id keep = match keep.keep_objects with
  | [] -> []
  | _ :: _ -> [KeepObject (id, keep)]

let escape_objects id escape = match escape.escape_objects with
  | [] -> []
  | _ :: _ -> [EscapeObject (id, escape)]

(** The [ModActions] abstraction represent operations on modules
    that are specific to a given stage. Two instances are defined below,
    for Synterp and Interp. *)
module type ModActions = sig

  type typexpr
  type env

  val stage : Summary.Stage.t
  val substobjs_table_name : string
  val modobjs_table_name : string

  val enter_module : ModPath.t -> full_path -> int -> unit

  val enter_modtype : ModPath.t -> full_path -> int -> unit

  val open_module : open_filter -> ModPath.t -> full_path -> int -> unit

  module Lib : Lib.StagedLibS

  (** Create the substitution corresponding to some functor applications *)

  val compute_subst : is_mod:bool -> env -> MBId.t list -> ModPath.t -> ModPath.t list -> Entries.inline -> MBId.t list * substitution

end

module SynterpActions : ModActions with
  type env = unit with
  type typexpr = Constrexpr.universe_decl_expr option * Constrexpr.constr_expr =
struct
  type typexpr = Constrexpr.universe_decl_expr option * Constrexpr.constr_expr
  type env = unit
  let stage = Summary.Stage.Synterp
  let substobjs_table_name = "MODULE-SYNTAX-SUBSTOBJS"
  let modobjs_table_name = "MODULE-SYNTAX-OBJS"

  let enter_module obj_mp obj_path i =
    consistency_checks false obj_path;
    Nametab.push_module (Until i) obj_path obj_mp

  let enter_modtype mp sp i =
    if Nametab.exists_modtype sp then
      anomaly (pr_path sp ++ str " already exists.");
    Nametab.push_modtype (Nametab.Until i) sp mp

  let open_module f obj_mp obj_path i =
    consistency_checks true obj_path;
    if in_filter ~cat:None f then Nametab.push_module (Nametab.Exactly i) obj_path obj_mp

  module Lib = Lib.Synterp

  let rec compute_subst () mbids mp_l inl =
    match mbids,mp_l with
      | _,[] -> mbids,empty_subst
      | [],r -> user_err Pp.(str "Application of a functor with too few arguments.")
      | mbid::mbids,mp::mp_l ->
          let mbid_left,subst = compute_subst () mbids mp_l inl in
          mbid_left, join (map_mbid mbid mp (empty_delta_resolver mp)) subst

  let compute_subst ~is_mod () mbids mp1 mp_l inl =
    compute_subst () mbids mp_l inl

end

module InterpActions : ModActions
  with type env = Environ.env
  with type typexpr = Constr.t * UVars.AbstractContext.t option =
struct
  type typexpr = Constr.t * UVars.AbstractContext.t option
  type env = Environ.env
  let stage = Summary.Stage.Interp
  let substobjs_table_name = "MODULE-SUBSTOBJS"
  let modobjs_table_name = "MODULE-OBJS"

  (** {6 Current module type information}

    This information is stored by each [start_modtype] for use
    in a later [end_modtype]. *)

  let enter_module obj_mp obj_path i = ()
  let enter_modtype mp sp i = ()

  let open_module f obj_mp obj_path i = ()

  module Lib = Lib.Interp

  let rec compute_subst env mbids sign mp_l inl =
    match mbids,mp_l with
      | _,[] -> mbids,empty_subst
      | [],r -> user_err Pp.(str "Application of a functor with too few arguments.")
      | mbid::mbids,mp::mp_l ->
          let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
          let mb = Environ.lookup_module mp env in
          let mbid_left,subst = compute_subst env mbids fbody_b mp_l inl in
          let resolver = match mod_global_delta mb with
          | None -> empty_delta_resolver mp
          | Some delta ->
            Modops.inline_delta_resolver env inl mp farg_id farg_b delta
          in
          mbid_left,join (map_mbid mbid mp resolver) subst

  let compute_subst ~is_mod env mbids mp1 mp_l inl =
    let typ = type_of_mod mp1 env is_mod in
    compute_subst env mbids typ mp_l inl

end

type exp_substituted_object = (substitutive_objects, exp_algebraic_objects, Empty.t, Empty.t) object_view

and exp_algebraic_objects = { exp_algebraic_objects : exp_substituted_object list }

(* and exp_substitutive_objects = Names.MBId.t list * exp_algebraic_objects *)

type module_objects =
  { module_prefix : object_prefix;
    module_substituted_objects : exp_substituted_object list;
    module_keep_objects : keep_objects;
    module_escape_objects : escape_objects;
  }

(** The [StagedModS] abstraction describes module operations at a given stage. *)
module type StagedModS = sig

  type typexpr
  type env

  val get_module_sobjs : bool -> env -> Entries.inline -> typexpr module_alg_expr -> substitutive_objects

  val load_keep : int -> full_path -> ModPath.t -> keep_objects -> unit
  val load_escape : int -> full_path -> ModPath.t -> escape_objects -> unit
  val load_module : int -> full_path -> ModPath.t -> substitutive_objects -> unit
  val load_safe_library : DirPath.t -> Mod_declarations.module_body -> unit
  val import_modules : export:Lib.export_flag -> (open_filter * ModPath.t) list -> unit

  val add_leaf : Libobject.t -> unit
  val add_leaves : Libobject.t list -> unit

  val expand_aobjs : Libobject.algebraic_objects -> Libobject.t list

  val get_applications : typexpr module_alg_expr -> ModPath.t * ModPath.t list
  val debug_print_modtab : unit -> Pp.t

  module ModObjs : sig val all : unit -> module_objects ModPath.Map.t end

  val close_section : unit -> unit

end

(** Some utilities about substitutive objects :
    substitution, expansion *)

let sobjs_no_functor (mbids,_) = List.is_empty mbids

let subst_filtered sub (f,mp as x) =
  let mp' = subst_mp sub mp in
  if mp == mp' then x
  else f, mp'

let rec subst_aobjs sub = function
  | Objs o as objs ->
    let o' = subst_objects sub o in
    if o == o' then objs else Objs o'
  | Ref (mp, sub0) as r ->
    let sub0' = join sub0 sub in
    if sub0' == sub0 then r else Ref (mp, sub0')

and subst_sobjs sub (mbids,aobjs as sobjs) =
  let aobjs' = subst_aobjs sub aobjs in
  if aobjs' == aobjs then sobjs else (mbids, aobjs')

and subst_objects subst seg =
  let subst_one node =
    match node with
    | AtomicObject obj ->
      let obj' = Libobject.subst_object (subst,obj) in
      if obj' == obj then node else AtomicObject obj'
    | ModuleObject (id, sobjs) ->
      let sobjs' = subst_sobjs subst sobjs in
      if sobjs' == sobjs then node else ModuleObject (id, sobjs')
    | ModuleTypeObject (id, sobjs) ->
      let sobjs' = subst_sobjs subst sobjs in
      if sobjs' == sobjs then node else ModuleTypeObject (id, sobjs')
    | IncludeObject aobjs ->
      let aobjs' = subst_aobjs subst aobjs in
      if aobjs' == aobjs then node else IncludeObject aobjs'
    | ExportObject { mpl } ->
      let mpl' = List.Smart.map (subst_filtered subst) mpl in
      if mpl'==mpl then node else ExportObject { mpl = mpl' }
    | KeepObject _ | EscapeObject _ -> assert false
  in
  List.Smart.map subst_one seg

(** The [StagedMod] abstraction factors out the code dealing with modules
  that is common to all stages. *)
module StagedMod(Actions : ModActions) = struct

type typexpr = Actions.typexpr
type env = Actions.env

(** ModSubstObjs : a cache of module substitutive objects

   This table is common to modules and module types.
   -  For a Module M:=N, the objects of N will be reloaded
      with M after substitution.
   -  For a Module M:SIG:=..., the module M gets its objects from SIG

   Invariants:
   - A alias (i.e. a module path inside a Ref constructor) should
     never lead to another alias, but rather to a concrete Objs
     constructor.

   We will plug later a handler dealing with missing entries in the
   cache. Such missing entries may come from inner parts of module
   types, which aren't registered by the standard libobject machinery.
*)

module ModSubstObjs :
 sig
   val set : ModPath.t -> substitutive_objects -> unit
   val get : ModPath.t -> substitutive_objects
   val set_missing_handler : (ModPath.t -> substitutive_objects) -> unit
 end =
 struct
   let table =
     Summary.ref ~stage:Actions.stage (ModPath.Map.empty : substitutive_objects ModPath.Map.t)
       ~name:Actions.substobjs_table_name
   let missing_handler = ref (fun mp -> assert false)
   let set_missing_handler f = (missing_handler := f)
   let set mp objs = (table := ModPath.Map.add mp objs !table)
   let get mp =
     try ModPath.Map.find mp !table with Not_found -> !missing_handler mp
 end

let expand_aobjs = function
  | Objs o -> o
  | Ref (mp, sub) ->
    match ModSubstObjs.get mp with
      | (_,Objs o) -> subst_objects sub o
      | _ -> assert false (* Invariant : any alias points to concrete objs *)

let expand_sobjs (_,aobjs) = expand_aobjs aobjs

module Expand =
struct

type exp_object = (substitutive_objects, exp_algebraic_objects, keep_objects, escape_objects) object_view

let exp_substituted_view (obj : exp_substituted_object) : exp_object = match obj with
| (AtomicObject _ | ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | ExportObject _) as o -> o
| EscapeObject (_, o) | KeepObject (_, o) -> Empty.abort o

let keep_view (obj : Libobject.t) : exp_object = match obj with
| (AtomicObject _ | KeepObject _) as o -> o
| ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | ExportObject _ | EscapeObject _ ->
  assert false (** keep objects only contain atomic / keep *)

let escape_view (obj : Libobject.t) : exp_object = match obj with
| (AtomicObject _ | EscapeObject _) as o -> o
| ModuleObject _ | ModuleTypeObject _ | IncludeObject _ | ExportObject _ | KeepObject _ ->
  assert false (** escape objects only contain atomic / escape *)

let rec substituted_object_view (obj : Libobject.t) : exp_substituted_object = match obj with
| (AtomicObject _ | ModuleObject _ | ModuleTypeObject _ | ExportObject _) as o -> o
| IncludeObject aobjs ->
  let aobjs = expand_aobjs aobjs in
  IncludeObject { exp_algebraic_objects = List.map substituted_object_view aobjs }
| EscapeObject _ | KeepObject _ ->
  (* forbidden in substitutive objects *)
  assert false

let object_view (obj : Libobject.t) : exp_object = match obj with
| (AtomicObject _ | EscapeObject _ | ModuleObject _ | ModuleTypeObject _ | ExportObject _ | KeepObject _) as o -> o
| IncludeObject aobjs ->
  let aobjs = expand_aobjs aobjs in
  IncludeObject { exp_algebraic_objects = List.map substituted_object_view aobjs }

end


(** {6 ModObjs : a cache of module objects}

   For each module, we also store a cache of
   "prefix", "substituted objects", "keep objects".
   This is used for instance to implement the "Import" command.

   substituted objects :
     roughly the objects above after the substitution - we need to
     keep them to call open_object when the module is opened (imported)

   keep objects :
     The list of non-substitutive objects - as above, for each of
     them we will call open_object when the module is opened

   (Some) Invariants:
   * If the module is a functor, it won't appear in this cache.

   * Module objects in substitutive_objects part have empty substituted
     objects.

   * Modules which where created with Module M:=mexpr or with
     Module M:SIG. ... End M. have the keep list empty.
*)

module ModObjs :
 sig
   val set : ModPath.t -> module_objects -> unit
   val get : ModPath.t -> module_objects (* may raise Not_found *)
   val all : unit -> module_objects ModPath.Map.t
 end =
 struct
   let table =
     Summary.ref ~stage:Actions.stage (ModPath.Map.empty : module_objects ModPath.Map.t)
       ~name:Actions.modobjs_table_name
   let set mp objs = (table := ModPath.Map.add mp objs !table)
   let get mp = ModPath.Map.find mp !table
   let all () = !table
 end

(** {6 SafeLibs : the set of libraries loaded through [Require (safe)]}

   A [Require (safe)] library is imported in the kernel but no libobject
   replay is performed, so it has no entry in [ModObjs] and cannot be
   imported through the usual object-collection machinery. We record the
   set of such libraries (per stage) so that [Import]/[Export] of a
   safe-loaded library can push names directly by walking the kernel
   module structure instead. *)

module SafeLibs :
 sig
   val register : DirPath.t -> Mod_declarations.module_body -> unit
   val find : DirPath.t -> Mod_declarations.module_body option
 end =
 struct
   let table =
     Summary.ref ~stage:Actions.stage (DirPath.Map.empty : Mod_declarations.module_body DirPath.Map.t)
       ~name:(Actions.modobjs_table_name ^ "-SAFE-LIBS")
   let register dp mb = (table := DirPath.Map.add dp mb !table)
   let find dp = DirPath.Map.find_opt dp !table
 end

(** {6 Name pushing for [Require (safe)] libraries}

   These walk the kernel module structure of a safe-loaded library and
   push short names into the nametab. The walk carries the module-nesting
   depth [i] (the library module is depth 1); an object directly inside a
   module at depth [i] has [i] path components stripped from its full name,
   hence a "[Until]-index" of [i+1].

   The visibility to push at is computed by [vis] from that [Until]-index:
   - at load time, [Until k], so only fully-qualified(-ish) names are
     visible (as a plain [Require (safe)] should);
   - at import time, [Exactly (k-1)], matching the depth [open_object]
     would use for the same object during a normal [Import] (a top-level
     constant of the library becomes visible under its bare name). The top
     library module name itself ([Until]-index 1) is not (re-)pushed on
     import, mirroring normal library import which never re-pushes it.

   Constants/inductives/constructors exist only at the [Interp] stage;
   module and module type short names at [Synterp]. *)

let safe_require_mind_names vis sp mind mib =
  mib.Declarations.mind_packets |> Array.iteri @@ fun ind (mip:Declarations.one_inductive_body) ->
  let ind = (mind, ind) in
  let () = Option.iter (fun vis -> Nametab.push vis (Libnames.add_path_suffix sp mip.mind_typename) (GlobRef.IndRef ind)) vis in
  mip.mind_consnames |> Array.iteri @@ fun ctor cna ->
  Option.iter (fun vis -> Nametab.push vis (Libnames.add_path_suffix sp cna) (GlobRef.ConstructRef (ind, ctor+1))) vis

let rec safe_require_mod_names ~vis i sp mp mb =
  let () = match Actions.stage with
    | Summary.Stage.Synterp -> Option.iter (fun v -> Nametab.push_module v sp mp) (vis i)
    | Interp -> ()
  in
  match Mod_declarations.mod_type mb with
  | MoreFunctor _ -> ()
  | NoFunctor contents ->
    contents |> List.iter @@ fun (lab, contents) ->
    match contents with
    | Declarations.SFBrules _ ->
      ()
    | SFBconst _ ->
      begin match Actions.stage with
      | Synterp -> ()
      | Interp ->
        let kn = Global.constant_of_delta_kn (KerName.make mp lab) in
        let sp = Libnames.add_path_suffix sp lab in
        Option.iter (fun v -> Nametab.push v sp (GlobRef.ConstRef kn)) (vis (i+1))
      end
    | SFBmind mib ->
      begin match Actions.stage with
      | Synterp -> ()
      | Interp ->
        let mind = Global.mind_of_delta_kn (KerName.make mp lab) in
        safe_require_mind_names (vis (i+1)) sp mind mib
      end
    | SFBmodtype _ ->
      begin match Actions.stage with
      | Synterp ->
        let mp = ModPath.MPdot (mp, lab) in
        let sp = Libnames.add_path_suffix sp lab in
        Option.iter (fun v -> Nametab.push_modtype v sp mp) (vis (i+1))
      | Interp -> ()
      end
    | SFBmodule mb ->
      safe_require_mod_names ~vis (i+1) (Libnames.add_path_suffix sp lab) (MPdot (mp,lab)) mb

let safe_require_names ~vis dp mb =
  let mp = ModPath.MPfile dp in
  let sp = Libnames.make_path0 dp in
  safe_require_mod_names ~vis 1 sp mp mb

(** Push the fully-qualified-only ([Until]) names of a safe-loaded library
    and record it as safe-loaded (so a later [Import]/[Export] can find its
    module structure). [mb] is the kernel module body of the library, which
    at the [Synterp] stage cannot be recovered from the kernel (it is not
    imported there) and so is supplied by the caller. *)
let load_safe_library dp mb =
  safe_require_names ~vis:(fun k -> Some (Nametab.Until k)) dp mb;
  SafeLibs.register dp mb

(** Push the short ([Exactly]) names of a safe-loaded library, as done by
    [Import]. Known divergence from a real [Import]: the kernel structure
    carries no vernacular locality info ([ImportNeedQualified] from a
    [Local Definition] lives only in libobjects), so this may expose short
    names that a real [Import] would keep qualified-only. *)
let import_safe_library dp mb =
  safe_require_names ~vis:(fun k -> if k <= 1 then None else Some (Nametab.Exactly (k-1))) dp mb

 open Expand

(** {6 Declaration of module substitutive objects} *)

(** Nota: Interactive modules and module types cannot be recached!
    This used to be checked here via a flag along the substobjs. *)

(** {6 Declaration of module type substitutive objects} *)

(** Nota: Interactive modules and module types cannot be recached!
    This used to be checked more properly here. *)

let load_modtype i sp mp sobjs =
  Actions.enter_modtype mp sp i;
  ModSubstObjs.set mp sobjs

(** {6 Declaration of substitutive objects for Include} *)

let rec load_object : type a. (a -> exp_object) -> int -> object_prefix * a -> unit = fun view i (prefix, obj) ->
  match view obj with
  | AtomicObject o -> Libobject.load_object i (prefix, o)
  | ModuleObject (id,sobjs) ->
    let sp, kn = Lib.make_oname prefix id in
    load_module i sp (mp_of_kn kn) sobjs
  | ModuleTypeObject (id,sobjs) ->
    let name = Lib.make_oname prefix id in
    let (sp,kn) = name in
    load_modtype i sp (mp_of_kn kn) sobjs
  | IncludeObject aobjs ->
    load_include i (prefix, aobjs)
  | ExportObject _ -> ()
  | KeepObject (id,objs) ->
    let sp, kn = Lib.make_oname prefix id in
    load_keep i sp (mp_of_kn kn) objs
  | EscapeObject (id,objs) ->
    let sp, kn = Lib.make_oname prefix id in
    load_escape i sp (mp_of_kn kn) objs

and load_objects : type a. (a -> exp_object) -> int -> object_prefix -> a list -> unit = fun view i prefix objs ->
  List.iter (fun obj -> load_object view i (prefix, obj)) objs

and load_include i (prefix, aobjs) =
  load_objects exp_substituted_view i prefix aobjs.exp_algebraic_objects

and load_keep i obj_path obj_mp kobjs =
  (* Invariant : seg isn't empty *)
  let prefix = { obj_path ; obj_mp; } in
  let modobjs =
    try ModObjs.get obj_mp
    with Not_found -> assert false (* a substobjs should already be loaded *)
  in
  assert (eq_object_prefix modobjs.module_prefix prefix);
  assert (List.is_empty modobjs.module_keep_objects.keep_objects);
  ModObjs.set obj_mp { modobjs with module_keep_objects = kobjs };
  load_objects keep_view (i+1) prefix kobjs.keep_objects

and load_escape i obj_path obj_mp eobjs =
  (* Invariant : seg isn't empty *)
  let prefix = { obj_path ; obj_mp; } in
  let modobjs =
    try ModObjs.get obj_mp
    with Not_found ->
      (* escape objects can exist even if there is no corresponding real module *)
      { module_prefix = prefix;
        module_substituted_objects = [];
        module_keep_objects = { keep_objects = [] };
        module_escape_objects = { escape_objects = [] };
      }
  in
  assert (eq_object_prefix modobjs.module_prefix prefix);
  assert (List.is_empty modobjs.module_escape_objects.escape_objects);
  ModObjs.set obj_mp { modobjs with module_escape_objects = eobjs };
  load_objects escape_view (i+1) prefix eobjs.escape_objects

and load_module i obj_path obj_mp sobjs =
  let prefix = { obj_path ; obj_mp; } in
  Actions.enter_module obj_mp obj_path i;
  ModSubstObjs.set obj_mp sobjs;
  (* If we're not a functor, let's iter on the internal components *)
  if sobjs_no_functor sobjs then begin
    let objs = expand_sobjs sobjs in
    let objs = List.map substituted_object_view objs in
    let module_objects =
      { module_prefix = prefix;
        module_substituted_objects = objs;
        module_keep_objects = { keep_objects = [] };
        module_escape_objects = { escape_objects = [] };
      }
    in
    ModObjs.set obj_mp module_objects;
    load_objects exp_substituted_view (i+1) prefix objs
  end

(** {6 Implementation of Import and Export commands} *)

let mark_object f obj (exports,acc) =
  (exports, (f,obj)::acc)

let rec collect_module (f,mp) acc =
  (* A [Require (safe)] library has no [ModObjs] entry; importing it pushes
     short names directly by walking the kernel structure. This must take
     precedence over the (missing) [ModObjs] lookup. Filters are ignored:
     there are no libobjects/categories to filter on. *)
  match (match mp with MPfile dp -> Option.map (fun mb -> (dp, mb)) (SafeLibs.find dp) | _ -> None) with
  | Some (dp, mb) -> import_safe_library dp mb; acc
  | None ->
  try
    (* May raise Not_found for unknown module and for functors *)
    let modobjs = ModObjs.get mp in
    let prefix = modobjs.module_prefix in
    let acc = collect_objects escape_view f 1 prefix modobjs.module_escape_objects.escape_objects acc in
    let acc = collect_objects keep_view f 1 prefix modobjs.module_keep_objects.keep_objects acc in
    collect_objects exp_substituted_view f 1 prefix modobjs.module_substituted_objects acc
  with Not_found when Actions.stage = Summary.Stage.Synterp ->
    acc

and collect_object : type a. (a -> exp_object) -> _ -> _ -> _ -> a -> _ -> _ = fun view f i prefix obj acc ->
  match view obj with
  | ExportObject { mpl } -> collect_exports f i mpl acc
  | (AtomicObject _ | IncludeObject _ | KeepObject _ | EscapeObject _
  | ModuleObject _ | ModuleTypeObject _) as obj -> mark_object f (prefix,obj) acc

and collect_objects : type a. (a -> exp_object) -> _ -> _ -> _ -> a list -> _ = fun view f i prefix objs acc ->
  List.fold_left (fun acc obj -> collect_object view f i prefix obj acc)
    acc
    (List.rev objs)

and collect_export f (f',mp) (exports,objs as acc) =
  match filter_and f f' with
  | None -> acc
  | Some f ->
    let exports' = ModPath.Map.update mp (function
        | None -> Some f
        | Some f0 ->
          let f' = filter_or f f0 in
          if filter_eq f' f0 then Some f0 else Some f')
        exports
    in
    (* If the map doesn't change there is nothing new to export. *)
    if exports == exports' then acc
    else
      collect_module (f,mp) (exports', objs)


and collect_exports f i mpl acc =
  if Int.equal i 1 then
    List.fold_left (fun acc fmp -> collect_export f fmp acc) acc (List.rev mpl)
  else acc

let collect_modules mpl =
  List.fold_left (fun acc fmp -> collect_module fmp acc)  (ModPath.Map.empty, []) (List.rev mpl)

let open_modtype i ((sp,kn),_) =
  let mp = mp_of_kn kn in
  let mp' =
    try Nametab.locate_modtype (qualid_of_path sp)
    with Not_found ->
      anomaly (pr_path sp ++ str " should already exist!");
  in
  assert (ModPath.equal mp mp');
  Nametab.push_modtype (Nametab.Exactly i) sp mp

let rec open_object : type a. (a -> exp_object) -> _ -> _ -> _ * a -> _ = fun view f i (prefix, obj) ->
  match view obj with
  | AtomicObject o -> Libobject.open_object f i (prefix, o)
  | ModuleObject (id,sobjs) ->
    let sp, kn = Lib.make_oname prefix id in
    let mp = mp_of_kn kn in
    open_module f i sp mp sobjs
  | ModuleTypeObject (id,sobjs) ->
    let name = Lib.make_oname prefix id in
    open_modtype i (name, sobjs)
  | IncludeObject aobjs ->
    open_include f i (prefix, aobjs)
  | ExportObject { mpl } -> open_export f i mpl
  | KeepObject (id,objs) ->
    let name = Lib.make_oname prefix id in
    open_keep f i (name, objs)
  | EscapeObject (id,objs) ->
    let name = Lib.make_oname prefix id in
    open_escape f i (name, objs)

and open_module f i obj_path obj_mp sobjs =
  Actions.open_module f obj_mp obj_path i;
  (* If we're not a functor, let's iter on the internal components *)
  if sobjs_no_functor sobjs then begin
    let modobjs = ModObjs.get obj_mp in
    open_objects exp_substituted_view f (i+1) modobjs.module_prefix modobjs.module_substituted_objects
  end

and open_objects : type a. (a -> exp_object) -> _ -> _ -> _ -> a list -> _ = fun view f i prefix objs ->
  List.iter (fun obj -> open_object view f i (prefix, obj)) objs

and open_include f i (prefix, aobjs) =
  open_objects exp_substituted_view f i prefix aobjs.exp_algebraic_objects

and open_export f i mpl =
  let _,objs = collect_exports f i mpl (ModPath.Map.empty, []) in
  List.iter (fun (f,o) -> open_object (fun x -> x) f 1 o) objs

and open_keep f i ((sp,kn),kobjs) =
  let obj_mp = mp_of_kn kn in
  let prefix = { obj_path=sp; obj_mp; } in
  open_objects keep_view f (i+1) prefix kobjs.keep_objects

and open_escape f i ((sp,kn),kobjs) =
  let obj_mp = mp_of_kn kn in
  let prefix = { obj_path=sp; obj_mp; } in
  open_objects escape_view f (i+1) prefix kobjs.escape_objects

let cache_include (prefix, aobjs) =
  let o = expand_aobjs aobjs in
  let o = List.map substituted_object_view o in
  load_objects exp_substituted_view 1 prefix o;
  open_objects exp_substituted_view unfiltered 1 prefix o

let cache_object (prefix, obj) =
  match obj with
  | AtomicObject o -> Libobject.cache_object (prefix, o)
  | ModuleObject _ -> load_object object_view 1 (prefix,obj)
  | ModuleTypeObject _ -> load_object object_view 0 (prefix,obj)
  | IncludeObject aobjs -> cache_include (prefix, aobjs)
  | ExportObject { mpl } -> anomaly Pp.(str "Export should not be cached")
  | KeepObject _ | EscapeObject _ -> anomaly (Pp.str "This module should not be cached!")

(* Adding operations with containers *)

let add_leaf_entry =
  match Actions.stage with
  | Summary.Stage.Synterp -> Lib.Synterp.add_leaf_entry
  | Summary.Stage.Interp -> Lib.Interp.add_leaf_entry

let add_leaf obj =
  cache_object (Lib.prefix (),obj);
  add_leaf_entry obj

let add_leaves objs =
  let add_obj obj =
    add_leaf_entry obj;
    load_object object_view 1 (Lib.prefix (),obj)
  in
  List.iter add_obj objs

let import_modules ~export mpl =
  let _,objs = collect_modules mpl in
  List.iter (fun (f,o) -> open_object (fun x -> x) f 1 o) objs;
  match export with
  | Lib.Import -> ()
  | Lib.Export ->
    let entry = ExportObject { mpl } in
    add_leaf_entry entry

(** {6 Handler for missing entries in ModSubstObjs} *)

(** Since the inner of Module Types are not added by default to
    the ModSubstObjs table, we compensate this by explicit traversal
    of Module Types inner objects when needed. Quite a hack... *)

let mp_id mp id = MPdot (mp, id)

let rec register_mod_objs mp obj = match obj with
  | ModuleObject (id,sobjs) -> ModSubstObjs.set (mp_id mp id) sobjs
  | ModuleTypeObject (id,sobjs) -> ModSubstObjs.set (mp_id mp id) sobjs
  | IncludeObject aobjs ->
    List.iter (register_mod_objs mp) (expand_aobjs aobjs)
  | _ -> ()

let handle_missing_substobjs mp = match mp with
  | MPdot (mp',l) ->
    let objs = expand_sobjs (ModSubstObjs.get mp') in
    List.iter (register_mod_objs mp') objs;
    ModSubstObjs.get mp
  | _ ->
    assert false (* Only inner parts of module types should be missing *)

let () = ModSubstObjs.set_missing_handler handle_missing_substobjs



(** {6 From module expression to substitutive objects} *)

(** Turn a chain of [MSEapply] into the head ModPath.t and the
    list of ModPath.t parameters (deepest param coming first).
    The left part of a [MSEapply] must be either [MSEident] or
    another [MSEapply]. *)

let get_applications mexpr =
  let rec get params = function
    | MEident mp -> mp, params
    | MEapply (fexpr, mp) -> get (mp::params) fexpr
    | MEwith _ -> user_err Pp.(str "Non-atomic functor application.")
  in get [] mexpr

(** Create the objects of a "with Module" structure. *)

let rec replace_module_object idl mp0 objs0 mp1 objs1 =
  match idl, objs0 with
  | _,[] -> []
  | id::idl,(ModuleObject (id', sobjs))::tail when Id.equal id id' ->
    begin
      let mp_id = MPdot(mp0, id) in
      let objs = match idl with
        | [] -> subst_objects (map_mp mp1 mp_id (empty_delta_resolver mp_id)) objs1
        | _ ->
          let objs_id = expand_sobjs sobjs in
          replace_module_object idl mp_id objs_id mp1 objs1
      in
      (ModuleObject (id, ([], Objs objs)))::tail
    end
  | idl,lobj::tail -> lobj::replace_module_object idl mp0 tail mp1 objs1

(** Substitutive objects of a module expression (or module type) *)

let rec get_module_sobjs is_mod env inl = function
  | MEident mp ->
    begin match ModSubstObjs.get mp with
    | (mbids,Objs _) when not (ModPath.is_bound mp) ->
      (mbids,Ref (mp, empty_subst)) (* we create an alias *)
    | sobjs -> sobjs
    end
  | MEwith (mty, WithDef _) -> get_module_sobjs is_mod env inl mty
  | MEwith (mty, WithMod (idl,mp1)) ->
    assert (not is_mod);
    let sobjs0 = get_module_sobjs is_mod env inl mty in
    if not (sobjs_no_functor sobjs0) then
      user_err Pp.(str "Illegal use of a functor.");
    (* For now, we expand everything, to be safe *)
    let mp0 = get_module_path mty in
    let objs0 = expand_sobjs sobjs0 in
    let objs1 = expand_sobjs (ModSubstObjs.get mp1) in
    ([], Objs (replace_module_object idl mp0 objs0 mp1 objs1))
  | MEapply _ as me ->
    let mp1, mp_l = get_applications me in
    let mbids, aobjs = get_module_sobjs is_mod env inl (MEident mp1) in
    let mbids_left,subst = Actions.compute_subst ~is_mod env mbids mp1 mp_l inl in
    (mbids_left, subst_aobjs subst aobjs)

let debug_print_modtab () =
  let pr_seg = function
    | 0 -> str "[]"
    | l -> str "[." ++ int l ++ str ".]"
  in
  let pr_modinfo mp modobjs s =
    let objs = List.length modobjs.module_substituted_objects + List.length modobjs.module_keep_objects.keep_objects in
    s ++ str (ModPath.to_string mp) ++ spc () ++ pr_seg objs
  in
  let modules = ModPath.Map.fold pr_modinfo (ModObjs.all ()) (mt ()) in
  hov 0 modules

let add_discharged_item : Lib.discharged_item -> unit = function
  | DischargedExport { mpl } -> import_modules ~export:Export mpl
  | DischargedLeaf o -> Lib.add_discharged_leaf o

let close_section () =
  let objs = Actions.Lib.close_section () in
  List.iter add_discharged_item objs

end

module SynterpVisitor : StagedModS
  with type env = SynterpActions.env
  with type typexpr = Constrexpr.universe_decl_expr option * Constrexpr.constr_expr
  = StagedMod(SynterpActions)

module InterpVisitor : StagedModS
  with type env = InterpActions.env
  with type typexpr = Constr.t * UVars.AbstractContext.t option
 = StagedMod(InterpActions)

(** {6 Modules : start, end, declare} *)

type current_module_syntax_info = {
  cur_mp : ModPath.t;
  cur_typ : ((Constrexpr.universe_decl_expr option * Constrexpr.constr_expr) module_alg_expr * int option) option;
  cur_mbids : MBId.t list;
}

let default_module_syntax_info mp = { cur_mp = mp; cur_typ = None; cur_mbids = [] }

let openmod_syntax_info =
  Summary.ref None ~stage:Summary.Stage.Synterp ~name:"MODULE-SYNTAX-INFO"

(** {6 Current module information}

    This information is stored by each [start_module] for use
    in a later [end_module]. *)

type current_module_info = {
  cur_typ : (module_struct_entry * int option) option; (** type via ":" *)
  cur_typs : module_type_body list (** types via "<:" *)
}

let default_module_info = { cur_typ = None; cur_typs = [] }

let openmod_info = Summary.ref default_module_info ~name:"MODULE-INFO"

let start_library dir =
  let mp = Global.start_library dir in
  openmod_info := default_module_info;
  openmod_syntax_info := Some (default_module_syntax_info mp);
  Lib.start_compilation dir mp

let set_openmod_syntax_info info = match !openmod_syntax_info with
  | None -> anomaly Pp.(str "bad init of openmod_syntax_info")
  | Some _ -> openmod_syntax_info := Some info

let openmod_syntax_info () = match !openmod_syntax_info with
  | None -> anomaly Pp.(str "missing init of openmod_syntax_info")
  | Some v -> v

let vm_state =
  (* VM bytecode is not needed here *)
  let vm_handler _ _ _ () = (), None in
  ((), { Mod_typing.vm_handler })

module RawModOps = struct

module Synterp = struct

let build_subtypes mtys =
  List.map
    (fun (m,ann) ->
       let inl = inl2intopt ann in
       let mte, base, kind = Modintern.intern_module_ast Modintern.ModType m in
       (mte, base, kind, inl))
  mtys

let intern_arg (idl,(typ,ann)) =
  let inl = inl2intopt ann in
  let lib_dir = Lib.library_dp() in
  let (mty, base, kind) = Modintern.intern_module_ast Modintern.ModType typ in
  let sobjs = SynterpVisitor.get_module_sobjs false () inl mty in
  let mp0 = get_module_path mty in
  let map {CAst.v=id} =
    let sp = Libnames.make_path DirPath.empty id in
    let mbid = MBId.make lib_dir id in
    let mp = MPbound mbid in
    (* We can use an empty delta resolver because we load only syntax objects *)
    let sobjs = subst_sobjs (map_mp mp0 mp (empty_delta_resolver mp)) sobjs in
    SynterpVisitor.load_module 1 sp mp sobjs;
    mbid
  in
  List.map map idl, (mty, base, kind, inl)

let intern_args params =
  List.map intern_arg params

let start_module_core id args res =
  (* Loads the parsing objects in arguments *)
  let args = intern_args args in
  let mbids = List.flatten @@ List.map (fun (mbidl,_) -> mbidl) args in
  let res_entry_o, sign = match res with
    | Enforce (res,ann) ->
        let inl = inl2intopt ann in
        let (mte, base, kind) = Modintern.intern_module_ast Modintern.ModType res in
        Some (mte, inl), Enforce (mte, base, kind, inl)
    | Check resl -> None, Check (build_subtypes resl)
  in
  let mp = ModPath.MPdot((openmod_syntax_info ()).cur_mp, id) in
  mp, res_entry_o, mbids, sign, args

let start_module export id args res =
  let () = if Option.has_some export && not (CList.is_empty args)
    then user_err Pp.(str "Cannot import functors.")
  in
  let fs = Summary.Synterp.freeze_summaries () in
  let mp, res_entry_o, mbids, sign, args = start_module_core id args res in
  set_openmod_syntax_info { cur_mp = mp; cur_typ = res_entry_o; cur_mbids = mbids };
  let prefix = Lib.Synterp.start_module export id mp fs in
  Nametab.(push_dir (Until 1) (prefix.obj_path) (GlobDirRef.DirOpenModule prefix.obj_mp));
  mp, args, sign

let end_module_core id (m_info : current_module_syntax_info) objects fs =
  let {Lib.substobjs = substitute; keepobjs = keep; escapeobjs = escape; anticipateobjs = special; } = objects in

  (* For sealed modules, we use the substitutive objects of their signatures *)
  let sobjs0, keep = match m_info.cur_typ with
    | None -> ([], Objs substitute), keep
    | Some (mty, inline) ->
      SynterpVisitor.get_module_sobjs false () inline mty, { keep_objects = [] }
  in
  Summary.Synterp.unfreeze_summaries fs;
  let sobjs = let (ms,objs) = sobjs0 in (m_info.cur_mbids@ms,objs) in

  (* We substitute objects if the module is sealed by a signature *)
  let sobjs =
    match m_info.cur_typ with
      | None -> sobjs
      | Some (mty, _) ->
        subst_sobjs (map_mp (get_module_path mty) m_info.cur_mp (empty_delta_resolver m_info.cur_mp)) sobjs
  in
  let node = ModuleObject (id,sobjs) in
  (* We add the keep objects, if any, and if this isn't a functor *)
  let keep = if not (CList.is_empty m_info.cur_mbids) then [] else keep_objects id keep in
  let escape = escape_objects id escape in
  let objects = special@[node]@keep@escape in

  m_info.cur_mp, objects

let end_module () =
  let oldprefix,fs,objects = Lib.Synterp.end_module () in
  let m_info = openmod_syntax_info () in
  let olddp, id = pop_path oldprefix.obj_path in
  let mp,objects = end_module_core id m_info objects fs in

  let () = SynterpVisitor.add_leaves objects in

  assert (eq_full_path (Lib.prefix()).obj_path olddp);
  mp

let get_functor_sobjs is_mod inl (mbids,mexpr) =
  let (mbids0, aobjs) = SynterpVisitor.get_module_sobjs is_mod () inl mexpr in
  (mbids @ mbids0, aobjs)

let declare_module id args res mexpr_o =
  let fs = Summary.Synterp.freeze_summaries () in
  (* We simulate the beginning of an interactive module,
     then we adds the module parameters to the global env. *)
  let mp = ModPath.MPdot((openmod_syntax_info ()).cur_mp, id) in
  let args = intern_args args in
  let mbids = List.flatten @@ List.map fst args in
  let mty_entry_o = match res with
    | Enforce (mty,ann) ->
        let inl = inl2intopt ann in
        let (mte, base, kind) = Modintern.intern_module_ast Modintern.ModType mty in
        Enforce (mte, base, kind, inl)
    | Check mtys ->
      Check (build_subtypes mtys)
  in
  let mexpr_entry_o = match mexpr_o with
    | None -> None
    | Some (mexpr,ann) ->
      let (mte, base, kind) = Modintern.intern_module_ast Modintern.Module mexpr in
      Some (mte, base, kind, inl2intopt ann)
  in
  let sobjs, mp0 = match mexpr_entry_o, mty_entry_o with
    | None, Check _ -> assert false (* No body, no type ... *)
    | _, Enforce (typ,_,_,inl_res) -> get_functor_sobjs false inl_res (mbids,typ), get_module_path typ
    | Some (body, _, _, inl_expr), Check _ ->
      get_functor_sobjs true inl_expr (mbids,body), get_module_path body
  in
  (* Undo the simulated interactive building of the module
     and declare the module as a whole *)
  Summary.Synterp.unfreeze_summaries fs;

  (* We can use an empty delta resolver on syntax objects *)
  let sobjs = subst_sobjs (map_mp mp0 mp (empty_delta_resolver mp)) sobjs in
  ignore (SynterpVisitor.add_leaf (ModuleObject (id,sobjs)));
  mp, args, mexpr_entry_o, mty_entry_o

end

module Interp = struct

(** {6 Auxiliary functions concerning subtyping checks} *)

let check_sub env mp sub_mtb_l =
  let fold sub_mtb (cst, env) =
    let state = ((Environ.universes env, cst), Reductionops.inferred_universes) in
    let ugraph, cst = Subtyping.check_subtypes ~direct:true state env mp mp sub_mtb in
    (cst, Environ.set_universes ugraph env)
  in
  let cst, _ = List.fold_right fold sub_mtb_l (Univ.UnivConstraints.empty, env) in
  Global.add_univ_constraints cst

(** This function checks if the type calculated for the module [mp] is
    a "<:"-like subtype of all signatures in [sub_mtb_l]. Uses only
    the global environment. *)

let check_subtypes mp sub_mtb_l =
  check_sub (Global.env ()) mp sub_mtb_l

(** Same for module type [mp] *)

let check_subtypes_mt mp sub_mtb_l =
  let mtb =
    try Global.lookup_modtype mp with Not_found -> assert false
  in
  let env = Modops.add_module mp (module_body_of_type mtb) (Global.env ()) in
  check_sub env mp sub_mtb_l

let current_modresolver () =
  Safe_typing.delta_of_senv @@ Global.safe_env ()

let current_struct () =
  let struc = Safe_typing.structure_body_of_safe_env @@ Global.safe_env () in
  NoFunctor (List.rev struc)

(** Prepare the module type list for check of subtypes *)

let build_subtypes env mp args mtys =
  let (ctx, ans) = List.fold_left_map
    (fun ctx (mte,base,kind,inl) ->
      let mte, ctx' = Modintern.interp_module_ast env Modintern.ModType base mte in
      let env = Environ.push_context_set  ~strict:true ctx' env in
      let ctx = Univ.ContextSet.union ctx ctx' in
      let state = ((Environ.universes env, Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
      (* functor arguments are already part of the env, we compute the type
         and requantify over them *)
      let mtb, (_, cst), _ = Mod_typing.translate_modtype state vm_state env mp inl ([], mte) in
      let fold (mbid, mtb, _, _) accu =
        MoreFunctor (mbid, mtb, accu)
      in
      (* XXX: parameters will be rechecked for subtyping, even though we
         statically know they are the same as the ones of the ambient
         module *)
      let sign = List.fold_right fold args (mod_type mtb) in
      let mtb = make_module_type sign (mod_delta mtb) in
      let ctx = Univ.ContextSet.add_constraints cst ctx in
      ctx, mtb)
    Univ.ContextSet.empty mtys
  in
  (ans, ctx)

(** Process a declaration of functor parameter(s) (Id1 .. Idn : Typ)
    i.e. possibly multiple names with the same module type.
    Global environment is updated on the fly.
    Objects in these parameters are also loaded.
    Output is accumulated on top of [acc] (in reverse order). *)

let intern_arg (acc, cst) (mbidl,(mty, base, kind, inl)) =
  let env = Global.env() in
  let (mty, cst') = Modintern.interp_module_ast env kind base mty in
  let () = Global.push_context_set cst' in
  let () =
    let state = ((Global.universes (), Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
    let _, (_, cst), _ = Mod_typing.translate_modtype state vm_state (Global.env ()) base inl ([], mty) in
    Global.add_univ_constraints cst
  in
  let env = Global.env () in
  let sobjs = InterpVisitor.get_module_sobjs false env inl mty in
  let mp0 = get_module_path mty in
  let fold acc mbid =
    let id = MBId.to_id mbid in
    let sp = Libnames.make_path DirPath.empty id in
    let mp = MPbound mbid in
    let mtb = Global.add_module_parameter mbid mty inl in
    let resolver = mod_delta mtb in
    let sobjs = subst_sobjs (map_mp mp0 mp resolver) sobjs in
    InterpVisitor.load_module 1 sp mp sobjs;
    (mbid, mtb, mty, inl) :: acc
  in
  let acc = List.fold_left fold acc mbidl in
  (acc, Univ.ContextSet.union cst cst')


(** Process a list of declarations of functor parameters
    (Id11 .. Id1n : Typ1)..(Idk1 .. Idkm : Typk)
    Global environment is updated on the fly.
    The calls to [interp_modast] should be interleaved with these
    env updates, otherwise some "with Definition" could be rejected.
    Returns a list of mbids and entries (in reversed order).

    This used to be a [List.concat (List.map ...)], but this should
    be more efficient and independent of [List.map] eval order.
*)

let intern_args params =
  let args, ctx = List.fold_left intern_arg ([], Univ.ContextSet.empty) params in
  List.rev args, ctx

let start_module_core id args res =
  let mp = Global.start_module id in
  let params, ctx = intern_args args in
  let () = Global.push_context_set ctx in
  let env = Global.env () in
  let res_entry_o, subtyps, ctx' = match res with
    | Enforce (mte, base, kind, inl) ->
        let (mte, ctx) = Modintern.interp_module_ast env kind base mte in
        let env = Environ.push_context_set ctx env in
        (* We check immediately that mte is well-formed *)
        let state = ((Environ.universes env, Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
        let _, (_, cst), _ = Mod_typing.translate_modtype state vm_state env mp inl ([], mte) in
        let ctx = Univ.ContextSet.add_constraints cst ctx in
        Some (mte, inl), [], ctx
    | Check resl ->
      let typs, ctx = build_subtypes env mp params resl in
      None, typs, ctx
  in
  let () = Global.push_context_set ctx' in
  mp, res_entry_o, subtyps, params, Univ.ContextSet.union ctx ctx'

let start_module export id args res =
  let fs = Summary.Interp.freeze_summaries () in
  let mp, res_entry_o, subtyps, _, _ = start_module_core id args res in
  openmod_info := { cur_typ = res_entry_o; cur_typs = subtyps };
  let _ : object_prefix = Lib.Interp.start_module export id mp fs in
  mp

let end_module_core id m_info objects fs =
  let {Lib.substobjs = substitute; keepobjs = keep; escapeobjs = escape; anticipateobjs = special; } = objects in

  (* For sealed modules, we use the substitutive objects of their signatures *)
  let sobjs0, keep = match m_info.cur_typ with
    | None -> ([], Objs substitute), keep
    | Some (mty, inline) ->
      InterpVisitor.get_module_sobjs false (Global.env()) inline mty, { keep_objects = [] }
  in

  let struc = current_struct () in
  let restype' = Option.map (fun (ty,inl) -> (([],ty),inl)) m_info.cur_typ in
  let state = ((Global.universes (), Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
  let _, (_, cst), _ =
    Mod_typing.finalize_module state vm_state (Global.env ()) (Global.current_modpath ())
      (struc, current_modresolver ()) restype'
  in
  let () = Global.add_univ_constraints cst in

  let mp,mbids,resolver = Global.end_module fs id m_info.cur_typ in
  let sobjs = let (ms,objs) = sobjs0 in (mbids@ms,objs) in

  let () = check_subtypes mp m_info.cur_typs in

  (* We substitute objects if the module is sealed by a signature *)
  let sobjs =
    match m_info.cur_typ with
      | None -> sobjs
      | Some (mty, _) ->
        subst_sobjs (map_mp (get_module_path mty) mp resolver) sobjs
  in
  let node = ModuleObject (id,sobjs) in
  (* We add the keep objects, if any, and if this isn't a functor *)
  let keep = if not (CList.is_empty mbids) then [] else keep_objects id keep in
  (* NB: escape objects are added even for sealed modules, not sure if want *)
  let escape = escape_objects id escape in
  let objects = special@[node]@keep@escape in

  mp, objects

let end_module () =
  let oldprefix,fs,objects = Lib.Interp.end_module () in
  let m_info = !openmod_info in
  let _olddp, id = pop_path oldprefix.obj_path in
  let mp,objects = end_module_core id m_info objects fs in

  let () = InterpVisitor.add_leaves objects in

  (* Name consistency check : kernel vs. library *)
  assert (ModPath.equal oldprefix.obj_mp mp);

  mp

let get_functor_sobjs is_mod env inl (params,mexpr) =
  let (mbids, aobjs) = InterpVisitor.get_module_sobjs is_mod env inl mexpr in
  (List.map pi1 params @ mbids, aobjs)

(* TODO cleanup push universes directly to global env *)
let declare_module id args res mexpr_o =
  let fs = Summary.Interp.freeze_summaries () in
  (* We simulate the beginning of an interactive module,
     then we adds the module parameters to the global env. *)
  let mp, mty_entry_o, subs, params, ctx = start_module_core id args res in
  let env = Global.env () in
  let mexpr_entry_o, inl_expr, ctx' = match mexpr_o with
    | None -> None, default_inline_level (), Univ.ContextSet.empty
    | Some (mte, base, kind, inl) ->
      let (mte, ctx) = Modintern.interp_module_ast env kind base mte in
      Some mte, inl, ctx
  in
  let env = Environ.push_context_set ctx' env in
  let ctx = Univ.ContextSet.union ctx ctx' in
  let params = List.map (fun (mbid, _, mte, b) -> (mbid, mte, b)) params in
  let entry, inl_res = match mexpr_entry_o, mty_entry_o with
    | None, None -> assert false (* No body, no type ... *)
    | None, Some (typ, inl) -> MType (params, typ), inl
    | Some body, otyp -> MExpr (params, body, Option.map fst otyp), Option.cata snd (default_inline_level ()) otyp
  in
  let sobjs, mp0 = match entry with
    | MType (_,mte) | MExpr (_,_,Some mte) ->
      get_functor_sobjs false env inl_res (params,mte), get_module_path mte
    | MExpr (_,me,None) ->
      get_functor_sobjs true env inl_expr (params,me), get_module_path me
  in
  (* Undo the simulated interactive building of the module
     and declare the module as a whole *)
  Summary.Interp.unfreeze_summaries fs;
  let inl = match inl_expr with
  | None -> None
  | _ -> inl_res
  in
  let () = Global.push_context_set ctx in
  let state = ((Global.universes (), Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
  let _, (_, cst), _ = Mod_typing.translate_module state vm_state (Global.env ()) mp inl entry in
  let () = Global.add_univ_constraints cst in
  let mp_env,resolver = Global.add_module id entry inl in

  (* Name consistency check : kernel vs. library *)
  assert (ModPath.equal mp (mp_of_kn (Lib.make_kn id)));
  assert (ModPath.equal mp mp_env);

  let () = check_subtypes mp subs in

  let sobjs = subst_sobjs (map_mp mp0 mp resolver) sobjs in
  InterpVisitor.add_leaf (ModuleObject (id,sobjs));
  mp

end

end

(** {6 Module types : start, end, declare} *)

module RawModTypeOps = struct

module Synterp = struct

let start_modtype_core id cur_mp args mtys =
  let mp = ModPath.MPdot(cur_mp, id) in
  let args = RawModOps.Synterp.intern_args args in
  let mbids = List.flatten @@ List.map (fun (mbidl,_) -> mbidl) args in
  let sub_mty_l = RawModOps.Synterp.build_subtypes mtys in
  mp, mbids, args, sub_mty_l

let start_modtype id args mtys =
  let fs = Summary.Synterp.freeze_summaries () in
  let mp, mbids, args, sub_mty_l = start_modtype_core id (openmod_syntax_info ()).cur_mp args mtys in
  set_openmod_syntax_info { cur_mp = mp; cur_typ = None; cur_mbids = mbids };
  let prefix = Lib.Synterp.start_modtype id mp fs in
  Nametab.(push_dir (Until 1) (prefix.obj_path) (GlobDirRef.DirOpenModtype prefix.obj_mp));
  mp, args, sub_mty_l

let end_modtype_core id mbids objects fs =
  let {Lib.substobjs = substitute; keepobjs = _; escapeobjs = escape; anticipateobjs = special; } = objects in
  Summary.Synterp.unfreeze_summaries fs;
  let modtypeobjs = (mbids, Objs substitute) in
  special@[ModuleTypeObject (id,modtypeobjs)]@(escape_objects id escape)

let end_modtype () =
  let oldprefix,fs,objects = Lib.Synterp.end_modtype () in
  let _olddp, id = pop_path oldprefix.obj_path in
  let objects = end_modtype_core id (openmod_syntax_info ()).cur_mbids objects fs in
  SynterpVisitor.add_leaves objects;
  (openmod_syntax_info ()).cur_mp

let declare_modtype id args mtys (mty,ann) =
  let fs = Summary.Synterp.freeze_summaries () in
  let inl = inl2intopt ann in
  (* We simulate the beginning of an interactive module,
     then we adds the module parameters to the global env. *)
  let mp, mbids, args, sub_mty_l = start_modtype_core id (openmod_syntax_info ()).cur_mp args mtys in
  let mte, base, kind = Modintern.intern_module_ast Modintern.ModType mty in
  let entry = mbids, mte in
  let sobjs = RawModOps.Synterp.get_functor_sobjs false inl entry in
  let subst = map_mp (get_module_path (snd entry)) mp (empty_delta_resolver mp) in
  let sobjs = subst_sobjs subst sobjs in

  (* Undo the simulated interactive building of the module type
     and declare the module type as a whole *)
  Summary.Synterp.unfreeze_summaries fs;
  ignore (SynterpVisitor.add_leaf (ModuleTypeObject (id,sobjs)));
  mp, args, (mte, base, kind, inl), sub_mty_l

end

module Interp = struct

let openmodtype_info =
  Summary.ref ([] : module_type_body list) ~name:"MODTYPE-INFO"

let start_modtype_core id args mtys =
  let mp = Global.start_modtype id in
  let params, params_ctx = RawModOps.Interp.intern_args args in
  let () = Global.push_context_set params_ctx in
  let env = Global.env () in
  let sub_mty_l, sub_mty_ctx = RawModOps.Interp.build_subtypes env mp params mtys in
  let () = Global.push_context_set sub_mty_ctx in
  mp, params, sub_mty_l, Univ.ContextSet.union params_ctx sub_mty_ctx

let start_modtype id args mtys =
  let fs = Summary.Interp.freeze_summaries () in
  let mp, _, sub_mty_l, _ = start_modtype_core id args mtys in
  openmodtype_info := sub_mty_l;
  let prefix = Lib.Interp.start_modtype id mp fs in
  Nametab.(push_dir (Until 1) (prefix.obj_path) (GlobDirRef.DirOpenModtype mp));
  mp

let end_modtype_core id sub_mty_l objects fs =
  let {Lib.substobjs = substitute; keepobjs = _; escapeobjs = escape; anticipateobjs = special; } = objects in
  let mp, mbids = Global.end_modtype fs id in
  let () = RawModOps.Interp.check_subtypes_mt mp sub_mty_l in
  let modtypeobjs = (mbids, Objs substitute) in
  let objects = special@[ModuleTypeObject (id,modtypeobjs)]@(escape_objects id escape) in
  mp, objects

let end_modtype () =
  let oldprefix,fs,objects = Lib.Interp.end_modtype () in
  let olddp, id = pop_path oldprefix.obj_path in
  let sub_mty_l = !openmodtype_info in
  let mp, objects = end_modtype_core id sub_mty_l objects fs in
  let () = InterpVisitor.add_leaves objects in
  (* Check name consistence : start_ vs. end_modtype, kernel vs. library *)
  assert (eq_full_path (Lib.prefix()).obj_path olddp);
  assert (ModPath.equal oldprefix.obj_mp mp);
  mp

let declare_modtype id args mtys (mte,base,kind,inl) =
  let fs = Summary.Interp.freeze_summaries () in
  (* We simulate the beginning of an interactive module,
     then we adds the module parameters to the global env. *)
  let mp, params, sub_mty_l, ctx = start_modtype_core id args mtys in
  let env = Global.env () in
  let mte, mte_ctx = Modintern.interp_module_ast env kind base mte in
  let () = Global.push_context_set mte_ctx in
  let env = Global.env () in
  (* We check immediately that mte is well-formed *)
  let state = ((Global.universes (), Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
  let _, (_, mte_cst), _ = Mod_typing.translate_modtype state vm_state env mp inl ([], mte) in
  let () = Global.push_context_set (Univ.Level.Set.empty, mte_cst) in
  let params = List.map (fun (mbid, _, mte, b) -> (mbid, mte, b)) params in
  let entry = params, mte in
  let env = Global.env () in
  let sobjs = RawModOps.Interp.get_functor_sobjs false env inl entry in
  let subst = map_mp (get_module_path (snd entry)) mp (empty_delta_resolver mp) in
  let sobjs = subst_sobjs subst sobjs in

  (* Undo the simulated interactive building of the module type
     and declare the module type as a whole *)
  Summary.Interp.unfreeze_summaries fs;

  (* We enrich the global environment *)
  let () = Global.push_context_set ctx in
  let () = Global.push_context_set mte_ctx in
  let () = Global.push_context_set (Univ.Level.Set.empty, mte_cst) in
  let mp_env = Global.add_modtype id entry inl in

  (* Name consistency check : kernel vs. library *)
  assert (ModPath.equal mp_env mp);

  (* Subtyping checks *)
  let () = RawModOps.Interp.check_subtypes_mt mp sub_mty_l in

  InterpVisitor.add_leaf (ModuleTypeObject (id, sobjs));
  mp

end

end

(** {6 Include} *)

module RawIncludeOps = struct

exception NoIncludeSelf

module Synterp = struct

let rec include_subst mp mbids = match mbids with
  | [] -> empty_subst
  | mbid::mbids ->
    let subst = include_subst mp mbids in
    join (map_mbid mbid mp (empty_delta_resolver mp)) subst

let declare_one_include_core cur_mp (me_ast,annot) =
  let me, base, kind = Modintern.intern_module_ast Modintern.ModAny me_ast in
  let is_mod = (kind == Modintern.Module) in
  let inl = inl2intopt annot in
  let mbids,aobjs = SynterpVisitor.get_module_sobjs is_mod () inl me in
  let subst_self =
    try
      if List.is_empty mbids then raise NoIncludeSelf;
      include_subst cur_mp mbids
    with NoIncludeSelf -> empty_subst
  in
  let base_mp = get_module_path me in
  (* We can use an empty delta resolver on syntax objects *)
  let subst = join subst_self (map_mp base_mp cur_mp (empty_delta_resolver cur_mp)) in
  let aobjs = subst_aobjs subst aobjs in
  (me, base, kind, inl), aobjs

let declare_one_include (me_ast,annot) =
  let res, aobjs = declare_one_include_core (openmod_syntax_info ()).cur_mp (me_ast,annot) in
  SynterpVisitor.add_leaf (IncludeObject aobjs);
  res

let declare_include me_asts = List.map declare_one_include me_asts

end

module Interp = struct

let rec include_subst env mp reso mbids sign inline = match mbids with
  | [] -> empty_subst
  | mbid::mbids ->
    let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
    let subst = include_subst env mp reso mbids fbody_b inline in
    let mp_delta =
      Modops.inline_delta_resolver env inline mp farg_id farg_b reso
    in
    join (map_mbid mbid mp mp_delta) subst

let rec decompose_functor mpl typ =
  match mpl, typ with
  | [], _ -> typ
  | _::mpl, MoreFunctor(_,_,str) -> decompose_functor mpl str
  | _ -> user_err Pp.(str "Application of a functor with too much arguments.")

let type_of_incl env is_mod = function
  | MEident mp -> type_of_mod mp env is_mod
  | MEapply _ as me ->
    let mp0, mp_l = InterpVisitor.get_applications me in
    decompose_functor mp_l (type_of_mod mp0 env is_mod)
  | MEwith _ -> raise NoIncludeSelf

(** Implements [Include F] where [F] has parameters [mbids] to be
    instantiated by fields of the current "self" module, i.e. using
    subtyping, by the current module itself. *)

let declare_one_include_core (me,base,kind,inl) =
  let env = Global.env() in
  let me, cst = Modintern.interp_module_ast env kind base me in
  let () = Global.push_context_set cst in
  let env = Global.env () in
  let is_mod = (kind == Modintern.Module) in
  let cur_mp = Global.current_modpath () in
  let mbids,aobjs = InterpVisitor.get_module_sobjs is_mod env inl me in
  let subst_self =
    try
      if List.is_empty mbids then raise NoIncludeSelf;
      let typ = type_of_incl env is_mod me in
      let reso = RawModOps.Interp.current_modresolver () in
      include_subst env cur_mp reso mbids typ inl
    with NoIncludeSelf -> empty_subst
  in
  let base_mp = get_module_path me in

  let state = ((Global.universes (), Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
  let sign, (), resolver, (_, cst), _ =
    Mod_typing.translate_mse_include is_mod state vm_state (Global.env ()) (Global.current_modpath ()) inl me
  in
  let () = Global.add_univ_constraints cst in
  let () = assert (ModPath.equal cur_mp (Global.current_modpath ())) in
  (* Include Self support  *)
  let mb = make_module_body (RawModOps.Interp.current_struct ()) (RawModOps.Interp.current_modresolver ()) [] in
  let rec compute_sign sign =
    match sign with
    | MoreFunctor(mbid,mtb,str) ->
      let state = ((Global.universes (), Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
      (* Module subcomponents are already part of env at this point *)
      let env = Environ.shallow_add_module cur_mp mb (Global.env ()) in
      let (_, cst) = Subtyping.check_subtypes ~direct:true state env cur_mp (MPbound mbid) mtb in
      let () = Global.add_univ_constraints cst in
      let mpsup_delta = match mod_global_delta mb with
      | None -> assert false (* mb is guaranteed not to be a functor here *)
      | Some delta ->
        Modops.inline_delta_resolver (Global.env ()) inl cur_mp mbid mtb delta
      in
      let subst = Mod_subst.map_mbid mbid cur_mp mpsup_delta in
      compute_sign (Modops.subst_signature subst cur_mp str)
    | NoFunctor str -> ()
  in
  let () = compute_sign sign in

  let resolver = Global.add_include me is_mod inl in
  let subst = join subst_self (map_mp base_mp cur_mp resolver) in
  subst_aobjs subst aobjs

let declare_one_include (me,base,kind,inl) =
  let aobjs = declare_one_include_core (me,base,kind,inl) in
  InterpVisitor.add_leaf (IncludeObject aobjs)

let declare_include me_asts = List.iter declare_one_include me_asts

end

end

(** {6 Libraries} *)

type library_name = DirPath.t

(** A library object is made of some substitutive objects
    and some "keep" and "escape" objects. *)

type library_objects = Libobject.t list * keep_objects * escape_objects

module Synterp = struct

let start_module export id args res =
  RawModOps.Synterp.start_module export id args res

let end_module = RawModOps.Synterp.end_module

(** Declare a module in terms of a list of module bodies, by including them.
Typically used for `Module M := N <+ P`.
*)
let declare_module_includes id args res mexpr_l =
  let fs = Summary.Synterp.freeze_summaries () in
  let mp, res_entry_o, mbids, sign, args = RawModOps.Synterp.start_module_core id args res in
  let mod_info = { cur_mp = mp; cur_typ = res_entry_o; cur_mbids = mbids } in
  let includes = List.map_left (RawIncludeOps.Synterp.declare_one_include_core mp) mexpr_l in
  let bodies, incl_objs = List.split includes in
  let incl_objs = List.map (fun x -> IncludeObject x) incl_objs in
  let objects = {
    Lib.substobjs = incl_objs;
    keepobjs = { keep_objects = [] };
    escapeobjs = { escape_objects = [] };
    anticipateobjs = [];
  } in
  let mp, objects = RawModOps.Synterp.end_module_core id mod_info objects fs in
  SynterpVisitor.add_leaves objects;
  mp, args, bodies, sign

(** Declare a module type in terms of a list of module bodies, by including them.
Typically used for `Module Type M := N <+ P`.
*)
let declare_modtype_includes id args res mexpr_l =
  let fs = Summary.Synterp.freeze_summaries () in
  let mp, mbids, args, subtyps = RawModTypeOps.Synterp.start_modtype_core id (openmod_syntax_info ()).cur_mp args res in
  let includes = List.map_left (RawIncludeOps.Synterp.declare_one_include_core mp) mexpr_l in
  let bodies, incl_objs = List.split includes in
  let incl_objs = List.map (fun x -> IncludeObject x) incl_objs in
  let objects = {
    Lib.substobjs = incl_objs;
    keepobjs = { keep_objects = [] };
    escapeobjs = { escape_objects = [] };
    anticipateobjs = [];
  } in
  let objects = RawModTypeOps.Synterp.end_modtype_core id mbids objects fs in
  SynterpVisitor.add_leaves objects;
  mp, args, bodies, subtyps

let declare_module id args mtys me_l =
  match me_l with
  | [] ->
    let mp, args, body, sign = RawModOps.Synterp.declare_module id args mtys None in
    assert (Option.is_empty body);
    mp, args, [], sign
  | [me] ->
    let mp, args, body, sign = RawModOps.Synterp.declare_module id args mtys (Some me) in
    mp, args, [Option.get body], sign
  | me_l -> declare_module_includes id args mtys me_l

let start_modtype id args mtys =
  RawModTypeOps.Synterp.start_modtype id args mtys

let end_modtype = RawModTypeOps.Synterp.end_modtype

let declare_modtype id args mtys mty_l =
  match mty_l with
    | [] -> assert false
    | [mty] ->
      let mp, args, body, sign = RawModTypeOps.Synterp.declare_modtype id args mtys mty in
      mp, args, [body], sign
    | mty_l -> declare_modtype_includes id args mtys mty_l

let declare_include = RawIncludeOps.Synterp.declare_include

let register_library dir (objs:library_objects) =
  let mp = MPfile dir in
  let sp = path_of_file dir in
  let sobjs,keepobjs,escapeobjs = objs in
  SynterpVisitor.load_module 1 sp mp ([],Objs sobjs);
  SynterpVisitor.load_escape 2 sp mp escapeobjs;
  SynterpVisitor.load_keep 2 sp mp keepobjs

let register_safe_library dir mb =
  SynterpVisitor.load_safe_library dir mb

let import_modules = SynterpVisitor.import_modules

let import_module f ~export mp =
  import_modules ~export [f,mp]

let close_section = SynterpVisitor.close_section

end

module Interp = struct

let start_module = RawModOps.Interp.start_module

let end_module = RawModOps.Interp.end_module

(** Declare a module in terms of a list of module bodies, by including them.
Typically used for `Module M := N <+ P`.
*)
let declare_module_includes id args res mexpr_l =
  let fs = Summary.Interp.freeze_summaries () in
  let mp, res_entry_o, subtyps, _, _ = RawModOps.Interp.start_module_core id args res in
  let mod_info = { cur_typ = res_entry_o; cur_typs = subtyps } in
  let incl_objs = List.map_left (fun x -> IncludeObject (RawIncludeOps.Interp.declare_one_include_core x)) mexpr_l in
  let objects = {
    Lib.substobjs = incl_objs;
    keepobjs = { keep_objects = [] };
    escapeobjs = { escape_objects = [] };
    anticipateobjs = [];
  } in
  let mp, objects = RawModOps.Interp.end_module_core id mod_info objects fs in
  InterpVisitor.add_leaves objects;
  mp

(** Declare a module type in terms of a list of module bodies, by including them.
Typically used for `Module Type M := N <+ P`.
*)
let declare_modtype_includes id args res mexpr_l =
  let fs = Summary.Interp.freeze_summaries () in
  let mp, _, subtyps, _ = RawModTypeOps.Interp.start_modtype_core id args res in
  let incl_objs = List.map_left (fun x -> IncludeObject (RawIncludeOps.Interp.declare_one_include_core x)) mexpr_l in
  let objects = {
    Lib.substobjs = incl_objs;
    keepobjs = { keep_objects = [] };
    escapeobjs = { escape_objects = [] };
    anticipateobjs = [];
  } in
  let mp, objects = RawModTypeOps.Interp.end_modtype_core id subtyps objects fs in
  InterpVisitor.add_leaves objects;
  mp

let declare_module id args mtys me_l =
  match me_l with
  | [] -> RawModOps.Interp.declare_module id args mtys None
  | [me] -> RawModOps.Interp.declare_module id args mtys (Some me)
  | me_l -> declare_module_includes id args mtys me_l

let start_modtype = RawModTypeOps.Interp.start_modtype

let end_modtype = RawModTypeOps.Interp.end_modtype

let declare_modtype id args mtys mty_l =
  match mty_l with
  | [] -> assert false
  | [mty] -> RawModTypeOps.Interp.declare_modtype id args mtys mty
  | mty_l -> declare_modtype_includes id args mtys mty_l

let declare_include me_asts =
  if Lib.sections_are_opened () then
    user_err Pp.(str "Include is not allowed inside sections.");
  RawIncludeOps.Interp.declare_include me_asts

let register_library dir cenv (objs:library_objects) digest vmtab =
  let mp = MPfile dir in
  let sp = path_of_file dir in
  let () =
    try
      (* If the library was loaded inside a module or section, the
         end_segment will replay the library object for non-kernel
         effects but the kernel did not forget the library. *)
      ignore(Global.lookup_module mp);
    with Not_found ->
      begin
      let mp' = Global.import cenv vmtab digest in
      if not (ModPath.equal mp mp') then
        anomaly (Pp.str "Unexpected disk module name.")
      end
  in
  let sobjs,keepobjs,escapeobjs = objs in
  InterpVisitor.load_module 1 sp mp ([],Objs sobjs);
  InterpVisitor.load_escape 1 sp mp escapeobjs;
  InterpVisitor.load_keep 1 sp mp keepobjs

let register_safe_library dir mb =
  InterpVisitor.load_safe_library dir mb

let import_modules = InterpVisitor.import_modules

let import_module f ~export mp =
  import_modules ~export [f,mp]

let close_section = InterpVisitor.close_section

end

let end_library_hook = ref []
let append_end_library_hook f =
  end_library_hook := f :: !end_library_hook

let end_library_hook () =
  List.iter (fun f -> f ()) (List.rev !end_library_hook)

(** binary-equivalence-taiga#841 G1 fix (Review841's finding: the exact
    objects digest refuses every Admitted->Qed and every unused addition,
    defeating the whole lever, because `cst_kind` -- IsAssumption vs
    IsProof -- lives inside the CONSTANT libobject's payload, and an
    ADDED declaration is new content under any exact-equality comparison
    regardless of field-level normalization).

    Partition every atomic libobject in a library's exported content into
    three groups, by its registered tag (`Libobject.object_name`, the
    string each `declare_object`/`declare_named_object_full` call
    registers -- e.g. "CONSTANT") -- CONFIRMED STRUCTURALLY, not by the
    tag string alone (binary-equivalence-taiga#841 Review841 G1 self-audit,
    a Lean attack shape (b) check: a tag string only decides WHICH
    registered classifier to dispatch to -- `Libobject.cutoff_classify`,
    see its own doc comment for why `Declare`/`DeclareInd` register their
    classifiers into a `Libobject`-owned table instead of this function
    calling into those modules directly (a real `dune build` dependency
    cycle) -- and each classifier still does its own `Libobject.Dyn.Easy.prj`
    check before answering, so a tag string match that fails its
    structural check falls through to EXACT here -- never silently
    dropped from every digest):
    - EXCLUDED (`"INDUCTIVE"`, `"PRIMPROJS"`): a declaration's
      semantically load-bearing identity (type, universe context,
      transparent body, and for inductives the WHOLE
      `mutual_inductive_body` including primitive-record/projection
      structure) is ALREADY independently covered by
      `Safe_typing.comp_iface`'s kernel-level per-declaration digest
      (D1/D3), itself subset-checked (extras ignored). `DeclareInd`'s
      INDUCTIVE/PRIMPROJS libobjects carry nothing beyond that except
      `ind_names`'s declaration-site `Loc.t`s, read only by
      `Nametab.set_cci_src_loc` ("Declared in" messages) -- presentation
      only, never typechecking or `Print Assumptions`.
    - SUBSET-CHECKED (`"CONSTANT"` only): NOT fully excluded like
      INDUCTIVE/PRIMPROJS, because two of its four fields are NOT
      presentation-only: `Declare`'s own registered classifier
      (`Declare.ml`'s top-level `Libobject.register_cutoff_classifier
      "CONSTANT"`) digests `cst_locl` (whether the name needs
      qualification when `Import`ed -- a FRESH compile of a dependent
      could resolve an unqualified reference differently if this changes)
      and `cst_warn` (a deprecation/warning annotation on USES of this
      name -- a FRESH compile could fail under `-w
      +deprecated...-warn-error`); `cst_kind`/`cst_loc` are still excluded
      from that digest for the same presentation-only reason as
      INDUCTIVE's fields (Review841 round 3's "l1"/"d1" fixtures: exactly
      this gap, reproduced and closed). Lands in a per-declaration digest
      SET, subset-checked (`Safe_typing.decl_objects_subset_ok`): every
      digest the dependent recorded must still be found among the
      library's current digests; an added CONSTANT is ignored.
    - EXACT (everything else -- Hints, Instances, Notations, Canonical
      Structures, Coercions, the univ-constraint-source object, Ltac,
      IMPLICITS, ARGUMENTS-SCOPE, `ExportObject`, module/include
      wrappers): unchanged from the existing design for most of these,
      but IMPLICITS/ARGUMENTS-SCOPE moved HERE in round 3 (Review841's
      "i1"/"i3" fixtures) after an earlier revision's raw-leaf-digest SET
      treatment proved unsound -- see [classify]'s own doc comment for
      why and for the correct (not-yet-built) per-GlobRef-effective-value
      fix.


    G7 (name-shadowing refusal) is implemented in `Safe_typing.dep_ok`
    directly (`added_label_collision`/`used_names_of_needed`), reusing the
    kernel's own `iface_table` key set rather than anything from this
    module -- see that function's doc comment. *)
module G1Partition = struct
  type classification =
    | Excluded
    | Exact

  let modpath_of_gr = function
    | GlobRef.ConstRef c -> Some (Constant.modpath c)
    | GlobRef.IndRef (mind, _) -> Some (MutInd.modpath mind)
    | GlobRef.ConstructRef ((mind, _), _) -> Some (MutInd.modpath mind)
    | GlobRef.VarRef _ -> None

  let is_local dir gr =
    match modpath_of_gr gr with
    | Some mp -> ModPath.subpath (MPfile dir) mp
    | None -> false

  (* "IMPLICITS"/"ARGUMENTS-SCOPE" are EXCLUDED here (dropped from the
     exact digest), not subset-checked by their raw leaf bytes: an
     `Arguments foo {x}` added to an EXISTING declaration, or two
     reordered Arguments leaves for the same name, change which one is
     EFFECTIVE without the leaf SET changing at all -- Review841 round 3's
     "i1"/"i3" fixtures reproduced exactly this as a real unsoundness
     (reused dependent loads where a fresh compile fails) against an
     earlier revision's raw-leaf-digest SET. Their real coverage lives in
     [vernac_iface_entries] below: a per-NAME digest of the EFFECTIVE,
     RESOLVED value (`Impargs.implicits_of_global`/
     `Notation.find_arguments_scope`, the same functions elaboration
     itself consults, queried fresh at [end_library] time against the
     library's OWN completed environment -- not the raw leaf objects),
     checked like the kernel's [iface_table] (every name the dependent
     used must still match; an added name is ignored; see [dep_ok] via
     the new [req_vernac_iface] field).

     binary-equivalence-taiga#841 Review841 round 5 (forg, Main's
     finding): this is sound ONLY when every target the raw object
     concerns is itself one of THIS library's own top-level declarations
     -- [vernac_iface_entries]'s own walk, below, only ever visits
     declaration objects actually PRESENT in THIS library's own object
     tree, so a `#[global] Arguments Nat.pred ...` overriding a FOREIGN
     target (declared in a different, already-loaded library) is never
     re-queried by that walk at all: excluding it here would drop it from
     every digest with NOTHING picking up the slack. Fix: inspect the raw
     object's own target [GlobRef.t](s) directly (via
     [Impargs.cutoff_implicits_targets]/
     [Notation.cutoff_arguments_scope_target]) and only Exclude when
     EVERY target is local to [dir] (so [vernac_iface_entries]'s walk
     will in fact re-visit it via that target's own CONSTANT/INDUCTIVE
     declaration object elsewhere in the same tree); a foreign target (or
     a [VarRef], which [vernac_iface_entries] never keys) stays in the
     EXACT digest, same as before G1 for that specific object. *)
  let classify dir (obj : Libobject.obj) : classification =
    match Impargs.cutoff_implicits_targets obj with
    | Some targets ->
      if List.for_all (is_local dir) targets then Excluded else Exact
    | None ->
      match Notation.cutoff_arguments_scope_target obj with
      | Some gr -> if is_local dir gr then Excluded else Exact
      | None ->
        (match Libobject.cutoff_classify obj with
         | Some Libobject.CutoffExcluded -> Excluded
         | Some (Libobject.CutoffKeyed _) -> Excluded
         | None -> Exact)

  let rec filter_atomic dir (o : Libobject.t) : Libobject.t option =
    match o with
    | Libobject.AtomicObject obj ->
      (match classify dir obj with Exact -> Some o | Excluded -> None)
    | Libobject.ModuleObject (id, (mbids, alg)) ->
      Option.map (fun alg -> Libobject.ModuleObject (id, (mbids, alg))) (filter_algebraic dir alg)
    | Libobject.ModuleTypeObject (id, (mbids, alg)) ->
      (* A module type whose filtered body holds no Exact object contributes
         nothing a dependent can observe through this digest: its fields and
         their shape are in the keyed [comp_iface] label digest, and its name
         is in the G7 closure. Keeping the empty wrapper made any unrelated
         new Module Type refuse every dependent (mtunrel0). A module type
         that carries exact syntax keeps its wrapper. *)
      (match filter_algebraic dir alg with
       | Some (Libobject.Objs []) -> None
       | filtered ->
         Option.map (fun alg -> Libobject.ModuleTypeObject (id, (mbids, alg))) filtered)
    | Libobject.IncludeObject alg ->
      Option.map (fun alg -> Libobject.IncludeObject alg) (filter_algebraic dir alg)
    | Libobject.KeepObject (id, { Libobject.keep_objects }) ->
      Some (Libobject.KeepObject (id, { Libobject.keep_objects = List.filter_map (filter_atomic dir) keep_objects }))
    | Libobject.EscapeObject (id, { Libobject.escape_objects }) ->
      Some (Libobject.EscapeObject (id, { Libobject.escape_objects = List.filter_map (filter_atomic dir) escape_objects }))
    | Libobject.ExportObject _ -> Some o
  and filter_algebraic dir = function
    | Libobject.Objs l -> Some (Libobject.Objs (List.filter_map (filter_atomic dir) l))
    | Libobject.Ref _ as r -> Some r

  let filter_library_objects dir ((substobjs, keepobjs, escapeobjs) : library_objects) : library_objects =
    (List.filter_map (filter_atomic dir) substobjs,
     { Libobject.keep_objects = List.filter_map (filter_atomic dir) keepobjs.Libobject.keep_objects },
     { Libobject.escape_objects = List.filter_map (filter_atomic dir) escapeobjs.Libobject.escape_objects })
  (* Export objects carry exactly the module paths made visible by Require
     Export. Keep their root dirpaths as a graph edge, not as an opaque
     whole-library digest, so adding a disjoint export remains reusable. *)
  let rec export_dirs_of_object = function
    | Libobject.ExportObject { Libobject.ExportObj.mpl } ->
      List.map (fun (_, mp) -> ModPath.dp mp) mpl
    | Libobject.ModuleObject (_, (_, alg))
    | Libobject.ModuleTypeObject (_, (_, alg))
    | Libobject.IncludeObject alg -> export_dirs_of_algebraic alg
    | Libobject.KeepObject (_, { Libobject.keep_objects }) ->
      List.concat_map export_dirs_of_object keep_objects
    | Libobject.EscapeObject (_, { Libobject.escape_objects }) ->
      List.concat_map export_dirs_of_object escape_objects
    | Libobject.AtomicObject _ -> []
  and export_dirs_of_algebraic = function
    | Libobject.Objs l -> List.concat_map export_dirs_of_object l
    | Libobject.Ref _ -> []

  let exported_dirs (md_syntax_objects, md_objects) =
    let dirs (substobjs, keepobjs, escapeobjs) =
      substobjs @ keepobjs.Libobject.keep_objects @ escapeobjs.Libobject.escape_objects
      |> List.concat_map export_dirs_of_object
    in
    DirPath.Set.elements (List.fold_left (fun s dp -> DirPath.Set.add dp s)
      DirPath.Set.empty (dirs md_syntax_objects @ dirs md_objects)) |> Array.of_list

  (* A module alias or Include changes which target's exports become visible.
     Keep the referenced module paths in a separate digest so such a change
     is checked without making every disjoint Require Export a refusal. *)
  let rec alias_paths_of_object = function
    | Libobject.ModuleObject (_, (_, alg))
    | Libobject.ModuleTypeObject (_, (_, alg))
    | Libobject.IncludeObject alg -> alias_paths_of_algebraic alg
    | Libobject.KeepObject (_, { Libobject.keep_objects }) ->
      List.concat_map alias_paths_of_object keep_objects
    | Libobject.EscapeObject (_, { Libobject.escape_objects }) ->
      List.concat_map alias_paths_of_object escape_objects
    | Libobject.ExportObject _ | Libobject.AtomicObject _ -> []
  and alias_paths_of_algebraic = function
    | Libobject.Objs l -> List.concat_map alias_paths_of_object l
    | Libobject.Ref (mp, _) -> [mp]

  let alias_digest (md_syntax_objects, md_objects) =
    let paths (substobjs, keepobjs, escapeobjs) =
      substobjs @ keepobjs.Libobject.keep_objects @ escapeobjs.Libobject.escape_objects
      |> List.concat_map alias_paths_of_object
    in
    Csha256.digest (Marshal.to_string
      (paths md_syntax_objects, paths md_objects) [])

  (* A transitive consumer needs exact syntax objects such as Notations and
     Hints, but module wrappers themselves are represented by [comp_iface]
     and the closure-name check. Flatten their contents so an unused Module
     or Module Type addition does not poison every transitive dependent.
     [ExportObject]s are left out: which libraries become visible is checked
     precisely by [exported_dirs] and the closure visibility set, so a
     disjoint [Require Export] must not change this digest. *)
  let rec transitive_objects_of_object dir (o : Libobject.t) =
    match o with
    | Libobject.AtomicObject obj ->
      (match classify dir obj with
       | Exact -> [o]
       | Excluded -> [])
    | Libobject.ModuleObject (_, (_, alg))
    | Libobject.ModuleTypeObject (_, (_, alg))
    | Libobject.IncludeObject alg ->
      transitive_objects_of_algebraic dir alg
    | Libobject.KeepObject (_, { Libobject.keep_objects }) ->
      List.concat_map (transitive_objects_of_object dir) keep_objects
    | Libobject.EscapeObject (_, { Libobject.escape_objects }) ->
      List.concat_map (transitive_objects_of_object dir) escape_objects
    | Libobject.ExportObject _ -> []
  and transitive_objects_of_algebraic dir = function
    | Libobject.Objs l -> List.concat_map (transitive_objects_of_object dir) l
    | Libobject.Ref _ -> []

  let transitive_objects_digest dir (md_syntax_objects, md_objects) =
    let flatten (substobjs, keepobjs, escapeobjs) =
      List.concat_map (transitive_objects_of_object dir)
        (substobjs @ keepobjs.Libobject.keep_objects @ escapeobjs.Libobject.escape_objects)
    in
    match flatten md_syntax_objects, flatten md_objects with
    | [], [] -> Safe_typing.no_transitive_syntax_digest
    | syntax, objects ->
      Csha256.digest (Marshal.to_string (syntax, objects) [])

  (** binary-equivalence-taiga#841 Review841 round 3 + round 5: the KEYED
      vernac-level interface table, checked by [Safe_typing.iface_subset_ok]
      exactly like the kernel's own [iface_table]. [Libobject.cutoff_classify]
      now hands back the target [GlobRef.t] DIRECTLY (round 5; the
      predecessor reconstructed it here from [dir]+[Id.t], which only
      worked for CONSTANT) -- covers CONSTANT, INDUCTIVE types and
      constructors (ind1/ind2/g7ctor); PRIMPROJS stays wholesale excluded
      (see [DeclareInd]'s own classifier doc comment). *)
  (** binary-equivalence-taiga#841 round 8 (kd1/kd2/dv2/dl2): keyed by a
      QUALIFIED string derived from [gr] itself (the [GlobRef.t] a
      [CutoffKeyed] entry already carries, now correctly scoped --
      [Declare]/[DeclareInd]'s own classifiers capture the declaration's
      true [ModPath.t] at declaration time rather than reconstructing it
      from [Global.current_modpath ()] at [end_library] time; see
      [Declare.constant_obj]'s [cst_modpath] doc comment), NEVER the bare
      [Id.t] round 5 first shipped with: two declarations sharing a
      short name (a top-level [foo] and a nested [M.foo]) landing under
      the SAME bare key let [Safe_typing.iface_subset_ok]'s
      single-match lookup silently pair a changed SECOND entry against
      an unrelated, unchanged FIRST one with the same key -- confirmed
      exploitable into a kernel-accepted proof of [False] (round 8
      review, "kd1"/"kd2"). [qualified_key_of_globref] has no notion of
      "basename" to extract back out afterward: unlike the kernel's own
      [iface_table]/[closure_table] split, [vernac_iface] is NEVER
      flattened into a cross-library shadow table at all (see [dep_ok]'s
      doc comment, condition (d)) -- it only ever compares one library's
      own recorded entries against its own live ones, so there is no
      second, coarser representation it needs to feed. *)
  let qualified_key_of_globref (gr : GlobRef.t) : string =
    match gr with
    | GlobRef.ConstRef c -> Constant.to_string c
    | GlobRef.IndRef (mind, i) -> MutInd.to_string mind ^ "#" ^ string_of_int i
    | GlobRef.ConstructRef ((mind, i), j) ->
      MutInd.to_string mind ^ "#" ^ string_of_int i ^ "#" ^ string_of_int j
    | GlobRef.VarRef id -> Id.to_string id

  (* Digit-leading, so it can never be the start of an identifier: keys in
     this namespace cannot collide with a [CutoffKeyed] declaration key. *)
  let raw_arguments_key_prefix = "1args#"

  let vernac_iface_entries dir (objs : Libobject.t list) : (string * Digest.t) array * (string * Digest.t) array =
    let env = Global.env () in
    let acc = ref [] in
    let abbrev_acc = ref [] in
    let raw_args = ref [] in
    let handle_atomic obj =
      (* Local [Arguments] objects are per-target state.  Collect their raw
         bytes per target, so a changed existing field is rejected while a
         new module type and all of its new fields remain an ignored
         addition.  They are emitted below under [raw_arguments_key_prefix],
         one folded digest per target: [iface_subset_ok] matches the first
         entry with a given key, so a key must never carry two digests.
         Foreign targets stay in the exact whole-object digest. *)
      let raw_digest = Csha256.digest (Marshal.to_string obj []) in
      let add_raw_target gr =
        raw_args := (qualified_key_of_globref gr, raw_digest) :: !raw_args
      in
      (match Impargs.cutoff_implicits_targets obj with
       | Some targets when List.for_all (is_local dir) targets ->
         List.iter add_raw_target targets
       | _ ->
         match Notation.cutoff_arguments_scope_target obj with
         | Some gr when is_local dir gr -> add_raw_target gr
         | Some _ | None -> ());
      match Libobject.cutoff_classify obj with
      | Some (Libobject.CutoffKeyed entries) ->
        List.iter (fun (gr, _id, base) ->
            let impls = Impargs.implicits_of_global gr in
            let scopes = Notation.find_arguments_scope env gr in
            let d = Csha256.digest (Marshal.to_string (base, impls, scopes) []) in
            acc := (qualified_key_of_globref gr, d) :: !acc)
          entries
      | Some Libobject.CutoffExcluded | None ->
        (* binary-equivalence-taiga#841 round 7 (ab1): an abbreviation is
           not a [CutoffKeyed] target (it has no [GlobRef.t] -- see
           [Abbreviation.cutoff_abbrev_entry]'s doc comment), so it is
           checked separately here rather than through
           [Libobject.cutoff_classify]. Still keyed by bare [Id.t]
           (round 8 does not extend the qualified-path fix to
           abbreviations): unlike CONSTANT/INDUCTIVE, nothing here yet
           captures an abbreviation's own enclosing module path, so a
           nested [Notation] colliding with another same-named one is a
           known, narrower residual version of the SAME masking class --
           no worse than before this round. *)
        (match Abbreviation.cutoff_abbrev_entry obj with
         | Some (id, d) -> abbrev_acc := (Id.to_string id, d) :: !abbrev_acc
         | None -> ())
    in
    let rec walk (o : Libobject.t) = match o with
      | Libobject.AtomicObject obj -> handle_atomic obj
      | Libobject.ModuleObject (_, (_, alg)) -> walk_alg alg
      | Libobject.ModuleTypeObject (_, (_, alg)) -> walk_alg alg
      | Libobject.IncludeObject alg -> walk_alg alg
      | Libobject.KeepObject (_, { Libobject.keep_objects }) -> List.iter walk keep_objects
      | Libobject.EscapeObject (_, { Libobject.escape_objects }) -> List.iter walk escape_objects
      | Libobject.ExportObject _ -> ()
    and walk_alg = function
      | Libobject.Objs l -> List.iter walk l
      | Libobject.Ref _ -> ()
    in
    List.iter walk objs;
    let raw_keys =
      List.sort_uniq String.compare (List.map fst !raw_args)
    in
    List.iter (fun key ->
        let ds =
          List.rev !raw_args
          |> List.filter_map (fun (k, d) -> if String.equal k key then Some d else None)
        in
        acc := (raw_arguments_key_prefix ^ key,
                Csha256.digest (Marshal.to_string ds [])) :: !acc)
      raw_keys;
    Array.of_list !acc, Array.of_list !abbrev_acc

  let partition dir (md_syntax_objects, md_objects : library_objects * library_objects) =
    let exact_syntax = filter_library_objects dir md_syntax_objects in
    let exact_objects = filter_library_objects dir md_objects in
    let exact_digest = Csha256.digest (Marshal.to_string (exact_syntax, exact_objects) []) in
    let exported_dirs = exported_dirs (md_syntax_objects, md_objects) in
    let alias_digest = alias_digest (md_syntax_objects, md_objects) in
    let transitive_digest = transitive_objects_digest dir (md_syntax_objects, md_objects) in
    let (substobjs, keepobjs, escapeobjs) = md_objects in
    let vernac_iface, abbrev_iface =
      vernac_iface_entries dir
        (substobjs @ keepobjs.Libobject.keep_objects @ escapeobjs.Libobject.escape_objects)
    in
    (exact_digest, exported_dirs, alias_digest, transitive_digest, vernac_iface, abbrev_iface)
end


let end_library ~output_native_objects ~require_order dir =
  end_library_hook();
  let { Lib.info; interp_objects = lib_stack; synterp_objects = lib_stack_syntax; } =
    Lib.end_compilation dir
  in
  let drop_anticipate {Lib.substobjs; keepobjs; escapeobjs; anticipateobjs=_} =
    (substobjs, keepobjs, escapeobjs)
  in
  (* binary-equivalence-taiga#841 D4/G1: compute md_objects/md_syntax_objects
     (Anticipate-dropped, matching exactly what is returned/serialized
     below) BEFORE calling Global.export, so the digests -- and commit 1's
     Dvo_iface, once it lands and consumes the same values -- see the
     REQUIRE-leaf-free value that ends up on disk, never a different one.
     WIP: not yet run through commit 1's shared Loc-erasing normalization
     hook (lands with sami/861-loc-free-identity) -- the exact-equality
     half is sound but less precise (changes on every length-changing
     edit to anything NOT excluded/subset-checked) until rebased. *)
  let md_objects = drop_anticipate lib_stack in
  let md_syntax_objects = drop_anticipate lib_stack_syntax in
  let objects_digest, exported_dirs, alias_digest, transitive_objects_digest, vernac_iface, abbrev_iface =
    G1Partition.partition dir (md_syntax_objects, md_objects)
  in
  (* binary-equivalence-taiga#841 round 23 (speed-coord review plan-861c1-r1
     finding R1-3, and the two fixtures it produced:
     order_instance_priority_residual_gap, info_deprecated_attribute_residual_gap).
     Two things a dependent's own compile observes used to live only in the
     summary segment, which no digest covers: this library's file-level
     attributes (a deprecation here makes a dependent built under
     "+deprecated" fail), and the order its requirements were loaded in
     (which decides which instance or hint a dependent's proof search
     picks). Both are folded into the exact-compared objects digest, so a
     change in either refuses every dependent, and changes this library's
     own segment bytes as well. [No_sharing]: the digest has to be a
     function of the value, never of how it was built. *)
  let objects_digest =
    Csha256.digest
      (objects_digest ^ "\000usage_cutoff_summary\000"
       ^ Marshal.to_string (List.map DirPath.to_string require_order, info)
           [Marshal.No_sharing])
  in
  (* binary-equivalence-taiga#841 round 23: the libraries this one copies
     structurally. Every module expression this file interpreted named its
     targets through [Modintern]; a target rooted in this library itself is
     this library's own content, already covered by its own digest. See
     [Safe_typing.structural_dep]. *)
  let structural_dirs =
    Modintern.structural_targets ()
    |> List.map ModPath.dp
    |> List.filter (fun dp -> not (DirPath.equal dp dir))
    |> List.sort_uniq DirPath.compare
    |> Array.of_list
  in
  Modintern.clear_structural_targets ();
  let mp,cenv,vmlib,ast = Global.export ~output_native_objects ~objects_digest ~exported_dirs ~alias_digest ~transitive_objects_digest ~vernac_iface ~extra_closure_names:abbrev_iface ~structural_dirs dir in
  assert (ModPath.equal mp (MPfile dir));
  cenv,md_objects,md_syntax_objects,vmlib,ast,info

(** {6 Iterators} *)

let iter_all_interp_segments f =
  let rec apply_obj prefix obj = match obj with
    | IncludeObject aobjs ->
      let objs = InterpVisitor.expand_aobjs aobjs in
      List.iter (apply_obj prefix) objs
    | _ -> f prefix obj
  in
  let rec subst_view (obj : exp_substituted_object) : Libobject.t = match obj with
  | KeepObject (_, o) | EscapeObject (_, o) -> Empty.abort o
  | (AtomicObject _ | ExportObject _ | ModuleObject _ | ModuleTypeObject _) as o -> o
  | IncludeObject aobjs ->
    let aobjs = aobjs.exp_algebraic_objects in
    IncludeObject (Objs (List.map subst_view aobjs))
  in
  let apply_mod_obj _ modobjs =
    let prefix = modobjs.module_prefix in
    List.iter (fun obj -> apply_obj prefix (subst_view obj)) modobjs.module_substituted_objects;
    List.iter (fun obj -> apply_obj prefix obj) modobjs.module_keep_objects.keep_objects
  in
  let apply_nodes (node, os) = List.iter (fun o -> apply_obj (Lib.node_prefix node) o) os in
  ModPath.Map.iter apply_mod_obj (InterpVisitor.ModObjs.all ());
  List.iter apply_nodes (Lib.contents ())


(** {6 Some types used to shorten declaremods.mli} *)

type module_params = (lident list * (Constrexpr.module_ast * inline)) list
type module_expr = (Modintern.module_struct_expr * ModPath.t * Modintern.module_kind * Entries.inline)
type module_params_expr = (MBId.t list * module_expr) list

(** {6 Debug} *)

let debug_print_modtab () = InterpVisitor.debug_print_modtab ()

(** For printing modules, [process_module_binding] adds names of
    bound module (and its components) to Nametab. It also loads
    objects associated to it. *)

let process_module_binding mbid me =
  let sp = Libnames.make_path DirPath.empty (MBId.to_id mbid) in
  let mp = MPbound mbid in
  let sobjs = InterpVisitor.get_module_sobjs false (Global.env()) (default_inline_level ()) me in
  let subst = map_mp (get_module_path me) mp (empty_delta_resolver mp) in
  let sobjs = subst_sobjs subst sobjs in
  SynterpVisitor.load_module 1 sp mp sobjs;
  InterpVisitor.load_module 1 sp mp sobjs

let () = append_end_library_hook Profile_tactic.do_print_results_at_close
