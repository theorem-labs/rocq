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
open Libnames
open Tac2expr
open Tac2val

type global_data = {
  gdata_expr : glb_tacexpr;
  gdata_type : type_scheme;
  gdata_mutable : bool;
  gdata_deprecation : Deprecation.t option;
  gdata_mutation_history : ModPath.t list;
}

type constructor_data = {
  cdata_prms : int;
  cdata_type : type_constant;
  cdata_args : int glb_typexpr list;
  cdata_indx : int option;
}

type projection_data = {
  pdata_prms : int;
  pdata_type : type_constant;
  pdata_ptyp : int glb_typexpr;
  pdata_mutb : bool;
  pdata_indx : int;
}

type alias_data = {
  alias_body : raw_tacexpr;
  alias_depr : Deprecation.t option;
}

type ltac_state = {
  ltac_tactics : global_data KerName.Map.t;
  ltac_constructors : constructor_data KerName.Map.t;
  ltac_projections : projection_data KerName.Map.t;
  ltac_types : glb_quant_typedef KerName.Map.t;
  ltac_aliases : alias_data KerName.Map.t;
}

let empty_state = {
  ltac_tactics = KerName.Map.empty;
  ltac_constructors = KerName.Map.empty;
  ltac_projections = KerName.Map.empty;
  ltac_types = KerName.Map.empty;
  ltac_aliases = KerName.Map.empty;
}

type compile_info = {
  source : string;
}

let ltac_state = Summary.ref empty_state ~name:"ltac2-state"

let compiled_tacs = Summary.ref ~local:true ~name:"ltac2-compiled-state" KerName.Map.empty

type notation_data =
  | UntypedNota of raw_tacexpr
  | TypedNota of {
      nota_prms : int;
      nota_argtys : int glb_typexpr Id.Map.t;
      nota_ty : int glb_typexpr;
      nota_body : glb_tacexpr;
    }

let ltac_notations = Summary.ref KerName.Map.empty ~name:"ltac2-notations"

let define_global kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_tactics = KerName.Map.add kn e state.ltac_tactics }

let interp_global kn =
  let data = KerName.Map.find kn ltac_state.contents.ltac_tactics in
  data

let set_compiled_global kn info v =
  assert (not (interp_global kn).gdata_mutable);
  compiled_tacs := KerName.Map.add kn (info,v) !compiled_tacs

let get_compiled_global kn = KerName.Map.find_opt kn !compiled_tacs

let compiled_globals () = !compiled_tacs

let globals () = (!ltac_state).ltac_tactics

let define_constructor kn t =
  let state = !ltac_state in
  ltac_state := {
    state with
    ltac_constructors = KerName.Map.add kn t state.ltac_constructors;
  }

let interp_constructor kn = KerName.Map.find kn ltac_state.contents.ltac_constructors

let find_all_constructors_in_type kn =
  KerName.Map.filter (fun _ data -> KerName.equal kn data.cdata_type) (!ltac_state).ltac_constructors

let define_projection kn t =
  let state = !ltac_state in
  ltac_state := { state with ltac_projections = KerName.Map.add kn t state.ltac_projections }

let interp_projection kn = KerName.Map.find kn ltac_state.contents.ltac_projections

let define_type kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_types = KerName.Map.add kn e state.ltac_types }

let interp_type kn = KerName.Map.find kn ltac_state.contents.ltac_types

let define_alias ?deprecation kn tac =
  let state = !ltac_state in
  let data = { alias_body = tac; alias_depr = deprecation } in
  ltac_state := { state with ltac_aliases = KerName.Map.add kn data state.ltac_aliases }

let interp_alias kn = KerName.Map.find kn ltac_state.contents.ltac_aliases

let define_notation kn tac =
  ltac_notations := KerName.Map.add kn tac !ltac_notations

let interp_notation kn = KerName.Map.find kn !ltac_notations

(** The table of ML primitives. It is looked up on every [GTacPrm] node the
    interpreter evaluates, so it is a hash table rather than a map ordered by
    string comparison. Nothing iterates over it. *)
module MLTbl = Hashtbl.Make(struct
  type t = ml_tactic_name
  let equal n1 n2 =
    String.equal n1.mltac_tactic n2.mltac_tactic &&
    String.equal n1.mltac_plugin n2.mltac_plugin
  let hash (n : t) = Hashtbl.hash n
end)

let primitive_table : valexpr MLTbl.t = MLTbl.create 1024

(** Counts the definitions of a primitive. A reader of [interp_primitive] that keeps what it read
    compares this count to tell a table it has not read since from one it has. *)
let primitive_defs = ref 0

let define_primitive name f =
  let f = match f with
    | ValCls f -> ValCls (annotate_closure (FrPrim name) f)
    | _ -> f
  in
  incr primitive_defs;
  MLTbl.replace primitive_table name f
let interp_primitive name = MLTbl.find primitive_table name
let primitive_definitions () = !primitive_defs

(** Name management *)

type tacref = Tac2expr.tacref =
| TacConstant of ltac_constant
| TacAlias of ltac_alias

module TacRef =
struct
type t = tacref
let compare r1 r2 = match r1, r2 with
| TacConstant c1, TacConstant c2 -> KerName.compare c1 c2
| TacAlias c1, TacAlias c2 -> KerName.compare c1 c2
| TacConstant _, TacAlias _ -> -1
| TacAlias _, TacConstant _ -> 1

let equal r1 r2 = compare r1 r2 == 0
end

module DefV = struct
  include TacRef
  let is_var _ = None
  let stage = Summary.Stage.Interp
  let summary_name = "ltac2-deftab"
  module Map = Map.Make(TacRef)
end
module DefTab = Nametab.EasyNoWarn(DefV)()

module CtorV = struct
  include KerName
  let is_var _ = None
  module Map = KerName.Map
  let stage = Summary.Stage.Interp
  let summary_name = "ltac2-ctortab"
  let object_name = "Ltac2 constructor"
  let warning_name_base = "ltac2-constructor"
end
module CtorTab = Nametab.Easy(CtorV)()

module TypV = struct
  include KerName
  let is_var _ = None
  let stage = Summary.Stage.Interp
  let summary_name = "ltac2-typtab"
  module Map = KerName.Map
end
module TypTab = Nametab.EasyNoWarn(TypV)()

module ProjV = struct
  include KerName
  let is_var _ = None
  let stage = Summary.Stage.Interp
  let summary_name = "ltac2-projtab"
  module Map = KerName.Map
end
module ProjTab = Nametab.EasyNoWarn(ProjV)()

let push_ltac = DefTab.push

let locate_ltac = DefTab.locate

let locate_extended_all_ltac = DefTab.locate_all

let path_of_ltac = DefTab.to_path

let shortest_qualid_of_ltac = DefTab.shortest_qualid

let push_constructor ?user_warns vis sp kn =
  (* XXX support qf *)
  let user_warns = Option.map UserWarn.with_empty_qf user_warns in
  CtorTab.push ?wdata:user_warns vis sp kn

(* XXX expose nowarn argument? *)
let locate_constructor qid = CtorTab.locate qid

let locate_extended_all_constructor = CtorTab.locate_all

let path_of_constructor = CtorTab.to_path

let shortest_qualid_of_constructor kn = CtorTab.shortest_qualid Id.Set.empty kn

let push_type = TypTab.push

let locate_type = TypTab.locate

let locate_extended_all_type = TypTab.locate_all

let path_of_type = TypTab.to_path

let shortest_qualid_of_type ?loc kn = TypTab.shortest_qualid Id.Set.empty ?loc kn

let push_projection = ProjTab.push

let locate_projection = ProjTab.locate

let locate_extended_all_projection = ProjTab.locate_all

let shortest_qualid_of_projection kn = ProjTab.shortest_qualid Id.Set.empty kn

type 'a or_glb_tacexpr =
| GlbVal of 'a
| GlbTacexpr of glb_tacexpr

(** The interpreter's environment. It holds the binders that lexically enclose the expression
    being run, which are usually few, so the newest bindings sit in a chain, newest first, where
    a binding costs one allocation and a lookup is a few pointer tests (identifiers are
    hashconsed). The chain holds at most [bound] bindings; the older ones sit in an [Id.Map]
    under it, so a lookup is never worse than [bound] tests plus the [Id.Map] lookup, and
    shadowed bindings are dropped as [Id.Map.add] drops them. A binding shadows every older one
    of the same name, in the chain and in the map, so each lookup returns what [Id.Map] would. *)
module IdMap =
struct
  type key = Id.t
  type 'a t =
  | Base of 'a Id.Map.t
  | Bind of { id : key; v : 'a; depth : int; next : 'a t; mutable merged : 'a Id.Map.t option }
  (** [depth] counts the [Bind] nodes from this one down to the [Base]. [merged] memoizes the map
      of every binding of the node, so that extending one full chain many times (a closure whose
      environment is full, called many times) merges it once. *)

  let bound = 16

  let empty = Base Id.Map.empty

  let rec find id = function
  | Base m -> Id.Map.find id m
  | Bind b -> if id == b.id || Id.equal id b.id then b.v else find id b.next

  let rec find_opt id = function
  | Base m -> Id.Map.find_opt id m
  | Bind b -> if id == b.id || Id.equal id b.id then Some b.v else find_opt id b.next

  let rec mem id = function
  | Base m -> Id.Map.mem id m
  | Bind b -> id == b.id || Id.equal id b.id || mem id b.next

  let rec get id = function
  | Base m -> Id.Map.get id m
  | Bind b -> if id == b.id || Id.equal id b.id then b.v else get id b.next

  (* The map of every binding of a chain, the newest winning. *)
  let rec merge = function
  | Base m -> m
  | Bind b -> Id.Map.add b.id b.v (merge b.next)

  let add id v t = match t with
  | Base _ -> Bind { id; v; depth = 1; next = t; merged = None }
  | Bind b ->
    if b.depth < bound then Bind { id; v; depth = b.depth + 1; next = t; merged = None }
    else
      let m = match b.merged with
      | Some m -> m
      | None -> let m = merge t in b.merged <- Some m; m
      in
      Bind { id; v; depth = 1; next = Base m; merged = None }

  (** [push id v t] binds [id] to [v] as [add] does, without merging the chain into a map: the
      chain then grows with each binding. Compiled Ltac2 code ([Tac2interp]) binds with it: its
      lookups read a known position of the chain ([Tac2interp.compile_simple]), and its chains
      are as long as the binders that lexically enclose an expression, which the program text
      bounds. *)
  let push id v t =
    let depth = match t with Base _ -> 1 | Bind b -> b.depth + 1 in
    Bind { id; v; depth; next = t; merged = None }
end

type environment = {
  env_ist : valexpr IdMap.t;
}

type ('a, 'b, 'r) intern_fun = Genintern.glob_sign -> 'a -> 'b * 'r glb_typexpr

type ('a, 'b) ml_object = {
  ml_intern : 'r. ('a, 'b or_glb_tacexpr, 'r) intern_fun;
  ml_subst : Mod_subst.substitution -> 'b -> 'b;
  ml_interp : environment -> 'b -> valexpr Proofview.tactic;
  ml_print : Environ.env -> Evd.evar_map -> 'b -> Pp.t;
  ml_raw_print : Environ.env -> Evd.evar_map -> 'a -> Pp.t;
}

module MLTypeObj =
struct
  type ('a, 'b) t = ('a, 'b) ml_object
end

module MLType = Tac2dyn.ArgMap(MLTypeObj)

let ml_object_table = ref MLType.empty

let define_ml_object t tpe =
  ml_object_table := MLType.add t (MLType.Pack tpe) !ml_object_table

let interp_ml_object t =
  try
    let MLType.Pack ans = MLType.find t !ml_object_table in
    ans
  with Not_found ->
    CErrors.anomaly Pp.(str "Unknown object type " ++ str (Tac2dyn.Arg.repr t))

(** Absolute paths *)

let rocq_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Init"; "Ltac2"]))

let coq_prefix = rocq_prefix

let std_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Std"; "Ltac2"]))

let ltac1_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Ltac1"; "Ltac2"]))

(** Generic arguments *)

type var_quotation_kind =
  | ConstrVar
  | PretermVar
  | PatternVar
  | HypVar

let wit_ltac2_constr = Genarg.make0 "ltac2:in-constr"
let wit_ltac2_var_quotation = Genarg.make0 "ltac2:quotation"
let wit_ltac2_tac = Genarg.make0 "ltac2:tactic"

let () = Geninterp.register_val0 wit_ltac2_tac
    (Some (Geninterp.val_tag (Genarg.topwit Stdarg.wit_unit)))

let is_constructor_id id =
  let id = Id.to_string id in
  assert (String.length id > 0);
  match id with
  | "true" | "false" -> true (* built-in constructors *)
  | _ ->
    match id.[0] with
    | 'A'..'Z' -> true
    | _ -> false

let is_constructor qid =
  let (_, id) = repr_qualid qid in
  is_constructor_id id
