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

(* BET-84 census row 10: each Ltac2 definition the proof reads, keyed by its
   kernel name as [Libnames.kername_key] writes it ([KerName.to_string] is not
   injective). ONE value function for the six channels, called by the
   record sites and by the replay evaluators
   (dev/tools/census/replay_channels.py): the digest of what [tbl] holds
   for [k], or absent. *)
let recorded_ltac2 channel tbl k =
  match KerName.Map.find_opt k tbl with
  | None -> None
  | Some v -> Some (Proof_recorder.digest ~what:channel v)

let record ~channel tbl k =
  if Proof_recorder.active () then
    Proof_recorder.read_by ~row:"10" ~channel ~id:k ~key:(fun () -> Libnames.kername_key k)
      ~value:(fun () -> recorded_ltac2 channel tbl k)

(* Ltac2 interpretation resolves a name at every call, so the lookup itself
   must build nothing when the recorder is off: [record] is reached only
   under [active], or on the failing lookup. *)
let find ~channel tbl kn =
  match KerName.Map.find kn tbl with
  | v ->
    if Proof_recorder.active () then record ~channel tbl kn;
    v
  | exception Not_found ->
    record ~channel tbl kn;
    raise Not_found

let interp_global kn = find ~channel:"ltac2_global" ltac_state.contents.ltac_tactics kn

let () =
  Proof_replay.register_evaluator "ltac2_global" (fun key ->
      match Libnames.kername_of_key key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_ltac2 "ltac2_global" ltac_state.contents.ltac_tactics k))

(* The other tables of the Ltac2 state, read the same way. A proof that runs
   an Ltac2 definition also reads the types, constructors and projections
   its code names, so evaluating [ltac2_global] alone replays nothing. *)
let () =
  Proof_replay.register_evaluator "ltac2_type" (fun key ->
      match Libnames.kername_of_key key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_ltac2 "ltac2_type" ltac_state.contents.ltac_types k))

let () =
  Proof_replay.register_evaluator "ltac2_constructor" (fun key ->
      match Libnames.kername_of_key key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_ltac2 "ltac2_constructor" ltac_state.contents.ltac_constructors k))

let () =
  Proof_replay.register_evaluator "ltac2_projection" (fun key ->
      match Libnames.kername_of_key key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_ltac2 "ltac2_projection" ltac_state.contents.ltac_projections k))

let () =
  Proof_replay.register_evaluator "ltac2_alias" (fun key ->
      match Libnames.kername_of_key key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_ltac2 "ltac2_alias" ltac_state.contents.ltac_aliases k))

(* Its one caller tests [active] first; [record] tests it again, so that no
   caller can make the lookup record with the recorder off. *)
let record_global kn = record ~channel:"ltac2_global" ltac_state.contents.ltac_tactics kn

(* BET-84: [Tac2interp.eval_global] runs the closure stored here in place of
   the global's definition, and row 10 records the definition only. Nothing
   in this tree calls this, so every entry is a plugin's closure, and the
   first one makes every later proof of the process ineligible
   (Proof_recorder.closure_setter; Claude review of e16e9d2ae4, finding 1). *)
let compiled_global_set =
  Proof_recorder.closure_setter ~what:"Tac2env.set_compiled_global" ~stock:0

let set_compiled_global kn info v =
  assert (not (interp_global kn).gdata_mutable);
  compiled_global_set ();
  compiled_tacs := KerName.Map.add kn (info,v) !compiled_tacs

let get_compiled_global kn = KerName.Map.find_opt kn !compiled_tacs

let globals () = (!ltac_state).ltac_tactics

let define_constructor kn t =
  let state = !ltac_state in
  ltac_state := {
    state with
    ltac_constructors = KerName.Map.add kn t state.ltac_constructors;
  }

let interp_constructor kn = find ~channel:"ltac2_constructor" ltac_state.contents.ltac_constructors kn

let find_all_constructors_in_type kn =
  KerName.Map.filter (fun _ data -> KerName.equal kn data.cdata_type) (!ltac_state).ltac_constructors

let define_projection kn t =
  let state = !ltac_state in
  ltac_state := { state with ltac_projections = KerName.Map.add kn t state.ltac_projections }

let interp_projection kn = find ~channel:"ltac2_projection" ltac_state.contents.ltac_projections kn

let define_type kn e =
  let state = !ltac_state in
  ltac_state := { state with ltac_types = KerName.Map.add kn e state.ltac_types }

let interp_type kn = find ~channel:"ltac2_type" ltac_state.contents.ltac_types kn

let define_alias ?deprecation kn tac =
  let state = !ltac_state in
  let data = { alias_body = tac; alias_depr = deprecation } in
  ltac_state := { state with ltac_aliases = KerName.Map.add kn data state.ltac_aliases }

let interp_alias kn = find ~channel:"ltac2_alias" ltac_state.contents.ltac_aliases kn

let define_notation kn tac =
  ltac_notations := KerName.Map.add kn tac !ltac_notations

let interp_notation kn = find ~channel:"ltac2_notation" !ltac_notations kn

let () =
  Proof_replay.register_evaluator "ltac2_notation" (fun key ->
      match Libnames.kername_of_key key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_ltac2 "ltac2_notation" !ltac_notations k))

module ML =
struct
  type t = ml_tactic_name
  let compare n1 n2 =
    let c = String.compare n1.mltac_plugin n2.mltac_plugin in
    if Int.equal c 0 then String.compare n1.mltac_tactic n2.mltac_tactic
    else c
end

module MLMap = Map.Make(ML)

(* ML tactic package suffixes built below [plugins/]. Some directories build
   multiple packages. The compatibility names load the same audited code. An
   ML tactic from any other package is code the census did not audit, so a
   proof that runs it is never replayed. *)
let audited_ml_tactic_plugin_suffixes =
  [ "btauto";
    "cc";
    "cc_core";
    "derive";
    "extraction";
    "firstorder";
    "firstorder_core";
    "funind";
    "ltac";
    "ltac2";
    "ltac2_ltac1";
    "micromega";
    "micromega_core";
    "nsatz";
    "nsatz_core";
    "number_string_notation";
    "ring";
    "rtauto";
    "ssreflect";
    "ssrmatching";
    "tauto";
    "zify" ]

let audited_ml_tactic_plugins =
  List.fold_left
    (fun set suffix ->
       String.Set.add ("coq-core.plugins." ^ suffix)
         (String.Set.add ("rocq-runtime.plugins." ^ suffix) set))
    String.Set.empty audited_ml_tactic_plugin_suffixes

let fence_primitive { mltac_plugin; mltac_tactic } =
  if Proof_recorder.active () &&
     not (String.Set.mem mltac_plugin audited_ml_tactic_plugins)
  then
    Proof_recorder.ineligible ~reason:"ml_tactic"
      ~detail:(mltac_plugin ^ "." ^ mltac_tactic)

let primitive_map = ref MLMap.empty

(* BET-84: a second definition of a primitive replaces its closure under an
   unchanged name, possibly an audited plugin's, which [fence_primitive]
   trusts by name, and row 10 records the source definitions only. Rocq
   defines each primitive once, so a redefinition makes every later proof of
   the process ineligible (Proof_recorder.closure_setter; Claude review of
   beb759fef3, finding 1). *)
let primitive_redefined =
  Proof_recorder.closure_setter ~what:"Tac2env.define_primitive" ~stock:0

let define_primitive name f =
  let f = match f with
    | ValCls f -> ValCls (annotate_closure (FrPrim name) f)
    | _ -> f
  in
  if MLMap.mem name !primitive_map then primitive_redefined ();
  primitive_map := MLMap.add name f !primitive_map
let interp_primitive name =
  fence_primitive name;
  MLMap.find name !primitive_map

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

type environment = {
  env_ist : valexpr Id.Map.t;
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

(* BET-84: as for [define_primitive]: the ML object behind a quotation is
   defined once per tag by Rocq. *)
let ml_object_redefined =
  Proof_recorder.closure_setter ~what:"Tac2env.define_ml_object" ~stock:0

let define_ml_object t tpe =
  if MLType.mem t !ml_object_table then ml_object_redefined ();
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
