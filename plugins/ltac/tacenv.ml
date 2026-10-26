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
open Pp
open Names
open Tacexpr

(** Nametab for tactics *)

module TacticV = struct
  include KerName
  let is_var _ = None
  module Map = KerName.Map
  let stage = Summary.Stage.Interp
  let summary_name = "ltac1tab"
end
module TacticTab = Nametab.EasyNoWarn(TacticV)()

let push_tactic vis sp kn = TacticTab.push vis sp kn

let locate_tactic qid = TacticTab.locate qid

let locate_extended_all_tactic qid = TacticTab.locate_all qid

let exists_tactic kn = TacticTab.exists kn

let path_of_tactic kn = TacticTab.to_path kn

let shortest_qualid_of_tactic kn = TacticTab.shortest_qualid Id.Set.empty kn

(** Tactic notations (TacAlias) *)

type alias = KerName.t
type alias_tactic =
  { alias_args: Id.t list;
    alias_body: glob_tactic_expr;
    alias_deprecation: Deprecation.t option;
  }

let alias_map = Summary.ref ~name:"tactic-alias"
  (KerName.Map.empty : alias_tactic KerName.Map.t)

let register_alias key tac =
  alias_map := KerName.Map.add key tac !alias_map

(* BET-84 census row 9: each Ltac alias and definition the proof reads. *)
let record channel k v =
  if Proof_recorder.active () then
    Proof_recorder.read_by ~row:"9" ~channel ~id:k ~key:(fun () -> KerName.to_string k)
      ~value:(fun () -> match v with
          | None -> None
          | Some v -> Some (Proof_recorder.digest ~what:channel v))

(* The lookup itself must build no option when the recorder is off: these run
   at every call of a tactic notation. [record] is reached with an already
   allocated [Some] only under [active]. *)
let interp_alias key =
  match KerName.Map.find key !alias_map with
  | v ->
    if Proof_recorder.active () then record "tactic_alias" key (Some v);
    v
  | exception Not_found ->
    record "tactic_alias" key None;
    CErrors.anomaly (str "Unknown tactic alias: " ++ KerName.print key ++ str ".")

let check_alias key =
  match KerName.Map.find key !alias_map with
  | v ->
    if Proof_recorder.active () then record "tactic_alias" key (Some v);
    true
  | exception Not_found ->
    record "tactic_alias" key None;
    false

(** ML tactic extensions (TacML) *)

type ml_tactic =
  Geninterp.Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic

module MLName =
struct
  type t = ml_tactic_name
  let compare tac1 tac2 =
    let c = String.compare tac1.mltac_tactic tac2.mltac_tactic in
    if c = 0 then String.compare tac1.mltac_plugin tac2.mltac_plugin
    else c
end

module MLTacMap = Map.Make(MLName)

let pr_tacname t =
  str t.mltac_plugin ++ str "::" ++ str t.mltac_tactic

let tac_tab = ref MLTacMap.empty

(* BET-84: [~overwrite:true] puts another closure under a name that is
   already registered, possibly the name of one of this tree's plugins, which
   [Tacinterp.fence_ml_tactic] trusts by name. Rocq never overwrites, so a
   replacement makes every later proof of the process ineligible
   (Proof_recorder.closure_setter; Claude review of 467292ce69, finding 2). *)
let ml_tactic_overwritten =
  Proof_recorder.closure_setter ~what:"Tacenv.register_ml_tactic ~overwrite" ~stock:0

let register_ml_tactic ?(overwrite = false) s (t : ml_tactic array) =
  let () =
    if MLTacMap.mem s !tac_tab then
      if overwrite then begin
        ml_tactic_overwritten ();
        tac_tab := MLTacMap.remove s !tac_tab
      end
      else
        CErrors.anomaly (str "Cannot redeclare tactic " ++ pr_tacname s ++ str ".")
  in
  tac_tab := MLTacMap.add s t !tac_tab

let interp_ml_tactic { mltac_name = s; mltac_index = i } =
  try
    let tacs = MLTacMap.find s !tac_tab in
    let () = if Array.length tacs <= i then raise Not_found in
    tacs.(i)
  with Not_found ->
    CErrors.user_err
      (str "The tactic " ++ pr_tacname s ++ str " is not installed.")

(***************************************************************************)
(* Tactic registration *)

(* Summary and Object declaration *)

open Libobject

type ltac_entry = {
  tac_for_ml : bool;
  tac_body : glob_tactic_expr;
  tac_redef : ModPath.t list;
  tac_deprecation : Deprecation.t option
}

let mactab =
  Summary.ref (KerName.Map.empty : ltac_entry KerName.Map.t)
    ~name:"tactic-definition"

let ltac_entries () = !mactab

let interp_ltac r =
  match KerName.Map.find r !mactab with
  | e ->
    if Proof_recorder.active () then record "tactic_definition" r (Some e);
    e.tac_body
  | exception Not_found ->
    record "tactic_definition" r None;
    raise Not_found

let is_ltac_for_ml_tactic r =
  match KerName.Map.find r !mactab with
  | e ->
    if Proof_recorder.active () then record "tactic_definition" r (Some e);
    e.tac_for_ml
  | exception Not_found ->
    record "tactic_definition" r None;
    raise Not_found

let add ~depr kn b t =
  let entry = {
    tac_for_ml = b;
    tac_body = t;
    tac_redef = [];
    tac_deprecation = depr;
  }
  in
  mactab := KerName.Map.add kn entry !mactab

let replace kn path t =
  let entry _ e = { e with tac_body = t; tac_redef = path :: e.tac_redef } in
  mactab := KerName.Map.modify kn entry !mactab

let tac_deprecation kn =
  try (KerName.Map.find kn !mactab).tac_deprecation with Not_found -> None

type tacdef = {
  local : bool;
  id : Id.t;
  for_ml : bool;
  expr : glob_tactic_expr;
  depr : Deprecation.t option;
}

let load_md i (prefix, {local; id; for_ml=b; expr=t; depr}) =
  let sp, kn = Lib.make_oname prefix id in
  let () = if not local then push_tactic (Nametab.Until i) sp kn in
  add ~depr kn b t

let open_md i (prefix, {local; id; for_ml=b; expr=t; depr}) =
  (* todo: generate a warning when non-unique, record choices for non-unique mappings *)
  let sp, kn = Lib.make_oname prefix id in
  let () = if not local then push_tactic (Nametab.Exactly i) sp kn in
  ()

let cache_md (prefix, {local; id; for_ml=b; expr=t; depr}) =
  let sp, kn = Lib.make_oname prefix id in
  let () = push_tactic (Nametab.Until 1) sp kn in
  add ~depr kn b t

let subst_md (subst, {local; id; for_ml; expr=t; depr}) =
  {local; id; for_ml; expr=Tacsubst.subst_tactic subst t; depr}

let classify_md _ = Substitute

let inMD : tacdef -> obj =
  declare_named_object_gen {(default_object "TAC-DEFINITION") with
     cache_function = cache_md;
     load_function = load_md;
     open_function = filtered_open open_md;
     subst_function = subst_md;
     classify_function = classify_md}

let register_ltac for_ml local ?deprecation id tac =
  Lib.add_leaf (inMD {local; id; for_ml; expr=tac; depr=deprecation})

type tacreplace = {
  repl_local : Libobject.locality;
  repl_tac : ltac_constant;
  repl_expr : glob_tactic_expr;
}

let load_replace i (prefix, {repl_local; repl_tac; repl_expr=t}) =
  match repl_local with
  | Local | Export -> ()
  | SuperGlobal ->
    replace repl_tac prefix.obj_mp t

let open_replace i (prefix, {repl_local; repl_tac; repl_expr=t}) =
  match repl_local with
  | Local | SuperGlobal -> ()
  | Export ->
    replace repl_tac prefix.obj_mp t

let cache_replace (prefix, {repl_local; repl_tac; repl_expr=t}) =
  replace repl_tac prefix.obj_mp t

let subst_replace (subst, {repl_local; repl_tac; repl_expr}) =
  { repl_local;
    repl_tac=Mod_subst.subst_kn subst repl_tac;
    repl_expr=Tacsubst.subst_tactic subst repl_expr;
  }

let classify_replace o = match o.repl_local with
  | Local -> Dispose
  | Export | SuperGlobal -> Substitute

let inReplace : tacreplace -> obj =
  declare_named_object_gen {(default_object "TAC-REDEFINITION") with
     cache_function = cache_replace;
     load_function = load_replace;
     (* should this be simple_open ie only redefine when importing the
        module containing the redef instead of a parent? *)
     open_function = filtered_open open_replace;
     subst_function = subst_replace;
     classify_function = classify_replace}

let redefine_ltac repl_local repl_tac repl_expr =
  Lib.add_leaf (inReplace {repl_local; repl_tac; repl_expr})
