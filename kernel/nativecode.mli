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
open Constr
open Declarations
open Environ
open Nativevalues

(** This file defines the mllambda code generation phase of the native
compiler. mllambda represents a fragment of ML, and can easily be printed
to OCaml code. *)

type cenv

val make_cenv : unit -> cenv
val get_cenv_symbols : cenv -> symbols

type global

val debug_native_compiler : CDebug.t

val keep_debug_files : unit -> bool

val pp_global : Format.formatter -> global -> unit

val mk_open : string -> global

val get_value : symbols -> int -> Nativevalues.t

val get_sort : symbols -> int -> Sorts.t

val get_name : symbols -> int -> Name.t

val get_const : symbols -> int -> Constant.t

val get_match : symbols -> int -> Nativevalues.annot_sw

val get_ind : symbols -> int -> inductive

val get_evar : symbols -> int -> Evar.t

val get_instance : symbols -> int -> UVars.Instance.t

val get_proj : symbols -> int -> inductive * int

(** A constant or inductive whose native code is not loaded yet. *)
type plan_item

val describe_item : plan_item -> string

(** Canonical name of the item (the kernel name of the constant or
    inductive). *)
val item_key : plan_item -> string

(** Name under which the item's code defines its main value, as it appears in
    the generated source. Two items with different [item_key] and the same
    [item_def_name] would shadow each other. *)
val item_def_name : plan_item -> string

(** [plan_deps env sigma ts]: every constant and inductive reachable from
    [ts] whose code is not loaded, each once, with its dependency level
    (inductives and constants without dependencies are level 0, a constant
    is 1 + the highest level it refers to). Ordered by (level, name), a
    function of the set of items only; items of one level never refer to
    each other. *)
val plan_deps : env -> Genlambda.evars -> constr list -> (int * plan_item) list

(** A compilation unit under construction: its own name/symbol environment. *)
type unit_builder

val new_unit : unit -> unit_builder

(** The first global of every unit (binds [symbols_tbl]). *)
val unit_header : global

(** The globals defining the item, in definition order. *)
val unit_add_item : unit_builder -> env -> Genlambda.evars -> plan_item -> global list

val unit_symbols : unit_builder -> symbols

(** [link_items items prefix]: from now on the code of every item is referred
    to as [prefix ^ name] (the unit that defines them is loaded). *)
val link_items : plan_item list -> string -> unit

val register_native_file : string -> unit

val is_loaded_native_file : string -> bool

val compile_constant_field : cenv -> env -> Constant.t ->
  global list -> constant_body -> global list

val compile_mind_field : cenv -> ModPath.t -> Id.t ->
  global list -> mutual_inductive_body -> global list

val compile_rewrite_rules : env -> Id.t ->
  global list -> rewrite_rules_body -> global list

(** [mk_conv_code env sigma t1 t2] is the code of the cast's own unit and its
    symbol table. Every dependency of [t1] and [t2] must already be linked
    ({!Nativelib.link_dependencies}); an anomaly is raised otherwise. *)
val mk_conv_code : env -> Genlambda.evars -> constr -> constr -> global list * symbols
val mk_norm_code : env -> Genlambda.evars -> constr -> global list * symbols

val mk_library_header : Nativevalues.symbols -> global list

val mod_uid_of_dirpath : DirPath.t -> string

val link_info_of_dirpath : DirPath.t -> link_info

val add_header_comment : global list -> string -> global list
