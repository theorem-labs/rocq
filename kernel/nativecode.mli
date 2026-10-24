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

(** The kernel switch of coqchk's native conversion; off by default.
    While it is on, [Typeops.check_cast] decides [VMcast]s with native
    code, and the printed code names globals injectively, from the bytes
    [A-Za-z0-9_] only. coqc leaves it off, so the names of the
    [.coq-native] units it writes and links do not change.
    [set_native_vm_conversion] raises an anomaly when it would change the
    switch after native code was loaded. *)
val native_vm_conversion : unit -> bool
val set_native_vm_conversion : bool -> unit

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

type code_location_updates
type linkable_code = global list * symbols * code_location_updates

val empty_updates : code_location_updates

val register_native_file : string -> unit

val is_loaded_native_file : string -> bool

val compile_constant_field : cenv -> env -> Constant.t ->
  global list -> constant_body -> global list

val compile_mind_field : cenv -> ModPath.t -> Id.t ->
  global list -> mutual_inductive_body -> global list

val compile_rewrite_rules : env -> Id.t ->
  global list -> rewrite_rules_body -> global list

val mk_conv_code : env -> Genlambda.evars -> string -> constr -> constr -> linkable_code
val mk_norm_code : env -> Genlambda.evars -> string -> constr -> linkable_code

(** {6 For the checker's unit cache} (see checker/convCache.ml) *)

(** A definition a unit defines. *)
type definition = Dconst of Constant.t | Dind of MutInd.t

val definition_equal : definition -> definition -> bool
val definition_compare : definition -> definition -> int
val definition_to_string : definition -> string

(** [closure_graph env sigma ts] is what [mk_deps_code] would emit for
    [ts], without generating anything: each definition the code of [ts]
    reaches, with the globals its own code names directly, callees before
    callers. Definitions already linked in this process are in it too. *)
val closure_graph :
  env -> Genlambda.evars -> constr list -> (definition * definition list) list

(** The globals the code of one definition names directly. *)
val direct_references : env -> Genlambda.evars -> definition -> definition list

val definition_is_linked : env -> definition -> bool
val definition_prefix : env -> definition -> string option

(** [mk_deps_code env sigma prefix t1 t2] is the code of a unit of the
    cache: the closure of [t1] and [t2] that this process has not linked,
    with no conversion term, so loading it runs no conversion. It carries
    its own symbols. *)
val mk_deps_code : env -> Genlambda.evars -> string -> constr -> constr -> linkable_code

val definitions_of_updates : code_location_updates -> definition list

(** [link_definitions env prefix defs] marks [defs] as defined by the unit
    of [prefix]. The caller marks only what it has checked. *)
val link_definitions : env -> string -> definition list -> unit

(** [unlink_definitions env defs] marks [defs] as defined by no unit, so
    that the next unit this process generates emits them again. *)
val unlink_definitions : env -> definition list -> unit

val mk_library_header : Nativevalues.symbols -> global list

val mod_uid_of_dirpath : DirPath.t -> string

val link_info_of_dirpath : DirPath.t -> link_info

val update_locations : code_location_updates -> unit

val add_header_comment : global list -> string -> global list
