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

type vodigest =
  | Dvo_or_vi of Digest.t        (* The digest of the seg_lib part *)

val digest_match : actual:vodigest -> required:vodigest -> bool

(** binary-equivalence-taiga#841 D1/D3/D4: see kernel/safe_typing.ml's doc
    comments on [iface_table], [dep_ok], [check_required]/
    [check_required_strict], and [export]/[import]/[import_strict] for the
    full soundness argument. WIP on branch sami/841-usage-cutoff: D1's full
    transitive-closure field ([comp_transitive_deps]) is not yet present
    here -- it lands with commit 1 on sami/861-loc-free-identity, which
    this branch rebases onto. Until then [comp_deps]/[dep_ok] operate over
    direct roots only, same as stock, so this slice is independently
    buildable but does NOT yet close the Blocker (two-levels-down) on its
    own -- see #841's "Red team, round 1" section. *)
type iface_table = (Id.t * Digest.t) array
val iface_subset_ok : recorded:iface_table -> live:iface_table -> bool
(** Review841 round 3: [vernac_iface] entries use [iface_subset_ok] above
    directly (same keyed shape as the kernel [iface_table]), not a
    separate unkeyed-SET function -- the old [decl_objects_subset_ok] is
    removed; it was the unsound predecessor this round replaced. *)
(** binary-equivalence-taiga#841 Review841 G7: see the doc comment on
    [Safe_typing.used_names_of_needed]/[added_label_collision] in the
    implementation for the full argument. [needed] here is structurally
    the same per-dependency tuple array as a library's own [comp_deps]/
    [md_deps] (not named [library_info], which stays internal) -- every
    one of [dep_ok]'s three call sites (the kernel's own [check_required],
    [vernac/library.ml]'s and [topbin/rocqnative.ml]'s own
    [intern_mandatory_library]) must compute this ONCE from its own full
    dependency array and pass the SAME value into every [dep_ok] call for
    that array, not recompute it per entry. *)
val used_names_of_needed :
  (DirPath.t * vodigest * iface_table option * Digest.t * Digest.t * iface_table) array ->
  Id.Set.t
val dep_ok :
  actual:vodigest -> required:vodigest ->
  actual_iface:iface_table option -> required_iface:iface_table option ->
  actual_objects_digest:Digest.t -> required_objects_digest:Digest.t ->
  actual_univs_digest:Digest.t -> required_univs_digest:Digest.t ->
  actual_vernac_iface:iface_table -> required_vernac_iface:iface_table ->
  used_names:Id.Set.t -> bool

(** {6 Safe environments } *)

(** Since we are now able to type terms, we can define an abstract type
    of safe environments, where objects are typed before being added.

    We also provide functionality for modules : [start_module], [end_module],
    etc.
*)

type safe_environment

type section_data

val empty_environment : safe_environment

val env_of_safe_env : safe_environment -> Environ.env

val sections_of_safe_env : safe_environment -> section_data Section.t option

val structure_body_of_safe_env : safe_environment -> Mod_declarations.structure_body

val flatten_env : safe_environment -> ModPath.t * Mod_declarations.structure_body

(** The safe_environment state monad *)

type safe_transformer0 = safe_environment -> safe_environment
type 'a safe_transformer = safe_environment -> 'a * safe_environment


(** {6 Stm machinery } *)

type private_constants

val debug_print_private_constants : private_constants -> Pp.t

val empty_private_constants : private_constants
val is_empty_private_constants : private_constants -> bool
val length_private : private_constants -> int
val pop_private : private_constants -> int -> private_constants * private_constants

val concat_private : private_constants -> private_constants -> private_constants
(** [concat_private e1 e2] adds the constants of [e1] to [e2], i.e. constants in
    [e1] must be more recent than those of [e2]. *)

val inline_private_constants :
  Environ.env -> private_constants Entries.proof_output -> Constr.constr * Univ.ContextSet.t
(** Abstract the private constants of a proof over the proof output *)

val push_private_constants : Environ.env -> private_constants -> Environ.env
(** Push the constants in the environment if not already there. *)

val universes_of_private : private_constants -> Univ.ContextSet.t

val constants_of_private : private_constants -> Constant.t list

val is_curmod_library : safe_environment -> bool

val is_joined_environment : safe_environment -> bool
(** {6 Enriching a safe environment } *)

(** Insertion of global axioms or definitions *)

type side_effect_declaration =
| DefinitionEff : Entries.definition_entry -> side_effect_declaration
| OpaqueEff : Constr.constr Entries.opaque_entry -> side_effect_declaration

type exported_opaque
type exported_private_constant = Constant.t * exported_opaque option

val repr_exported_opaque : exported_opaque -> Opaqueproof.opaque_handle * Opaqueproof.opaque_proofterm

val export_private_constants :
  private_constants ->
  exported_private_constant list safe_transformer

(** returns the main constant *)
val add_constant :
  ?typing_flags:Declarations.typing_flags ->
  Id.t -> Entries.constant_entry -> Constant.t safe_transformer

(** Similar to add_constant but also returns a certificate *)
val add_private_constant :
  Id.t -> Univ.ContextSet.t -> side_effect_declaration -> (Constant.t * private_constants) safe_transformer

(** {5 Delayed proofs} *)

(** Witness that a delayed Qed hole has a proof. This datatype is marshallable
    but care must be taken to marshal it at the same time as the environment
    it is referring to, since {!fill_opaque} relies on a shared pointer between
    the environment and the certificate. *)
type opaque_certificate

(** Check that the provided proof is correct for the corresponding handle. This
    does not modify the environment. Call {!fill_opaque} below for that. *)
val check_opaque : safe_environment -> Opaqueproof.opaque_handle ->
  private_constants Entries.proof_output -> opaque_certificate

(** Given an already checked proof for an opaque hole, actually fill it with the
    proof. This might fail if the current set of global universes is
    inconsistent with the one at the time of the call to {!check_opaque}.
    Precondition: the underlying handle must exist and must not have been
    filled. *)
val fill_opaque : opaque_certificate -> safe_transformer0

(** Check whether a handle was filled. It assumes that the handle was introduced
    in the opaque table and throws an anomaly otherwise. *)
val is_filled_opaque : Opaqueproof.opaque_handle -> safe_environment -> bool

(** Get the proof term that was checked by the kernel. *)
val repr_certificate : opaque_certificate ->
  Constr.t * Univ.ContextSet.t Opaqueproof.delayed_universes

(** {5 Rewrite rules} *)

(** Add a rewrite rule corresponding to the equality witnessed by the constant. *)
val add_rewrite_rules : Id.t -> Declarations.rewrite_rules_body -> safe_environment -> safe_environment

(** {5 Inductive blocks} *)

(** Adding an inductive type *)

val add_mind :
  ?typing_flags:Declarations.typing_flags ->
  Id.t -> Entries.mutual_inductive_entry ->
  (MutInd.t * IndTyping.NotPrimRecordReason.t option) safe_transformer

(** Adding a module or a module type *)

val add_module :
  Id.t -> Entries.module_entry -> Declarations.inline ->
    (ModPath.t * Mod_subst.delta_resolver) safe_transformer
val add_modtype :
  Id.t -> Entries.module_type_entry -> Declarations.inline ->
    ModPath.t safe_transformer

(** Adding universe constraints *)

val push_context_set :
  strict:bool -> Univ.ContextSet.t -> safe_transformer0

(** Adding global sort qualities *)

val push_qualities : rigid:bool -> Sorts.QContextSet.t -> safe_transformer0

(* (\** Generator of universes *\) *)
(* val next_universe : int safe_transformer *)

(** Setting the type theory flavor *)
val set_rewrite_rules_allowed : bool -> safe_transformer0
val set_impredicative_set : bool -> safe_transformer0
val set_indices_matter : bool -> safe_transformer0
val set_typing_flags : Declarations.typing_flags -> safe_transformer0
val set_share_reduction : bool -> safe_transformer0
val set_check_guarded : bool -> safe_transformer0
val set_check_positive : bool -> safe_transformer0
val set_check_universes : bool -> safe_transformer0
val set_VM : bool -> safe_transformer0
val set_native_compiler : bool -> safe_transformer0
val set_allow_sprop : bool -> safe_transformer0

(** {6 Interactive section functions } *)

val open_section : safe_transformer0

val close_section : safe_transformer0

val sections_are_opened : safe_environment -> bool

(** Insertion of local declarations (Local or Variables) *)

val push_named_assum : (Id.t * Constr.types) -> safe_transformer0

val push_named_def :
  Id.t * Entries.section_def_entry -> safe_transformer0

(** Add local universes to a polymorphic section *)
val push_section_context : UVars.UContext.t -> safe_transformer0

(** {6 Interactive module functions } *)

val start_module : Id.t -> ModPath.t safe_transformer

val start_modtype : Id.t -> ModPath.t safe_transformer

val add_module_parameter :
  MBId.t -> Entries.module_struct_entry -> Declarations.inline ->
    Mod_declarations.module_type_body safe_transformer

(** returns the number of module (type) parameters following the nested module
    structure. The inner module (type) comes first in the list. *)
val module_num_parameters : safe_environment -> int list

(** returns true if the module is a module type following the nested module
    structure. The inner module (type) comes first in the list. true means
    a module type, false a regular module *)
val module_is_modtype : safe_environment -> bool list

(** Traditional mode: check at end of module that no future was
    created. *)
val allow_delayed_constants : bool ref

(** The optional result type is given without its functorial part *)

val end_module :
  Id.t -> (Entries.module_struct_entry * Declarations.inline) option ->
    (ModPath.t * MBId.t list * Mod_subst.delta_resolver) safe_transformer

val end_modtype : Id.t -> (ModPath.t * MBId.t list) safe_transformer

val add_include :
  Entries.module_struct_entry -> bool -> Declarations.inline ->
   Mod_subst.delta_resolver safe_transformer

val current_modpath : safe_environment -> ModPath.t

val current_dirpath : safe_environment -> DirPath.t

(** {6 Libraries : loading and saving compilation units } *)

type compiled_library

val dirpath_of_library : compiled_library -> DirPath.t
val module_of_library : compiled_library -> Mod_declarations.module_body
val replace_module_of_library : compiled_library -> Mod_declarations.module_body -> compiled_library
val iface_of_library : compiled_library -> iface_table option
val objects_digest_of_library : compiled_library -> Digest.t
val univs_digest_of_library : compiled_library -> Digest.t
(** Digest of this library's OWN [(comp_univs, comp_sorts)] pair
    (binary-equivalence-taiga#841 Review841 G2). *)
val vernac_iface_of_library : compiled_library -> iface_table
(** G1/round-3: KEYED per-declaration vernac-interface digests. *)
(** Used by the checker, which recompiles the VM bytecode of every constant
    instead of trusting the one serialized in the file. *)
val univs_of_library : compiled_library -> Sorts.QContextSet.t * Univ.ContextSet.t
val check_flags_for_library : compiled_library -> safe_transformer0

val start_library : DirPath.t -> ModPath.t safe_transformer

val export :
  output_native_objects:bool -> objects_digest:Digest.t -> vernac_iface:iface_table ->
  safe_environment -> DirPath.t ->
    ModPath.t * compiled_library * Vmlibrary.compiled_library * Nativelib.native_library

val import : compiled_library -> Vmlibrary.on_disk -> vodigest ->
  ModPath.t safe_transformer

(** The ONLY entry point [checker/safe_checking.ml] may call (D2): every
    dependency is checked by whole-library digest equality alone, with
    [dep_ok]'s relaxed branch not merely untaken but absent from this
    function's call graph. *)
val import_strict : compiled_library -> Vmlibrary.on_disk -> vodigest ->
  ModPath.t safe_transformer

(** {6 Safe typing judgments } *)

type judgment = private {
  jdg_env : safe_environment;
  jdg_val : Constr.constr;
  jdg_type : Constr.types;
}

(** The safe typing of a term returns a typing judgment. *)
val typing : safe_environment -> Constr.constr -> judgment

(** {6 Queries } *)

val exists_objlabel : Id.t -> safe_environment -> bool

val delta_of_senv : safe_environment -> Mod_subst.delta_resolver

val constant_of_delta_kn_senv : safe_environment -> KerName.t -> Constant.t
val mind_of_delta_kn_senv : safe_environment -> KerName.t -> MutInd.t

(** {6 Retroknowledge / Native compiler } *)

val register_inline : Constant.t -> safe_transformer0
val register_inductive : inductive -> 'a CPrimitives.prim_ind -> safe_transformer0

val set_oracle : Conv_oracle.oracle -> safe_transformer0
val set_strategy : Conv_oracle.evaluable -> Conv_oracle.level -> safe_transformer0
