(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type opaques

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val compile_library_bytecode : Environ.env -> Names.DirPath.t -> Names.ModPath.t ->
  'a Mod_declarations.generic_module_body ->
  Vmlibrary.on_disk * 'a Mod_declarations.generic_module_body
(** Reserve a VM slot for every constant of a library that has bytecode,
    discarding whatever code descriptor the [.vo] file claims, and return the
    corresponding code table. The bytecode itself is only compiled, for the whole
    library at once, the first time one of its slots is resolved. *)

val check_module : Environ.env -> opaques -> Retroknowledge.action list -> Names.ModPath.t -> Mod_declarations.module_body -> opaques

exception BadConstant of Names.Constant.t * Pp.t

val constants_of_opaques : Environ.env -> opaques -> Names.Constant.t list
val empty_opaques : opaques
