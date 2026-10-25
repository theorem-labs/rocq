(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
val memory_stat : bool ref
val output_context : bool ref

val start_summary : bool -> unit
val record_constant : Names.Constant.t -> Declarations.constant_body -> unit
val record_inductive :
  indices_matter:bool -> Names.MutInd.t -> Declarations.mutual_inductive_body -> unit
val record_admitted : string -> unit

val stats : Environ.env -> Names.Cset.t Names.Cmap.t -> unit
