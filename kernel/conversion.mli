(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ

(***********************************************************************
  s conversion functions *)

type 'a kernel_conversion_function = env -> 'a -> 'a -> (unit, unit) result
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:TransparentState.t -> env ->
  ?evars:CClosure.evar_handler ->
  'a -> 'a -> (unit, unit) result

type conv_pb = CONV | CUMUL

type ('a, 'err) universe_compare = {
  compare_sorts : conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
  compare_cumul_instances : conv_pb -> UVars.variances ->
    UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare

type ('a, 'err) generic_conversion_function = ('a, 'err) universe_state -> constr -> constr -> ('a, 'err option) result

val get_cumulativity_constraints : conv_pb -> UVars.variances ->
  UVars.Instance.t -> UVars.Instance.t -> UVars.unif_constraints

val inductive_cumulativity_arguments : (Declarations.mutual_inductive_body * int) -> int
val constructor_cumulativity_arguments : (Declarations.mutual_inductive_body * int * int) -> int

val sort_cmp_universes : conv_pb -> Sorts.t -> Sorts.t ->
  'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

(* [flex] should be true for constants, false for inductive types and
constructors. *)
val convert_instances : flex:bool -> UVars.Instance.t -> UVars.Instance.t ->
  'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

(** This function never returns an non-empty error. *)
val checked_universes : (UGraph.t, 'err) universe_compare

(** These two functions can only fail with unit *)
val conv : constr extended_conversion_function

val conv_leq : types extended_conversion_function

(** The failure values depend on the universe state functions
    (for better error messages). *)
val generic_conv : conv_pb -> l2r:bool
  -> TransparentState.t -> env -> ?evars:CClosure.evar_handler
  -> ('a, 'err) generic_conversion_function

val default_conv     : conv_pb -> types kernel_conversion_function
val default_conv_leq : types kernel_conversion_function

type graph_inconsistency = Univ of UGraph.univ_inconsistency | Qual of QGraph.elimination_error

(** Diagnostic cross-declaration conversion cache COUNTING, binary-
    equivalence-taiga issue #874 version 3. Never consulted by [ccnv]; pure
    measurement, gated by ROCQ_CONV_XDECL_STATS=1. [set_current_library]
    and [mark_library_done] must be called by the library-checking driver
    (checker/checkLibrary.ml's [check_one_lib]) so the shareability test
    knows which library is presently being checked and which libraries
    already finished loading (checked or admitted) before it. Both are
    no-ops when the stats env var is unset, aside from the ref writes. *)
module XDeclCache : sig
  val set_current_library : Names.DirPath.t -> unit
  val mark_library_done : Names.DirPath.t -> unit
end
