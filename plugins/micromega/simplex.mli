(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Polynomial

(** Profiling *)

type profile_info =
  { number_of_successes : int
  ; number_of_failures : int
  ; success_pivots : int
  ; failure_pivots : int
  ; average_pivots : int
  ; maximum_pivots : int }

val get_profile_info : unit -> profile_info

(** What the calls of [integer_solver] during a computation added to the profile. *)
type profile_trace

(** [traced f] is [(f (), t)], [t] what the calls of [integer_solver] during [f ()] added to the
    profile. *)
val traced : (unit -> 'a) -> 'a * profile_trace

(** [replay t] adds [t] to the profile again, as the calls that made it did. *)
val replay : profile_trace -> unit

(** Simplex interface *)

val find_point : cstr list -> Vect.t option
val find_unsat_certificate : cstr list -> Vect.t option

val integer_solver :
  WithProof.t list -> ProofFormat.proof option

(** [relaxed_point lp] solves the rational relaxation of [lp] once, up to feasibility, with the
    environment that [integer_solver lp] builds: [Some sol], one of its points, or [None] if it is
    infeasible. *)
val relaxed_point : WithProof.t list -> Vect.t option
