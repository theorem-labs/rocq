(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The result of a model search on a cube. *)
type result =
  | Found of (int * Micromega.z) list  (** a model of the cube *)
  | Missed  (** no model found: the search ran, perhaps cut short by its budget, and found none *)
  | Deferred  (** the search did not start: its first step did not fit the budget *)

(** [find_model ~affordable depth sys] is [Found m], [m] an assignment of the variables of [sys]
    under which every constraint of [sys] holds, evaluated exactly over Z, if a short search finds
    one: one rational LP on [sys] as [lia] develops it, its point and three roundings of it, then a
    depth-first branching on a fractional variable, with at most 16 LPs. Before each step it asks
    [affordable] with the step's predicted processor seconds: before developing [sys], the
    development, first LP and check of its point, predicted from the last search's seconds per unit
    of cube size and the size of [sys] (a power [p ^ n] counting [n] times [p]), and [Deferred] if
    that does not fit; before a later LP, the LP and the check of its point, predicted from this
    search's last LP and check, and [Missed] if that does not fit. By default [affordable] is always
    true. [Missed] otherwise: also when [sys] has an exponent above 2^16 or a size above 2^20, when
    the evaluation would compute a product or power of more than 2^16 bits, and on any exception for
    which [CErrors.noncritical] holds. A cube that has a model has no certificate, so neither [lia]
    nor [nlia] proves it.

    The search changes state that the provers share: it clears the monomial table
    [Polynomial.LinPoly.MonT], sets the depth bound of [Certificate], and draws fresh variables and
    pivots in [Simplex]. Certificates stay the provers' own because each prover entry point resets
    that state before it reads it: [Certificate.lia], [Certificate.nlia],
    [Certificate.linear_prover_with_cert] and [Certificate.nlinear_prover] call
    [develop_constraints] first, and [Simplex.integer_solver] resets its pivot count. *)
val find_model :
     ?affordable:(float -> bool)
  -> int
  -> (Micromega.z Micromega.pExpr * Micromega.op1) list
  -> result

(** [pol_size p]: about the size of the expression that [Micromega.denorm] makes of [p] (its nodes, a
    term [x ^ i] counting [i]), without allocating, capped at 2^20 + 1; a degree of more than 21 binary
    digits or a nesting of coefficients deeper than 4096 gives the cap at once, whatever the size. The
    early-failure check's measure of a clause, to predict a search's first step on it from the
    prover's seconds on a clause of a known size. *)
val pol_size : Micromega.z Micromega.pol -> int
