(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Location stripping of globalized reduction expressions}

    Returns a copy in which every source location is replaced by the fixed
    value of {!LocStrip}. The user-reduction payload ([UserRed]) is stripped
    by the given function: its type is abstract here (see [Redexpr]). *)

val glob_red_expr : ('usr -> 'usr) -> 'usr Genredexpr.glob_red_expr -> 'usr Genredexpr.glob_red_expr
