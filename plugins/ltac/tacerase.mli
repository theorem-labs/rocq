(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** BET-84: the same tactic with every source location set to [None].

    A location only places an error message: two tactics that differ only
    in their locations run the same way and build the same terms. The proof
    replay digests a tactic definition through this view, so moving a
    definition to another line does not change it.

    The erasers are written by structure over the types and keep every
    other field. A generic argument is erased by the eraser registered for
    its type ({!register_erase0}); a type with none is kept as it is, with
    its locations, and so are a raw generic argument inside a [constr_expr]
    and a user reduction ([Redexpr.user_red_expr]), whose types are open.
    Keeping a location never makes two different values equal. *)

open Genarg

val register_erase0 : ('raw, 'glb, 'top) genarg_type -> ('glb -> 'glb) -> unit
(** Register the eraser of the globalized values of a generic argument
    type. Must be an [ExtraArg]. *)

val erase_genarg : glob_generic_argument -> glob_generic_argument

val erase_glob_constr : Glob_term.glob_constr -> Glob_term.glob_constr

val erase_constr_expr : Constrexpr.constr_expr -> Constrexpr.constr_expr

val erase_tactic : Tacexpr.glob_tactic_expr -> Tacexpr.glob_tactic_expr
