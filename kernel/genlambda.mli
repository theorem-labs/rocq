(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Intermediate language used by both the VM and native. *)

open Names
open Constr

type reloc_table = (int * int) array

type case_annot = case_info * reloc_table * Declarations.recursivity_kind

type 'v lambda

type 'v node =
| Lrel          of Name.t * int
| Lvar          of Id.t
| Levar         of Evar.t * 'v lambda array (* arguments *)
| Lprod         of 'v lambda * 'v lambda
| Llam          of Name.t binder_annot array * 'v lambda
| Llet          of Name.t binder_annot * 'v lambda * 'v lambda
| Lapp          of 'v lambda * 'v lambda array
| Lconst        of pconstant
| Lproj         of Projection.Repr.t * 'v lambda
| Lprim         of pconstant * CPrimitives.t * 'v lambda array
| Lcase         of case_annot * 'v lambda * 'v lambda * 'v lam_branches
  (* annotations, term being matched, accu, branches *)
| Lfix          of (int array * inductive array * int) * 'v fix_decl
| Lcofix        of int * 'v fix_decl
| Lint          of int
| Lparray       of 'v lambda array * 'v lambda
| Lmakeblock    of inductive * int * 'v lambda array
  (* inductive name, constructor tag, arguments *)
| Luint         of Uint63.t
| Lfloat        of Float64.t
| Lstring       of Pstring.t
| Lval          of 'v
| Lsort         of Sorts.t
| Lind          of pinductive

and 'v lam_branches =
  { constant_branches : 'v lambda array;
    nonconstant_branches : (Name.t binder_annot array * 'v lambda) array }

and 'v fix_decl = Name.t binder_annot array * 'v lambda array * 'v lambda array

type evars =
  { evars_val : CClosure.evar_handler }

val empty_evars : Environ.env -> evars

(** {5 Manipulation functions} *)

val node : 'v lambda -> 'v node
val mkLapp : 'v lambda -> 'v lambda array -> 'v lambda
val mkLlam : Name.t binder_annot array -> 'v lambda -> 'v lambda
val unsafe_mkPArray : 'v lambda array -> 'v lambda -> 'v lambda
val unsafe_mkPArray_val : 'v -> 'v lambda -> 'v lambda
val decompose_Llam : 'v lambda -> Name.t binder_annot array * 'v lambda
val decompose_Llam_Llet : 'v lambda -> (Name.t binder_annot * 'v lambda option) array * 'v lambda

val free_rels : 'v lambda -> Int.Set.t

(* {5 Simplification} *)

val optimize : 'v lambda -> 'v lambda

(** {5 Translation functions} *)

val get_alias : Environ.env -> evars -> Constant.t -> Constant.t * bool array

module type S =
sig
  type value
  val as_value : int -> value lambda array -> value option
  val check_inductive : inductive -> Declarations.mutual_inductive_body -> unit
end

(** [inlinable_body ~limit body] says whether an application of a constant with this body may be
    compiled as the body applied to the arguments instead of a call: the body must be a function
    ([Lambda]) of at most [limit] nodes, and hold no [Fix] or [CoFix], because expanding a loop
    would copy it rather than remove a call. Expanding such a body is the delta and beta step the
    compiler already takes for a constant declared with inline code, so the compiled code computes
    the same value. *)
val inlinable_body : limit:int -> Constr.t -> bool

module Make (Val : S) :
sig
  (** [lambda_of_constr ~inline_limit env sigma c]: with [inline_limit > 0] an application of a
      constant whose body passes [inlinable_body ~limit:inline_limit] is expanded, up to a budget on
      the nodes expanded in one call. Code compiled into a library file is compiled with
      [inline_limit = 0], so a library's bytes do not depend on this. *)
  val lambda_of_constr : inline_limit:int -> Environ.env -> evars -> Constr.constr -> Val.value lambda
end

(** {5 Printing} *)

val pp_lam : 'v lambda -> Pp.t
