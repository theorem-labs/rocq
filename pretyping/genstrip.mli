(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg

(** {5 Location stripping of globalized generic arguments}

    The strippers of {!LocStrip}, at the level of generic arguments: each
    argument type registers the stripper of its globalized value. *)

type 'glb strip_fun = 'glb -> 'glb

val register_strip0 : ('raw, 'glb, 'top) genarg_type -> 'glb strip_fun -> unit
(** Register the stripper of an [ExtraArg]. *)

val strip : ('raw, 'glb, 'top) genarg_type -> 'glb strip_fun
(** The stripper of an argument type. Lists, options and pairs are stripped
    component by component. Applying the stripper of an [ExtraArg] with no
    registered stripper raises [LocStrip.Unknown]. *)

val generic_strip : glob_generic_argument strip_fun
