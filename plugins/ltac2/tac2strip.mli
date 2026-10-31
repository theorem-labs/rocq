(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2expr

(** Typed location strippers of the Ltac2 values that libraries store, for
    the location-free interface key of a library (see {!LocStrip} and
    [Libobject.interface_key]). Each function returns a copy of its argument
    in which every source location is replaced and nothing else differs.
    They raise [LocStrip.Unknown] on a value they cannot strip by type. *)

val glb_tacexpr : glb_tacexpr -> glb_tacexpr
(** The payload of [GTacExt] goes through the stripper that its ML object
    registered with [Tac2env.define_ml_strip]. *)

val raw_tacexpr : raw_tacexpr -> raw_tacexpr
(** For globalized raw expressions (abbreviations, untyped notations).
    Raises on [CTacExt], which globalization never leaves. *)

val raw_typexpr : raw_typexpr -> raw_typexpr

val raw_patexpr : raw_patexpr -> raw_patexpr

val sexpr : sexpr -> sexpr

val notation_data : Tac2env.notation_data -> Tac2env.notation_data
