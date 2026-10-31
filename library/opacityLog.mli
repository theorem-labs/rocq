(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Whether a constant was an axiom or an opaque proof when a command whose
    outcome depends on that distinction ran while a library was compiled (a
    non-opaque [Strategy]/[Transparent] command, an extraction, a
    [Functional Scheme], a plugin's [Global.body_of_constant]), and which
    opaque table a proof body was read from (an extraction,
    [Global.body_of_constant], the keepfacts closure walk) (design D18,
    dispatch://INFRA-361). See [opacityLog.ml] for why. *)

val set_enabled : bool -> unit
(** Log queries ([true]) or ignore every [record] call ([false], the default).
    [Library.set_location_free_label] sets it: the queries are collected only
    under [-location-free-label]. *)

val reset : unit -> unit
(** Forget the queries logged so far. *)

val record : Constant.t -> Declarations.constant_body -> unit
(** [record c cb]: such a command told [c], whose body is [cb], apart as an
    axiom or an opaque proof. Logs [(c, true, None)] when [cb]'s body is an
    opaque proof ([OpaqueDef]), [(c, false, None)] when it is [Undef None],
    and nothing for any other body. Ignored unless logging is enabled. *)

val record_body_read : Constant.t -> Opaqueproof.opaque -> unit
(** [record_body_read c o]: an extraction, a caller of
    [Global.body_of_constant], or the walk that computes the library's
    assumption closures ([KeepFacts]), read the body of [c], the opaque proof
    [o]. Logs [(c, true, Some dp)], [dp] the library whose opaque
    table holds that body ([Opaqueproof.repr o]), also when [dp] is the
    library holding [c]. Ignored unless logging is enabled. *)

val get : unit -> (Constant.t * bool * DirPath.t option) list
(** The queries logged so far, newest first, with repeats. *)
