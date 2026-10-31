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
    dispatch://INFRA-361), from every process that compiles it: the
    compiling one, its [par:] and [-async-proofs] workers, and the children
    a plugin forks. See [opacityLog.ml] for why and how. *)

type query = {
  constant : string;  (** the constant's user name *)
  library : string option;  (** the [MPfile] root of its user name; [None] for a functor parameter's *)
  opaque : bool;  (** [true] for an opaque proof or a body read *)
  table : string option;  (** for a body read, the library whose opaque table holds the body *)
}

val env_var : string
(** ["ROCQ_OPACITYLOG_FILE"]: the path of the log file, exported by the
    compiling process for its workers and children. *)

val set_enabled : bool -> unit
(** [set_enabled true]: collect the queries of this compilation.
    [Library.set_location_free_label] calls it, before any tactic runs: the
    queries are collected only under [-location-free-label]. This process
    then creates its own log and exports its path in {!env_var}, overwriting
    any inherited value (it never writes into a log it did not create); if
    the log cannot be made, {!get} answers [None]. Worker processes are not
    given the flag, so they never call this and use the inherited log. *)

val reset : unit -> unit
(** Forget the queries logged so far, and empty the log file if this
    process created it. *)

val record : Constant.t -> Declarations.constant_body -> unit
(** [record c cb]: such a command told [c], whose body is [cb], apart as an
    axiom or an opaque proof. Logs [c] with [opaque = true] when [cb]'s body
    is an opaque proof ([OpaqueDef]), [opaque = false] when it is
    [Undef None], and nothing for any other body. It is kept in memory when
    this process collects queries, and appended to the log file when the
    environment names one. A process other than the log's owner that cannot
    open that log or write the record raises an error, before the caller
    uses the answer it records. *)

val record_body_read : Constant.t -> Opaqueproof.opaque -> unit
(** [record_body_read c o]: an extraction, a caller of
    [Global.body_of_constant], or the walk that computes the library's
    assumption closures ([KeepFacts]), read the body of [c], the opaque proof
    [o]. Logs [c] with [opaque = true] and [table] the library whose opaque
    table holds that body ([Opaqueproof.repr o]), also when it is the library
    holding [c]. Kept and appended as {!record} does. *)

val get : unit -> query list option
(** The queries logged so far, with repeats: those the log file holds (every
    process's) and those of this process. [None] when the log could not be
    created, opened, written or read back, holds a line that is not a record,
    or does not end with a newline (a torn last line): the caller then stores
    no opacity queries at all, never an empty list. *)
