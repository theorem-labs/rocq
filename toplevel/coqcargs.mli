(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compilation modes:
  - BuildVo      : process statements and proofs (standard compilation),
                   and also output an empty .vos file and .vok file
  - BuildVos     : process statements, and discard proofs,
                   and load .vos files for required libraries
  - BuildVok     : like BuildVo, but load .vos files for required libraries

  When loading the .vos version of a required library, if the file exists but is
  empty, then we attempt to load the .vo version of that library.
  This trick is useful to avoid the need for the user to compile .vos version
  when an up to date .vo version is already available.
*)
type compilation_mode = BuildVo | BuildVos | BuildVok

type glob_output =
| NoGlob
| GlobFile of string (* Single file for all coqc arguments *)

type t =
  { compilation_mode : compilation_mode

  ; compile_file: (string * bool) option  (* bool is verbosity  *)
  ; compilation_output_name : string option

  ; echo : bool

  ; glob_out    : glob_output option

  ; proof_record : bool
  (** [-proof-record]: write a {!Proof_record} file beside each [.vo]. *)
  ; proof_record_tables : bool
  (** [-proof-record-tables]: record, at each proof's start, a digest of
      every hint database and typeclass table, not only of the ones the
      proof searches. Implies [-proof-record]. *)

  ; proof_replay : Proof_replay.source option
  (** [-proof-replay FILE] or [-proof-replay-dir DIR]: the registration's
      record this compile replays from. *)
  ; proof_replay_ratio : float option
  (** [-proof-replay-ratio R]: the grade-to-registration ratio of per-file
      wall time, at the top of its measured spread. Required with a
      source, refused without one: there is no default charge. *)
  ; proof_replay_budget : float option
  (** [-proof-replay-budget SECONDS]: the per-file wall budget the charged
      clock runs against. Without it, nothing stops the file on time. *)
  ; proof_replay_peak_limit_kb : int option
  (** [-proof-replay-peak-limit-kb KB]: a file whose registered peak
      resident set was above this compiles without replay. *)

  ; output_context : bool
  }

val default : t
val parse : string list -> t
