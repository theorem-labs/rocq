(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The late-command scan of proof replay (BET-84, part P3): which commands
    of a source text, after its first [Qed] or [Save], can rebind a Rocqlib
    name, load code or change the working directory. A proof that opens
    before the last such command runs its tactics ({!Proof_replay}). The
    scan reads the text only; it decides nothing about a proof. *)

val scan_late_rebind : string -> (string * int) option
(** The first command in this source text, after its first [Qed] or [Save],
    that can rebind a Rocqlib name, load code or change the working
    directory — [Register], [Require], [Load], [Cd], [Declare], [Import],
    [Export], [Include], [Module], or an [End] that closes a module or a
    section inside which one of those appeared — with its line; [None] if
    there is none. Comments and strings are
    skipped; a number is read as Rocq's lexer reads it, and a late word also
    counts at the end of a longer identifier. A component of a qualified
    identifier ([Module.module_contents], [M.Register]) is one identifier
    token to the lexer and is not a late word. A sentence ends at ["."] or
    ["..."] followed by a blank, not at [".."]. *)

val scan_late_events : ?imports_late:bool -> string -> (string * int) option * int option
(** {!scan_late_rebind}, and the byte offset of the LAST such command's
    word. With [~imports_late:false], [Import] and [Export] are not late. A
    plain module ([Module M.], [Module Import M.]) is not late by itself,
    and its [End] only when a late word appeared inside it. *)

type require_text = { rq_from : string option; rq_names : string list }
(** A [Require] the source text spells out in full: its [From] prefix and
    its library names, as written. *)

type late_command = { lc_offset : int; lc_require : require_text option }
(** A late command: its word's byte offset, and for a [Require] the text
    spells out in full, that [Require]. *)

val scan_late_commands : ?imports_late:bool -> string -> (string * int) option * late_command list
(** {!scan_late_rebind}, and every late command, last first. A [Require]
    carries its names when it is its sentence's command word, or follows
    the sentence's [From q], and its sentence is [From q]? [Require]
    [(safe)]? ([Import] or [Export], with import categories)? then names
    of plain ASCII identifiers, each with an import filter or not. *)

type late_bound = { lb_last : int option; lb_requires : (int * require_text) list }
(** What a proof has to open after to replay: the offset of the last late
    command that is late whatever is loaded, and the [Require]s after it
    that the text spells out in full, last first, with their offsets. Each
    of those is late only while a library it names is not loaded. *)

val no_late : late_bound
(** No late command. *)

type late_events = {
  first : string * int;  (** the first late command, and its line *)
  late : late_bound;  (** [Import] and [Export] counted *)
  late_no_imports : late_bound;  (** [Import] and [Export] not counted *)
}

val late_events : string -> late_events option
(** The late commands of a source text; [None] when it has none. *)
