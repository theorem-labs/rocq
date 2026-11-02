(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The record that proof replay reads (BET-84, part P3): where it is,
    whether it is bound to this compile, and its proofs by name. The
    decision on each proof is {!Proof_replay}'s.

    {b The record is a trusted input, at the same tier as the binary.} Its
    stored terms are read back with [Marshal.from_string], which is not
    memory-safe on chosen bytes, and a stored term's declared type comes
    from it, so the record's parser is NOT a security boundary. A record is
    used only when it is bound to this compile: its bytes hash (SHA-256) to
    the [digest] when one is given (the grading engine passes the digest
    from the registration's root-owned manifest), the compiling user cannot
    write it and nobody but its owner can, and its header names this
    library. With a [Record_dir] and no [digest], the digest comes from the
    [<record>.sha256] file beside the record, and the same write rule holds
    for that file, for [DIR] and for each directory between [DIR] and the
    record; none of those below [DIR], the record and its digest file
    included, can be a symbolic link. *)

type source =
  | Record_file of string  (** one record file, for this compile only *)
  | Record_dir of string
      (** a directory of records: the file's record is the first that
          exists of [DIR/<dotted logical name>.proof-record.jsonl],
          [DIR/<the same with dots turned into slashes>.proof-record.jsonl]
          and [DIR/<V>.proof-record.jsonl], where V is the path of the
          object this compile writes, without its extension, when that path
          is relative and has no parent-directory part. *)

val configure : source:source -> peak_limit_kb:int option -> digest:string option -> unit
(** The command line's record options: where the record is, the peak
    memory above which a record is refused, and the record's SHA-256. *)

val configured : unit -> bool

val set_vo_path : string -> unit
(** The [.vo] this compile writes: with [-proof-replay-dir], one of the
    places the record is looked for. Call it before {!load}. *)

val read_file : string -> string
(** The bytes of a file, as the record is read. Raises [Sys_error] or
    [End_of_file]. *)

type loaded = {
  index : (string, Proof_record.proof) Hashtbl.t;  (** the record's proofs, by name *)
  registered_object : string * string option;
      (** the registration's [.vo], beside the record under the same name,
          and the SHA-256 of its opaque proofs that the record's trailer
          holds ({!Proof_record.trailer.vo_opaques}) *)
}

val load :
  library:string -> toolchain:(unit -> Proof_record.toolchain) -> (loaded, string) result option
(** [None] when no source is configured. Else the record for this library,
    or the reason the whole file runs without replay: ["no_record"] (no
    record for this library in the directory), ["bad_record"] (a record
    that cannot be read or does not parse), ["digest"], ["writable"],
    ["library"], ["format"] (the binding above), ["toolchain"] (the header
    names another binary, plugin set, load order, safe-dependency set or
    stack limit than [toolchain], or this compile could not read the
    digest of its binary or of a plugin's files:
    {!Proof_record.unknown_digest}), ["memory"] (the recorded peak is above
    the limit), ["rlimit"] or ["overcommit"]. [toolchain] is called only
    for a record that is bound to this compile. *)
