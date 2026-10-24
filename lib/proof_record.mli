(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Per-proof records: what each opaque proof of a compiled file read and
    wrote (BET-84, part P2).

    [rocq compile -proof-record] writes one record file beside each [.vo]
    (see {!path_of_vo}). The file is JSON Lines, UTF-8, one JSON object per
    line, each line ending in ["\n"]:

    - line 1 is the {!header} ([{"kind":"header", ...}]);
    - then one {!proof} line per opaque proof, in the order the proofs close
      ([{"kind":"proof", ...}]);
    - the last line is the {!trailer} ([{"kind":"trailer", ...}]).

    The compile writes the file in one piece after the [.vo], so a compile
    that fails or is killed leaves no record. {!parse_string} refuses a file
    without its trailer.

    Every field below is always present, in the order given; a reader must
    refuse a missing or an extra field. Digests are 32 lowercase hex digits
    (MD5, OCaml [Digest]). A field written [d] below is such a digest. *)

val format_version : int
(** The [version] field of the header. A reader refuses any other value. *)

(** {6 Header} *)

type toolchain = {
  binary : string;  (** [d] of the running [rocq] executable. *)
  plugins : (string * string) list;
  (** Each loaded ML plugin, in load order: findlib name, [d] of its file. *)
  load_order : (string * string) list;
  (** Each loaded library, in load order: logical name, [d] of its [.vo]. *)
  warnings : string;  (** The [-w] value of the command line, verbatim. *)
  safe_deps : string list;
  (** The libraries loaded safe ([Require (safe)]), in load order. *)
  stack_limit : string;  (** The soft [RLIMIT_STACK], ["unlimited"] or bytes. *)
}
(** Key item 2 as values. JSON: an object with these fields; a pair is a
    two-element array. *)

type header = {
  version : int;
  library : string;  (** Logical name of the compiled library. *)
  source : string;  (** The [.v] path as given on the command line. *)
  source_digest : string;  (** [d] of the [.v] bytes. *)
  toolchain : toolchain;  (** At the start of the file. *)
  memory_cap : string;
  (** The cgroup [memory.max] of the compile, ["max"] or bytes, or
      ["unknown"]. Recorded, never part of a key. *)
  rlimit_as : string;  (** Soft [RLIMIT_AS], ["unlimited"] or bytes. *)
  rlimit_data : string;  (** Soft [RLIMIT_DATA], ["unlimited"] or bytes. *)
  overcommit_memory : string;  (** [vm.overcommit_memory], or ["unknown"]. *)
  skip_qed_typecheck : bool;  (** Whether [-skip-qed-typecheck] was set. *)
  tables_at_start : bool;
  (** Whether each proof's [start_tables] holds the digest of every hint
      database and typeclass table ([-proof-record-tables]). *)
}

(** {6 Proofs} *)

type toolchain_key = {
  binary : string;  (** As {!toolchain.binary}. *)
  plugins : string;  (** [d] of {!toolchain.plugins}. *)
  load_order : string;  (** [d] of {!toolchain.load_order}. *)
  warnings : string;  (** As {!toolchain.warnings}. *)
  safe_deps : string;  (** [d] of {!toolchain.safe_deps}. *)
  stack_limit : string;  (** As {!toolchain.stack_limit}. *)
}
(** Key item 2, one field per item, so a reader can tell which item
    differs. Taken at the proof's start: a [Require] or [Declare ML Module]
    earlier in the file changes [plugins] and [load_order]. *)

type position = {
  module_path : string;  (** The current module path ([Lib] state). *)
  section_path : string;  (** The current section prefix. *)
}
(** Key item 3. *)

type ineligible = {
  reason : string;
  (** A stable reason name, for example ["command"], ["abstract"],
      ["unhashable"] or ["catchall"]. *)
  detail : string;  (** Free text: the tactic, the handler's file and line. *)
}

type read = {
  row : string;  (** The CHANNELS.md census row, for example ["1"], ["7"], ["N2"]. *)
  channel : string;  (** The lookup kind, for example ["constant"], ["hint_db"]. *)
  key : string;
  (** What was looked up: the kernel name, the hint database name (row 7),
      the typeclass table name (row 8), the option name. *)
  value : string option;
  (** [d] of the value found, or [None] (JSON [null]) when the lookup found
      nothing. *)
}

type writes = {
  universe_levels : string list;  (** Levels the proof created, in order. *)
  counters : (string * int) list;  (** Counter name, total advance. *)
  constraints : string list;  (** New universe constraints, printed. *)
  schemes : string list;  (** Schemes the proof created. *)
  constraint_sources : string list;  (** Constraint-source entries written. *)
  warnings_raised : (string * string) list;  (** Warning name, message. *)
}

type proof = {
  name : string;  (** Key item 1: the full name. *)
  statement : string;  (** Key item 1: [d] of the elaborated statement. *)
  sentences : string;
  (** Key item 1: [d] of the parsed sentences from the statement to the
      closer, locations of this file removed. *)
  closer : string;  (** Key item 1: ["Qed"], ["Save"], ["Defined"], ... *)
  toolchain_key : toolchain_key;  (** Key item 2. *)
  position : position;  (** Key item 3. *)
  ineligible : ineligible list;  (** Empty iff the proof is eligible. *)
  reads : read list;  (** In the order they happened, repeats removed. *)
  start_tables : read list;
  (** With {!header.tables_at_start}: one entry per hint database and
      typeclass table at the proof's start, searched or not. Else empty. *)
  writes : writes;
  kernel_check : bool;
  (** Whether the kernel type-checked the proof at its closer. The kernel
      check records no reads: they are suspended while it runs. *)
  wall_s : float;  (** Wall seconds from the statement to the closer. *)
  cpu_s : float;  (** Process CPU seconds over the same span. *)
}

(** {6 Trailer} *)

type trailer = {
  file_wall_s : float;  (** Wall seconds of the whole compile. *)
  file_cpu_s : float;  (** CPU seconds of the whole compile. *)
  peak_rss_kb : int;  (** Peak resident set, kB ([VmHWM]). *)
  proof_count : int;  (** The number of proof lines. *)
}

type file = { header : header; proofs : proof list; trailer : trailer }

val toolchain_key : toolchain -> toolchain_key

(** {6 Writing} *)

val output_header : Buffer.t -> header -> unit
val output_proof : Buffer.t -> proof -> unit
val output_trailer : Buffer.t -> trailer -> unit
(** Each appends one JSON object and ["\n"]. Floats must be finite. *)

val path_of_vo : string -> string
(** [path_of_vo "dir/Foo.vo"] is ["dir/Foo.proof-record.jsonl"]. *)

(** {6 Reading} *)

exception Parse_error of string

val parse_string : string -> file
(** Reads a whole record file. Raises [Parse_error] on another format
    version, a missing header or trailer, a missing, extra or repeated
    field, a trailer whose [proof_count] differs from the proof lines, or a
    line after the trailer. *)

(** {6 Digests} *)

exception Unhashable of string

val digest_value : ?locs:Loc.source -> 'a -> string
(** [d] of a value's structure. Equal structures give equal digests,
    whatever their sharing. Ints, strings, floats, boxed integers and
    constructors are told apart. Forced lazy values are digested as their
    value. An extension constructor is digested by its name only.

    With [~locs:src], each [Loc.t] whose [fname] equals [src] is digested
    as one fixed value, so two values that differ only in locations of
    [src] have equal digests. [src] must be an [InFile] source.

    Raises [Unhashable] on a closure, an unforced lazy value, an object,
    an abstract block, a cycle, or a value of more than 2{^25} distinct
    blocks. *)
