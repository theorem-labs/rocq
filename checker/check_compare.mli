(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The comparator of
    [rocqchk -compare CONFIG -challenge DIR -compare-out FILE].

    The challenge and the answer carry the same library names. [rocqchk]
    checks the answer with the kernel as it does without the option; this
    module loads the challenge into a second environment without a check,
    compares every challenge declaration with the answer declaration of the
    same canonical kernel name, computes each named theorem's axiom closure
    and writes a JSON verdict.

    The comparison is structural after a one-to-one renaming of universe
    levels: no conversion, no reduction, and no constant is unfolded. *)

type config

val read_config : string -> config
(** The config is one JSON object with the keys [theorems] (each
    [{name, permitted_axioms?}]), [permitted_axioms], [tolerated_flags],
    [rewrite_rules], [prechecked] ([{library, sha256}]) and
    [challenge_files] ([{path, sha256}]). Any other key, a duplicate key, a
    byte after the top-level value, a byte sequence that is not UTF-8 or a
    name that is not a string is an error.
    @raise CErrors.UserError on any of them. *)

val prechecked_libraries : config -> string list
(** The libraries the config declares pre-checked. They load through the
    existing [-admit] path, so the option adds each of them to the admit
    list; the config is the only place that names them. *)

type t

val prepare :
  config -> dir:string -> out:string -> add_challenge_load_path:(unit -> unit) ->
  under_challenge_root:(Names.DirPath.t -> bool) -> t
(** Resolve the challenge files under [dir] and check the sha256 of each.
    [add_challenge_load_path] puts [dir] on the load path in place of the
    answer's directories; it is called once, inside the challenge load.
    [under_challenge_root] says whether a library name lives under one of
    those roots: those are the answer's own libraries, and every other
    library the answer loaded is a shared one, which the challenge loads too.
    @raise CErrors.UserError when a file is missing or its sha256 differs. *)

val run :
  t -> Environ.env ->
  (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) ->
  Safe_typing.safe_environment ->
  answer_deps:(Names.DirPath.t * (Names.DirPath.t * Safe_typing.vodigest) array) list ->
  unit
(** Load the challenge into an environment of its own on top of the given
    empty safe environment, compare, and write the verdict file. The
    environment is the answer's, as [rocqchk] checked it, and the accessor
    reads its opaque proofs.
    @raise CErrors.UserError when a pre-checked library's sha256 differs,
    when the two sides record different dependency digests for a pre-checked
    library, or when the config names a theorem the challenge does not hold.
    A verdict is never an error: the file is written and the run exits 0. *)

val sha256_of_file : string -> string
(** The hex SHA-256 of a file. [rocqchk -sha256 FILE] prints it, which is how
    the test suite checks this implementation against the standard vectors
    and against [sha256sum]. *)

(** {6 The comparison itself}

    Exposed in the shape [kernel/indmerge.ml] will take, so that the two can
    be merged when it lands. *)

type umap
(** A bijection between the challenge's universe levels and the answer's,
    built as the walk goes. A level that would map to two levels, or two
    levels that would map to one, is a failure. *)

type diff = string
(** What differs, and where. *)

val empty_umap : umap

val equal_constr : umap -> Constr.t -> Constr.t -> (umap, diff) result

val eq_mib :
  umap -> Environ.env -> Declarations.mutual_inductive_body ->
  Declarations.mutual_inductive_body -> (umap, diff) result
