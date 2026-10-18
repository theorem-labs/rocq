(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

(* Directory where compiled files are stored *)
val output_dir : CUnix.physical_path ref
val include_dirs : CUnix.physical_path list ref

(** Default value for include dirs in non -boot mode (just the kernel). *)
val default_include_dirs : Boot.Env.t -> CUnix.physical_path list

val get_load_paths : (unit -> string list) ref

val load_obj : (string -> unit) ref

(** [link_dependencies env sigma ts] compiles, loads and links the native code
    of every constant and inductive that the terms [ts] reach and that is not
    linked yet. The code is cut into units of bounded size (see
    [ROCQCHK_NATIVE_UNIT_MIN]/[ROCQCHK_NATIVE_UNIT_MAX], in bytes of generated
    source), generated and compiled in dependency order, each unit once per
    cache ({!Nativecache}). A unit that cannot be compiled or loaded is an
    error that names it; there is no fallback. *)
val link_dependencies : Environ.env -> Genlambda.evars -> Constr.constr list -> unit

(** [run_cast ~profile code symbols] compiles (through the cache) and runs the
    unit holding a conversion's own [code]; all its dependencies must be linked
    ({!link_dependencies}). Returns the values stored in [rt1] and [rt2]. *)
val run_cast :
  profile:bool -> Nativecode.global list -> Nativevalues.symbols ->
  Nativevalues.t option * Nativevalues.t option

(** Fixes the cache root and epoch; needed before any [-j] worker forks so
    that every worker shares one cache. Called by {!link_dependencies} too. *)
val init_cache : unit -> unit

type native_library = Nativecode.global list * Nativevalues.symbols

(** [compile_library (code, _) file] is similar to [compile file code]
   but will perform some extra tweaks to handle [code] as a Rocq lib. *)
val compile_library : native_library -> string -> unit

(** [enable_library] marks the given library for dynamic loading
    the next time [link_libraries] is called. *)
val enable_library : string -> Names.DirPath.t -> unit

val link_libraries : unit -> unit

(* used for communication with the loaded libraries *)
val get_symbols : unit -> Nativevalues.symbols
val rt1 : Nativevalues.t option ref
val rt2 : Nativevalues.t option ref
