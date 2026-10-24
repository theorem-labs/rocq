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

val get_ml_filename : unit -> string * string

(** [force_temp_dir ()] makes now the directory where conversions and
    normalisations write their code, which is otherwise made on first
    use. A process forked later writes its code there too, and the
    process that made it removes it at exit: coqchk's [-j] workers end
    with [Unix._exit], which skips the [at_exit] removal. *)
val force_temp_dir : unit -> unit

(** {6 The checker's unit cache} (see checker/convCache.ml) *)

(** The directory where the workers publish their units, made on first use
    inside the process's temp dir (mode 0700) and added to the include
    dirs. The cache makes it in the main process before the first fork,
    and removes it itself, before the temp dir goes. *)
val cache_directory : unit -> string
val cache_directory_made : unit -> string option

(** A fresh file name in [cache_directory ()], with its prefix. *)
val cache_ml_filename : unit -> string * string

(** [load_unit ~prefixes file] loads a unit of the cache: the unit carries
    its own symbols, and nothing is marked linked, so the caller marks
    the definitions it has checked ([Nativecode.link_definitions]).
    [prefixes] are registered as loaded: the unit's, and every part's. *)
val load_unit : prefixes:string list -> string -> unit

(** {6 Compile slots}

    [Some (dir, cap)]: every compile of generated code holds one of [cap]
    slots in [dir] while its compiler runs (see nativelib.ml). A slot's
    owner record is installed whole; a slot is held while its holder or
    the compile it runs is alive, a record that cannot be read counts as
    held, and a record that goes while it is read counts as a release,
    not as a holder to take the next generation above. A compile dies
    with the process that started it. *)
val slots : (string * int) option ref

(** A slot, waiting until one frees and running [poll] between attempts;
    [None] when there are no slots. [release_slot] removes it. Only
    contention is waited for: any other error on the slot files raises
    [Unix.Unix_error], and so does a wait longer than 600 s. *)
val acquire_slot : ?poll:(unit -> unit) -> unit -> string option
val release_slot : string option -> unit

(** The slot files this process holds. *)
val held_slots : string list ref

(** {6 Dependency units compiled as parts} *)

type unit_part = {
  part_prefix : string;
  part_defs : Nativecode.definition list;
}

(** [compile_unit ~ml ~prefix code] compiles a dependency unit, its first
    global the symbols table, whole (as [ml], prefix [prefix]) or, above a
    size threshold, as parts [<base>_p<k>] compiled in parallel. It
    returns the [.cmxs] and the parts, each with the definitions it
    defines. *)
val compile_unit : ml:string -> prefix:string -> Nativecode.global list -> string * unit_part list

(** [compile_part_files ~base files] compiles the parts [(mli, ml)], as
    texts, into [<base>.cmxs]: interfaces, then the parts in parallel
    under slots, then the link. Raises the compiler's failure. *)
val compile_part_files : base:string -> (string * string) array -> string

(** Force the number of parts of every dependency unit ([None]: by size). *)
val set_forced_parts : int option -> unit

(** What a process does before it generates the code of a conversion,
    with the conversion's two terms. The cache reuses here what another
    worker has compiled and publishes what it compiles itself; it does
    nothing by default. *)
val prepare_conversion : (Environ.env -> Constr.t -> Constr.t -> unit) ref

(** [compile file code ~profile] will compile native [code] to [file],
   and return the name of the object file; this name depends on
   whether are in byte mode or not; file is expected to be .ml file *)
val compile : string -> Nativecode.global list -> profile:bool -> string

type native_library = Nativecode.global list * Nativevalues.symbols

(** [compile_library (code, _) file] is similar to [compile file code]
   but will perform some extra tweaks to handle [code] as a Rocq lib. *)
val compile_library : native_library -> string -> unit

(** [execute_library file upds] dynamically loads library [file],
    updates the library locations [upds], and returns the values stored
    in [rt1] and [rt2] *)
val execute_library :
  prefix:string -> string -> Nativevalues.symbols -> Nativecode.code_location_updates ->
  Nativevalues.t option * Nativevalues.t option

(** [enable_library] marks the given library for dynamic loading
    the next time [link_libraries] is called. *)
val enable_library : string -> Names.DirPath.t -> unit

val link_libraries : unit -> unit

(* used for communication with the loaded libraries *)
val get_symbols : unit -> Nativevalues.symbols
val rt1 : Nativevalues.t option ref
val rt2 : Nativevalues.t option ref
