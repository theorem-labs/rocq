(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** r3-b instrumentation: measurement scaffolding for speed lane R3 design
    b, to remove before release (see convLog.ml). With
    [ROCQCHK_CONV_LOG=<dir>] set, each VM cast appends one line to
    [<dir>/<pid>.tsv], whose last column is the cast's absolute start time,
    and each process appends its timeline events to
    [<dir>/<pid>.events.tsv]; without it, every function here does
    nothing. *)

val enabled : unit -> bool

(** [event name fields] appends one line to this process's events file:
    the absolute wall-clock time, the pid, [name] and [fields]. *)
val event : string -> string list -> unit

(** The ["process-start"] event, with the time this module was
    initialised, which is close to the start of the process. *)
val process_start : unit -> unit

type phase = Codegen | Compile | Load | Vm | Index | Wait

(** Which unit the code generation and the compile of a [phase] belong
    to: the conversion's own unit, or the dependency unit that the
    checker's cache (checker/convCache.ml) publishes. *)
type unit_kind = Conv | Dep

(** [with_constant c f] runs [f], attributing its casts to constant [c]. *)
val with_constant : Names.Constant.t -> (unit -> 'a) -> 'a

(** [start ()] begins a cast, with backend ["vm"]; [finish t0] writes its
    line, with [t0] the value of [start ()]. *)
val start : unit -> float
val finish : float -> unit

val set_backend : string -> unit

(** The .ml file of the unit of the cast, whose size the line gives. *)
val set_unit_file : string -> unit

(** [time phase f] runs [f] and adds its wall time to [phase]. *)
val time : phase -> (unit -> 'a) -> 'a
val time_add : phase -> float -> unit
val with_unit_kind : unit_kind -> (unit -> 'a) -> 'a

(** What the cast took from the cache: its status, the definitions reused,
    the units loaded, the definitions copied into its own unit because
    their claimant had not published them (and their declaration bytes),
    and the bytes of the manifest it published. *)
val set_cache :
  status:string -> reused:int -> units:int -> copied:int -> copied_bytes:int ->
  manifest_bytes:int -> unit
