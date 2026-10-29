
val activate : unit -> unit
(** Activates the three probes, which the plugin registers when it is loaded:
    the typeclass solver, the coercion hook and the canonical-solution hook. *)

val set_closures : unit -> unit
(** Calls each process-wide closure setter that the recorder fences once, as a
    plugin would (unicoq's [Set Use Unicoq] calls [Evarconv.set_evar_conv]). *)
