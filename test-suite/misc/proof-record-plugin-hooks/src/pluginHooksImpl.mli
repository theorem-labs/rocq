
val activate : unit -> unit
(** Activates the three probes, which the plugin registers when it is loaded:
    the typeclass solver, the coercion hook and the canonical-solution hook. *)

val set_unifier : unit -> unit
(** Installs a unifier with [Evarconv.set_evar_conv], as unicoq's
    [Set Use Unicoq] does. *)
