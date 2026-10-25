
val activate : unit -> unit
(** Activates the three probes, which the plugin registers when it is loaded:
    the typeclass solver, the coercion hook and the canonical-solution hook. *)

val register_override : unit -> unit
(** Registers all three probes again under their unchanged names, each with
    [~override:true]. *)
