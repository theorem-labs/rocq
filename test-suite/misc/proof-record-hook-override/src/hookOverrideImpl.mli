
val activate : unit -> unit
(** Activates the probe solver, which the plugin registers when it is loaded. *)

val register_override : unit -> unit
(** Registers the probe solver again under the same name, with [~override:true]. *)
