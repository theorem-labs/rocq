
val set_closures : unit -> unit
(** Calls once each fenced closure setter that belongs to Ltac2 or ssreflect:
    [Ssrcommon.set_ssrautoprop_tac], [Tac2env.define_primitive] and
    [Tac2env.define_ml_object] on a defined name, and
    [Tac2env.set_compiled_global]. *)
