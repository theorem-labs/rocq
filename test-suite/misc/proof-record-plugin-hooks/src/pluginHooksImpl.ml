(* Three probes that decline: a typeclass solver whose condition is always
   false, a coercion hook that always returns None, and a canonical-solution
   hook that always returns None. No behaviour changes through them. A real
   plugin's closure can read state that neither its name nor the plugin's
   files fix (rocq-elpi runs elpi programs that commands change), so a proof
   that asks an active one must store no term:
   - census row 8, channel [typeclass_solver] ([Class_tactics.find_solver]);
   - census row 14, channel [coercion_hooks] ([Coercion.apply_hooks]);
   - census row 14, channel [canonical_hooks] ([Evarconv.apply_hooks]). *)

(* One name per registry, so that a detail that named another registry's
   list would be seen. *)
let solver_name = "proof-record-probe-solver"
let coercion_name = "proof-record-probe-coercion"
let canonical_name = "proof-record-probe-canonical"

let solver : Class_tactics.solver =
  { Class_tactics.solver = (fun ?db:_ _ _ ~depth:_ ~unique:_ ~best_effort:_ ~goals:_ -> assert false) }

let condition : Class_tactics.condition = fun _ _ _ -> false

let coercion_hook : Coercion.hook =
  fun _env _sigma ~flags:_ _body ~inferred:_ ~expected:_ -> None

let canonical_hook : Evarconv.hook =
  fun _env _sigma _proj _pat -> None

(* Registered once each, when the plugin is loaded, and not active. *)
let () = Class_tactics.register_solver ~name:solver_name (solver, condition)
let () = Coercion.register_hook ~name:coercion_name coercion_hook
let () = Evarconv.register_hook ~name:canonical_name canonical_hook

let activate () =
  Class_tactics.activate_solver ~name:solver_name;
  Coercion.activate_hook ~name:coercion_name;
  Evarconv.activate_hook ~name:canonical_name
