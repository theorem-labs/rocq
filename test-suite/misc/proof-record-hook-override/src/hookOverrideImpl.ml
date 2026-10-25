(* A typeclass solver that never runs. Its condition is always false, so
   [Class_tactics.find_solver] always falls through to the built-in solver and
   no behaviour changes. Only its registrations can be seen, through the
   (name, generation) pairs that [rocq compile -proof-record] records for the
   active solvers (census row 8, channel [typeclass_solver], key [active]). *)

let name = "proof-record-probe"

let solver : Class_tactics.solver =
  { Class_tactics.solver = (fun ?db:_ _ _ ~depth:_ ~unique:_ ~best_effort:_ ~goals:_ -> assert false) }

let condition : Class_tactics.condition = fun _ _ _ -> false

(* The ordinary registration: once, when the plugin is loaded. *)
let () = Class_tactics.register_solver ~name (solver, condition)

let activate () = Class_tactics.activate_solver ~name

let register_override () = Class_tactics.register_solver ~name ~override:true (solver, condition)
