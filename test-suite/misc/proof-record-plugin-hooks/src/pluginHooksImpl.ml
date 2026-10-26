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

(* Every process-wide closure setter the recorder fences, called ONCE, as a
   plugin would after Rocq's own modules have installed theirs: one call too
   many for each, so a stock count set too high is seen as a missing detail.
   The closures are inert for the one proof that follows in Probe.v, [exact I]
   against [True]: the unifier accepts every problem, the others are never
   reached, and the kernel checks the term at Qed. *)
let probe_tactic = { Ltac_plugin.Tacexpr.mltac_plugin = "coq-test-suite.plugin_hooks";
                     mltac_tactic = "probe" }

let set_closures () =
  Evarconv.set_evar_conv (fun _flags _env sigma _pb _t1 _t2 -> Evarsolve.Success sigma);
  Evarconv.set_solve_evars (fun _env sigma c -> (sigma, c));
  Typeclasses.set_solve_all_instances (fun _env sigma _filter _unique _fail -> sigma);
  (Typeclasses.set_solve_one_instance[@warning "-3"]) (fun _env _sigma _t -> raise Not_found);
  Namegen.set_reserved_typed_name (fun _env _sigma _t -> Names.Anonymous);
  CClosure.set_conv (fun _ _ _ _ -> false);
  Coercionops.install_path_comparator (fun _ _ _ _ _ -> false);
  Tactics.declare_intro_decomp_eq (fun _ _ _ -> Proofview.tclUNIT ());
  Equality.set_eq_dec_scheme_kind Auto_ind_decl.eq_dec_scheme_kind;
  Ind_tables.set_declare_definition_scheme (fun ~univs:_ ~role:_ ~name:_ ~effs:_ _ ->
      CErrors.anomaly (Pp.str "probe"));
  Ind_tables.set_register_definition_scheme (fun ~internal:_ ~name:_ ~const:_ ~univs:_ ?loc:_ () -> ());
  (* The first registration is a new name; only the overwrite replaces one. *)
  Ltac_plugin.Tacenv.register_ml_tactic probe_tactic [| fun _ _ -> Proofview.tclUNIT () |];
  Ltac_plugin.Tacenv.register_ml_tactic ~overwrite:true probe_tactic [| fun _ _ -> Proofview.tclUNIT () |]

let activate () =
  Class_tactics.activate_solver ~name:solver_name;
  Coercion.activate_hook ~name:coercion_name;
  Evarconv.activate_hook ~name:canonical_name
