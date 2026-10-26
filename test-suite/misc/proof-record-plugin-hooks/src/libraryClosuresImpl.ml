(* The fenced closure setters that belong to plugins Rocq ships, called ONCE
   each after the plugins' own modules have installed theirs at load: one call
   too many for each, so a stock count set too high shows as a missing detail
   in misc/proof-record-plugin-hooks.sh (Claude review of e16e9d2ae4, findings
   1 to 3). No later proof reaches what they install: theories/Library.v runs
   only [exact I] after the call, and the compiled global replaced is its own
   [probe_target], which nothing runs. *)

open Ltac2_plugin

let print_primitive =
  { Tac2expr.mltac_plugin = "rocq-runtime.plugins.ltac2"; mltac_tactic = "print" }

let set_closures () =
  Ssreflect_plugin.Ssrcommon.set_ssrautoprop_tac (Proofview.tclUNIT ());
  (* A fresh closure: [define_primitive] annotates the closure it is given,
     and an annotated one, such as the current value, cannot be annotated
     again. *)
  Tac2env.define_primitive print_primitive
    (Tac2val.ValCls (Tac2val.abstract 1 (fun _ -> Proofview.tclUNIT (Tac2ffi.of_unit ()))));
  Tac2env.define_ml_object Tac2quote.wit_ident (Tac2env.interp_ml_object Tac2quote.wit_ident);
  let kn = match Tac2env.locate_ltac (Libnames.qualid_of_ident (Names.Id.of_string "probe_target")) with
    | Tac2expr.TacConstant kn -> kn
    | Tac2expr.TacAlias _ -> CErrors.anomaly (Pp.str "probe_target is an alias")
  in
  Tac2env.set_compiled_global kn { Tac2env.source = "proof-record-probe" } (Tac2ffi.of_unit ())
