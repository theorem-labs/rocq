(* [model] is a top-level Qed, so the
   environment holds it with its opaque body and the -j read-ahead computes its node.
   Its proof names Dzqxu.ax, whose user half is BadNames.Fwd.Dzqxu.ax and whose canonical half
   is BadNames.Fwd.zqxaXzqxforged.ax. In the opaques segment of Fwd.vo only, Dzqxu becomes
   Dzqxv (an object nothing declares, so the report prints "?" and the term's canonical
   half), and then aXzqxforged becomes a, a line break, zqxforged (the canonical half
   is no longer a name, so the report must stop). *)
Module Type E. End E.
Module X. End X.
Module Type TA. Parameter ax : nat. End TA.
Module F (Arg : E). Axiom ax : nat. End F.
Module Id (Arg : TA) := Arg.
Module zqxaXzqxforged := F X.
Module Dzqxu := Id zqxaXzqxforged.
Lemma model : nat. Proof. exact Dzqxu.ax. Qed.
