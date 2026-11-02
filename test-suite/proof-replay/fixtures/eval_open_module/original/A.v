(* Each proof asks Ltac2 about the module it is in, which is open:
   [Module.module_contents], [Module.is_functor] or [Module.is_modtype]. The
   kernel has no entry for an open module, so these answers come from the
   module being built, and the proof's key does not hold them. [same] asks
   for the fields of M, which the edited tree does not change, and must
   replay. The edited tree makes F a plain module and N a plain module, and
   declares one definition before [contents], which asks for the fields of
   the file: [functor], [modtype] and [contents] must each miss on the
   open_module read.

   Nothing in the edited tree after the first Qed is a late command, which
   would keep the proofs before it from replaying: the module type T comes
   before it, and the proofs call the queries through Ltac2 definitions made
   before it too, which the replay's source scan needed until it read
   [Module.module_contents] as one identifier (late_qualified_module_word). *)
From Ltac2 Require Import Ltac2.

Module Type T. End T.

Ltac2 current_fields () := Module.module_contents (Module.current_module ()).
Ltac2 current_is_functor () := Module.is_functor (Module.current_module ()).
Ltac2 current_is_modtype () := Module.is_modtype (Module.current_module ()).

Module M.
Lemma same : True.
Proof. let _ := current_fields () in exact I. Qed.
End M.

Module F (X : T).
Lemma functor : True.
Proof. let _ := current_is_functor () in exact I. Qed.
End F.

Module Type N.
Lemma modtype : True.
Proof. let _ := current_is_modtype () in exact I. Qed.
End N.

Lemma contents : True.
Proof. let _ := current_fields () in exact I. Qed.
