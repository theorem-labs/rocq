(* For statement_report_name_canonical.sh. O is sealed by T, so only its
   implementation holds D, an identity functor applied to zqxaXzqxforged, an
   application of F. The opaque proof of O.n names D.ax by a term whose user
   half is O.D.ax and whose canonical half is O.zqxaXzqxforged.ax: in the
   opaques segment of Canon.vo, that canonical half is the only text that
   holds zqxaXzqxforged. *)
Module Type E. End E.
Module X. End X.
Module Type TA. Parameter ax : nat. End TA.
Module Type T. Parameter n : nat. End T.
Module F (Arg : E). Axiom ax : nat. End F.
Module Id (Arg : TA) := Arg.
Module O : T.
  Module zqxaXzqxforged := F X.
  Module D := Id zqxaXzqxforged.
  Lemma n : nat. Proof. exact D.ax. Qed.
End O.
Definition model : nat := O.n.
