(* Two functors take a parameter of the same name, and an unrelated real module
   X holds an unsafe fixpoint of the same short name. Each listed name must be
   the name of a real constant: the parameter's own field belongs to no library,
   so it is the applications that are listed. *)
Module Type BT.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
End BT.
Module X : BT.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
End X.
Module F (A : BT) : BT.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
End F.
Module G (A : BT) : BT.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
End G.
Module FX := F X.
Module GX := G X.
