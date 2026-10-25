(* Two functors take a parameter of the same name, and an unrelated real module
   X holds an unsafe fixpoint of the same short name. Every flagged field is
   listed once under a name that identifies it: the parameters' own fields
   under the kernel's name for each parameter, <file#A#n>.loop, which cannot be
   mistaken for a constant of the library. *)
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
