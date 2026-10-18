(* One object under two user names (a module alias, Include, a functor
   application) has one entry per user name in the output, as the walk without
   reuse reports it: the second query of each pair replays the type of an axiom
   that names both. *)

(* Alias, a fixpoint assumed guarded. *)
Module N1.
  Unset Guard Checking.
  Fixpoint f (n : nat) : nat := f n.
  Set Guard Checking.
End N1.
Module M1 := N1.
Axiom b1 : M1.f = N1.f.
Print Assumptions b1.
Print Assumptions b1.

(* Include. *)
Module K2.
  Include N1.
End K2.
Axiom c2 : N1.f = K2.f.
Print Assumptions c2.
Print Assumptions c2.

(* Attribute, both names under one type. *)
Module M3.
  #[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n.
End M3.
Module MA3 := M3.
Axiom X3 : (fun _ _ : nat => nat) (M3.f 0) (MA3.f 0).
Definition d3 : nat := X3.
Print Assumptions X3.
Print Assumptions d3.

(* The two names in two axioms reached by one replay. *)
Module M4. Definition c : nat := 0. End M4.
Module MA4 := M4.
Axiom X4a : (fun _ : nat => nat) M4.c.
Axiom X4b : (fun _ : nat => nat) MA4.c.
Definition d4 : nat := X4a + X4b.
Print All Dependencies d4.
Print All Dependencies d4.

(* An inductive assumed positive. *)
Module V5.
  #[bypass_check(positivity)] Inductive I : Type := C : (I -> nat) -> I.
End V5.
Module X5. Include V5. End X5.
Axiom b5 : V5.I -> X5.I -> nat.
Print Assumptions b5.
Print Assumptions b5.

(* A functor application. *)
Module Type T. Parameter c : nat. End T.
Module F (A : T) <: T. Definition c := A.c. End F.
Module P6 : T. Definition c := 0. End P6.
Module Q6 := F P6.
Axiom X6 : (fun _ _ : nat => nat) P6.c Q6.c.
Definition d6 : nat := X6.
Print All Dependencies d6.
Print All Dependencies d6.
