Module Type SIG.
  Inductive w : Set :=
      A : w.
  Parameter f : w -> w.
End SIG.

Module M : SIG.
  Inductive w : Set :=
      A : w.
  Definition f x := match x with
                    | A => A
                    end.
End M.

Module N := M.

Check (N.f M.A).

(* Check use of equivalence on inductive types (bug #1242) *)

  Module Type ASIG.
  Inductive t : Set := a | b : t.
  Definition f := fun x => match x with a => true | b => false end.
  End ASIG.

  Module Type BSIG.
  Declare Module A : ASIG.
  Definition f := fun x => match x with A.a => true | A.b => false end.
  End BSIG.

  Module C (A : ASIG) (B : BSIG with Module A:=A).

  (* Check equivalence is considered in "case_info" *)
  Lemma test : forall x, A.f x = B.f x.
  intro x. unfold B.f, A.f.
  destruct x; reflexivity.
  Qed.

  (* Check equivalence is considered in pattern-matching *)
  Definition f (x : A.t) := match x with B.A.a => true | B.A.b => false end.

  End C.

(* Check subtyping of the context of parameters of the inductive types *)
(* The parameters are checked declaration by declaration, so a let-in *)
(* must face a let-in of a convertible type and body, and an assumption *)
(* an assumption; the inductive arities and constructor types are *)
(* checked the same way (rocq-prover/rocq#22387) *)

Module Type S. Inductive I (x:=0) (y:nat): Set := c: x=y -> I y. End S.
Module P.  Inductive I (y':nat) (z:=y'): Set := c : 0=y' -> I y'. End P.
Fail Module PP : S := P.
