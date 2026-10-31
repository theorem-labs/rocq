(* What the summary may call a functor's axiom, and what it leaves out.
   An axiom is named where it is declared, which for a functor's field is the
   module each application makes: App.in_f. That is the name Print
   Assumptions prints for it too; the functor's own F.in_f appears in
   neither account, which is what a reader that joins the two by name, as the
   BET grader does, needs. Where this summary has only a type to read, it
   cannot tell an assumption from a definition and names nothing, so no shape
   below is named one way here and another way by Print Assumptions. *)

Module Type S. Parameter n : nat. End S.
Module Type T. Parameter tgt : 1 = 2. End T.

Module Arg. Definition n := 0. End Arg.

Module F (X : S).
  Axiom in_f : False.
  Definition use : False := in_f.
End F.

(* The environment holds this application's fields under its own name. *)
Module App := F Arg.
Definition reached : False := App.use.

(* The shapes the walk leaves out, pinned here so a later change to it cannot
   alter them unseen. In each, all the summary has is a type that says
   nothing about what the module expression under it leaves assumed, so it
   reports no axiom of its own and Print Assumptions names one. *)

(* A seal a functor body declares: Print Assumptions names AppG.Inner.in_g
   for a proof that uses AppG.Inner.tgt, and the summary names nothing. The
   helper keeps the opacified-body accounting out of this: it reaches in_g
   through a constant that has a body, which that accounting drops. *)
Module G (X : S).
  Module Inner : T.
    Axiom in_g : False.
    Lemma helper : False. Proof. exact in_g. Qed.
    Lemma tgt : 1 = 2. Proof. destruct helper. Qed.
  End Inner.
End G.
Module AppG := G Arg.

(* An application inside a seal: Print Assumptions names Seal.Inner.in_f and
   the summary names nothing. *)
Module Seal : T.
  Module Inner := F Arg.
  Lemma tgt : 1 = 2. Proof. destruct Inner.use. Qed.
End Seal.

(* An ascription over a module expression: Plain defines what U asks for, so
   U's parameter is no axiom and must not be listed. The helper keeps the
   opacified-body accounting out of this: it reaches A.p through a constant
   that has a body, which that accounting drops. *)
Module Type U. Parameter p : nat. End U.
Module Plain. Definition p := 0. End Plain.
Module Type Q. Parameter q : nat. End Q.
Module Ascribed : Q.
  Module A : U := Plain.
  Definition helper := A.p.
  Definition q := helper.
End Ascribed.

(* A sealed functor, and an application an ascription hides: each is listed
   under its interface's parameter, AppH.tgt and AscApp.tgt, which the
   environment fold prints on its own. Print Assumptions names AppH.in_h and
   AscApp.in_k instead, so a reader that joins by name fails closed on them,
   which is the safe direction. *)
Module H (X : S) : T.
  Axiom in_h : False.
  Lemma tgt : 1 = 2. Proof. destruct in_h. Qed.
End H.
Module AppH := H Arg.

Module K (X : S).
  Axiom in_k : False.
  Lemma tgt : 1 = 2. Proof. destruct in_k. Qed.
End K.
Module AscApp : T := K Arg.

(* A sealed functor applied inside a seal: Print Assumptions names
   SealApp.Inside.in_h, and the summary names nothing. *)
Module SealApp : T.
  Module Inside := H Arg.
  Definition helper : 1 = 2 := Inside.tgt.
  Lemma tgt : 1 = 2. Proof. exact helper. Qed.
End SealApp.
