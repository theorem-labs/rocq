(* D4 — the bail-out firing where the analysis was RIGHT.

   The prefix is a beta redex whose argument is the inner fixpoint, and the
   body calls it through the redex binder [g].  After the prefix reduction
   the analysed body is [... inner a b k ...] with [a] and [b] the first two
   formal arguments, so the uniform prefix of 2 that the analysis computes is
   correct and the extrusion it licenses is justified.  The rewriting pass,
   which runs on the body as written, meets the redex argument [inner] with
   no arguments at all and bails.  Terminating and computing. *)

Definition outerD4 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat -> nat) p p p).
    fix inner 3.
    refine ((fun (g : nat -> nat -> nat -> nat) => _) inner).
    intros a b m.
    destruct m as [|k].
    + exact (outer p).
    + exact (g a b k).
Defined.

Print Assumptions outerD4.
Example d4_computes : outerD4 5 = 0. Proof. reflexivity. Qed.
