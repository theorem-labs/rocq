(* One object of each of the ten kinds the library label strips locations
   from (CONSTANT, INDUCTIVE, ABBREVIATION, NOTATION, TAC-DEFINITION,
   TAC-REDEFINITION, TacticGrammar and TacticSyntax, AUTOHINT with a Hint
   Extern, TAC2-DEFINITION), a few it reads as they are, and a functor. Each
   variant of misc/library-label.sh changes one thing. *)

Inductive t := C1 | C2.

Definition f (n : nat) := S n.

Lemma l1 : forall n, f n = S n.
Proof. intros n. reflexivity. Qed.

Notation "x +++ y" := (Nat.add x y) (at level 50, left associativity).

Notation h := (f 0).

Ltac my_tac := intros; reflexivity.

Ltac my_tac2 := idtac.

Ltac my_tac2 ::= intros.

Tactic Notation "my_exact" constr(x) := exact x.

#[global] Hint Resolve l1 : core.

#[global] Hint Extern 1 (f _ = _) => my_tac : core.

#[global] Set Asymmetric Patterns.

Module Type S. Parameter u : Type. End S.

Module F (X : S). Definition d := X.u. End F.

Definition g := f.

From Ltac2 Require Import Ltac2.

Ltac2 l2 (n : int) := n.
