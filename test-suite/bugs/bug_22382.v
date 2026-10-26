(* Source-only counterexample to nested-fixpoint uniformity analysis. *)
Definition relay (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (carry : nat := seed) (p m : nat) {struct m} : Type :=
    match m with
    | O => outer p -> False
    | S rest => inner carry rest
    end.

Fail
Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay russell n smaller smaller
  end.

(*
Definition diagonal (x : russell 2) : False := x x.
Definition contradiction : False := diagonal diagonal.

Print Assumptions contradiction.
*)

(* Upstream writes the second half with the [#[refine]] attribute on
   [Fixpoint], which Rocq 9.0.1 does not parse ("This command does not support
   this attribute: refine"). The tactic script below builds the same term. *)
Definition error : nat -> nat.
Proof.
  fix error 1.
  intro n.
  destruct n as [|n'].
  - exact 0.
  - refine ((_ : nat -> nat -> nat) n' 1).
    fix rec 2.
    exact ((fun (p : nat) (q r : nat) => match r with 0 => 1 + error q | S r' => rec p r' end) 1).
    Fail Guarded.
Abort.
