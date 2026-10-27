(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* The raw-prefix rule reduces the head of a fixpoint body to find its
   abstractions, as [whd_all] does: here 2^16 steps of delta and beta, since
   [i16] unfolds to 2^16 applications of the identity [i0]. Stock 9.2.0 makes
   the same steps in about 0.1 s. A walk that kept its bound values in a list
   and re-examined the whole term at each step took quadratic time in the
   number of steps (103 s at n = 16); each step now costs a constant or
   logarithmic amount. *)
(* Expected time < 2.00s *)

Definition i0 (g : nat -> nat) : nat -> nat := g.
Definition i1 (g : nat -> nat) : nat -> nat := i0 (i0 g).
Definition i2 (g : nat -> nat) : nat -> nat := i1 (i1 g).
Definition i3 (g : nat -> nat) : nat -> nat := i2 (i2 g).
Definition i4 (g : nat -> nat) : nat -> nat := i3 (i3 g).
Definition i5 (g : nat -> nat) : nat -> nat := i4 (i4 g).
Definition i6 (g : nat -> nat) : nat -> nat := i5 (i5 g).
Definition i7 (g : nat -> nat) : nat -> nat := i6 (i6 g).
Definition i8 (g : nat -> nat) : nat -> nat := i7 (i7 g).
Definition i9 (g : nat -> nat) : nat -> nat := i8 (i8 g).
Definition i10 (g : nat -> nat) : nat -> nat := i9 (i9 g).
Definition i11 (g : nat -> nat) : nat -> nat := i10 (i10 g).
Definition i12 (g : nat -> nat) : nat -> nat := i11 (i11 g).
Definition i13 (g : nat -> nat) : nat -> nat := i12 (i12 g).
Definition i14 (g : nat -> nat) : nat -> nat := i13 (i13 g).
Definition i15 (g : nat -> nat) : nat -> nat := i14 (i14 g).
Definition i16 (g : nat -> nat) : nat -> nat := i15 (i15 g).
Definition top : nat -> nat.
Proof.
  fix f 1.
  refine (i16 (fun n : nat => match n with O => O | S p => f p end)).
Time Defined.
