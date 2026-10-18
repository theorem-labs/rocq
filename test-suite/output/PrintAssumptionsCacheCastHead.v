(* Two types that differ only in a cast at the head of an application, which
   the walk reads (it visits the type of the cast) and a comparison that
   flattens applications and looks through casts does not. The second query of
   each pair replays one type after the other, and must print the references
   that only the cast's type contains, in either order. *)

Axiom ax0 : nat.
Definition X : Set := (fun _ : nat => nat) ax0.
Definition add (a b : nat) : nat := b.

(* The cast first, then the plain type. *)
Axiom zz : (fun _ : nat => nat) (add 0 0).
Axiom aa : (fun _ : nat => nat) ((add 0 <: X -> nat) 0).
Definition r1 : nat := (fun _ _ : nat => 0) aa zz.
Print Assumptions r1.
Print Assumptions r1.

(* The plain type first, then the cast. *)
Axiom ax1 : nat.
Definition X1 : Set := (fun _ : nat => nat) ax1.
Axiom yy : (fun _ : nat => nat) ((add 0 <: X1 -> nat) 0).
Axiom ww : (fun _ : nat => nat) (add 0 0).
Definition r2 : nat := (fun _ _ : nat => 0) ww yy.
Print Assumptions r2.
Print Assumptions r2.

(* Print All Dependencies, a cast whose type is a Prop-valued function. *)
Definition Y := nat.
Definition f (n : nat) : Y -> nat := fun _ => n.
Definition g (p : f 0 0 = 0) : True := I.
Axiom A0 : Prop.
Axiom A1 : Prop.
Axiom b0 : (f 0 <: (((fun _ : Prop => Y) A0) -> nat)) 0 = 0.
Axiom b1 : (f 0 <: (((fun _ : Prop => Y) A1) -> nat)) 0 = 0.
Definition R : True := let _ := g b0 in let _ := g b1 in I.
Print Assumptions R.
Print Assumptions R.
Print All Dependencies R.
Print All Dependencies R.

(* The cast kinds: a cast with [<:] (VM) and one with [:] (default), whose kinds
   the key does not tell apart, since the walk does not read them. *)
Axiom ax2 : nat.
Definition X2 : Set := (fun _ : nat => nat) ax2.
Axiom v1 : (fun _ : nat => nat) ((add 0 <: X2 -> nat) 0).
Axiom v2 : (fun _ : nat => nat) ((add 0 : X2 -> nat) 0).
Axiom v3 : (fun _ : nat => nat) (add 0 0).
Definition r3 : nat := (fun _ _ _ : nat => 0) v3 v2 v1.
Print Assumptions r3.
Print Assumptions r3.
