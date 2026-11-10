(* Two monomorphic blocks whose own universe levels carry different
   constraints: Spec relates u and v, Agent leaves them unrelated. The two
   declarations read the same; what differs is what each file says about the
   levels a merge would equate. *)
Universe u.
Universe v.
Constraint u < v.
#[universes(template=no)]
Inductive b (A : Type@{u}) (B : Type@{v}) := B0 : A -> B -> b A B.

Definition Stmt := forall x : b nat bool, x = x.
