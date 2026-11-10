Require Spec.
Require Agent.

(* The same merged name in three places a library writes out: a top-level
   definition, a Module, and a Module Type with a functor over it. Before the
   fix only the first was undone on export. *)
Definition top := Agent.Leaf.

Module M.
  Definition inmod := Agent.Leaf.
End M.

Module Type S.
  Parameter p : Agent.tree.
End S.

Module F (X : S).
  Definition infun := X.p.
  Definition alsohere := Agent.Leaf.
End F.
