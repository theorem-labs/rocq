Require Spec.
Require Agent.
Require Mid.

(* Compiled WITHOUT the option. The constraint contradicts the equality the
   merge rested on; Mid.vo records that equality, so this must be refused.
   Before it did, Mid.down gave a retraction of Type@{Spec.u} into itself
   and Hurkens' paradox closed False under the global context. *)
Constraint Spec.u < Agent.u.

Definition self : Type@{Spec.u} := Mid.down Type@{Spec.u}.
