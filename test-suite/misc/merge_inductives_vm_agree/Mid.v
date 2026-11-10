Require Spec.
Require Agent.

(* Built with the option, so its body may mix the two copies' constructors:
   this is the term the VM and the kernel could disagree about. *)
Definition g (b : Spec.box) : Spec.box :=
  match b with Spec.mk Y => Agent.mk Y end.
