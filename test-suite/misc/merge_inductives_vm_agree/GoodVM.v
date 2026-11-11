Require Spec.
Require Agent.

Definition sz (b : Spec.box) : nat := match b with Spec.mk n => n end.

(* A vm_compute proof over a merged type: both conversions must accept. *)
Definition u : sz (Agent.mk 3) = 3 := ltac:(vm_compute; reflexivity).
