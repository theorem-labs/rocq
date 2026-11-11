Require Spec.
Require Mid.

(* Proved by the VM's conversion, not the kernel's. *)
Definition t : Mid.g (Spec.mk 0) = Spec.mk 0 :=
  ltac:(vm_cast_no_check (@eq_refl _ (Spec.mk 0))).
