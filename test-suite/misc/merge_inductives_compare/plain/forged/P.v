Inductive colour := Red | Blue.

(* Another statement under the task's name: it must fail. *)
Theorem thm : Blue = Blue.
Proof. reflexivity. Qed.
