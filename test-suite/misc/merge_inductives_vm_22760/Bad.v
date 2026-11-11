Require Spec.
Require Agent.

(* rocq#22760's reproducer, over a type this run merges: Spec.Big and
   Agent.Big are the same declaration, so with the option they are one
   type here. *)
Import Spec.

Definition f1 (x : Big) : nat -> nat :=
  match x with C250 n => fun m => n | _ => fun m => 0 end.

Definition f2 (x : Big) : nat -> nat :=
  match x with C250 n => fun m => m | _ => fun m => 0 end.

Fail Definition no : f1 = f2 := eq_refl.
Definition yes : f1 = f2 := (eq_refl f1 <: f1 = f2).

Definition bad : False :=
  match f_equal (fun f => f (C250 1) 2) yes in _ = z
        return match z with 1 => True | _ => False end with
  | eq_refl => I
  end.

