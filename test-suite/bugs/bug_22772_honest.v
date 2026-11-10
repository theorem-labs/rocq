(* HONEST CONTROL for rocq#22772: the same shape -- primitive arrays, an
   array literal under a binder, a Prop-valued T applied to it, proved with
   exact_no_check -- but every statement in it is TRUE.  A sound toolchain
   MUST accept this at every stage, coqc and rocqchk alike. *)
From Corelib Require Import PrimInt63 PrimArray.
Definition T' (a : array bool) : Prop := forall y : bool, get a 0 = get a 0.
Lemma bad' : forall x : bool, T' [| x | x |].
Proof. exact_no_check (fun (x y : bool) => @eq_refl bool (get [| x | x |] 0)). Qed.
Definition ok : bool -> bool -> True := fun x y => match bad' x y with eq_refl => I end.
Print Assumptions ok.

(* The honest reads through a trusted library of the Export route still
   compute, and under binders they now agree with cbv. *)
Definition mem := array bool.
Definition read (m : mem) (i : int) : bool := get m i.
Definition init (n : int) (b : bool) : mem := make n b.
Definition honest_read : forall x : bool, read (init 1 x) 0 = x := fun x => eq_refl.
