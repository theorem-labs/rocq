(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)

Definition f : nat -> nat.
Proof. fix rec 1. exact (id (fun n : nat => n)). Defined.

Definition k : nat -> nat.
Proof. fix rec 1. exact (let t := 0 in fun n : nat => t). Defined.

Definition m1 : nat -> nat -> nat.
Proof. fix rec 2. exact (id (fun a n : nat => Nat.sub a n)). Defined.

Definition p (x : nat) : nat -> nat.
Proof. fix rec 1. exact (id (fun _ : nat => x)). Defined.

Fixpoint ev (n : nat) : bool := match n with 0 => true | S m => od m end
with od : nat -> bool := id (fun n : nat => false).

Definition k2 : nat -> nat -> nat.
Proof. fix rec 1. exact (let t := Nat.add 1 2 in fun n m : nat => Nat.add t m). Defined.

Fixpoint dbl (i x : nat) : nat := match i with 0 => x | S j => dbl j (dbl j x) end.

Definition d : nat -> nat.
Proof.
  fix rec 1. pose (dead := dbl 60 0). intro n.
  destruct n as [|q]. - exact 0. - exact q.
Defined.

Definition k3 : nat -> nat -> nat.
Proof. fix rec 1. exact (let t := Nat.add 1 2 in fun n m : nat => Nat.add t (Nat.sub n m)). Defined.

Definition k4 : nat -> nat -> nat.
Proof.
  fix rec 2.
  exact (let t := Nat.add 1 2 in fun a : nat => id (fun n : nat => Nat.add t (Nat.sub a n))).
Defined.

Definition k5 : nat -> nat.
Proof. fix rec 1. exact (let t := Nat.add 1 2 in id (fun n : nat => Nat.add t n)). Defined.

Definition m3 : nat -> nat -> nat.
Proof. fix rec 2. exact (fun a : nat => let t := Nat.add a 1 in id (fun n : nat => Nat.sub t n)). Defined.

Goal forall n, f n = f n.
Proof. intro n. vm_compute. reflexivity. Qed.

Goal forall n, k n = k n.
Proof. intro n. vm_compute. reflexivity. Qed.

Goal forall a n, m1 a n = m1 a n.
Proof. intros a n. vm_compute. reflexivity. Qed.

Goal forall n, od n = od n.
Proof. intro n. vm_compute. reflexivity. Qed.

Goal f 5 = 5.
Proof. vm_compute. match goal with |- 5 = 5 => reflexivity end. Qed.

Goal m1 5 2 = 3.
Proof. vm_compute. match goal with |- 3 = 3 => reflexivity end. Qed.

Goal p 7 3 = 7.
Proof. vm_compute. match goal with |- 7 = 7 => reflexivity end. Qed.

Goal ev 3 = false.
Proof. vm_compute. match goal with |- false = false => reflexivity end. Qed.

Goal k 5 = 0.
Proof. vm_compute. match goal with |- 0 = 0 => reflexivity end. Qed.

Goal k2 0 4 = 7.
Proof. vm_compute. match goal with |- 7 = 7 => reflexivity end. Qed.

Goal forall n m, k2 n m = k2 n m.
Proof. intros n m. vm_compute. reflexivity. Qed.

Goal k3 5 1 = 7.
Proof. vm_compute. match goal with |- 7 = 7 => reflexivity end. Qed.

Goal k4 5 1 = 7.
Proof. vm_compute. match goal with |- 7 = 7 => reflexivity end. Qed.

Goal k5 4 = 7.
Proof. vm_compute. match goal with |- 7 = 7 => reflexivity end. Qed.

Goal m3 5 2 = 4.
Proof. vm_compute. match goal with |- 4 = 4 => reflexivity end. Qed.

Goal forall n, k5 n = k5 n.
Proof. intro n. vm_compute. reflexivity. Qed.

Goal forall a n, m3 a n = m3 a n.
Proof. intros a n. vm_compute. reflexivity. Qed.

Goal d 3 = 2.
Proof. Timeout 10 vm_compute. match goal with |- 2 = 2 => reflexivity end. Qed.

Definition f5 : f 5 = 5 := (eq_refl 5 <: f 5 = 5).
