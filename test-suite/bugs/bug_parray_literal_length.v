(* An array literal longer than PrimArray.max_length must be refused by the
   kernel: lazy reduction truncates it to max_length while the VM keeps it
   whole, which made its length provably both 4194303 and 4194304. *)

From Corelib Require Import PrimInt63 PrimArray.
From Ltac2 Require Import Ltac2.

Ltac2 literal (n : int) :=
  match Constr.Unsafe.kind '[| true | true : bool |] with
  | Constr.Unsafe.Array u _ def ty =>
    Constr.Unsafe.make (Constr.Unsafe.Array u (Array.make n 'true) def ty)
  | _ => Control.throw Not_found
  end.

(* A literal of exactly max_length is accepted, and both machines agree on
   its length. *)
Definition ok : array bool := ltac2:(let c := literal 4194303 in exact $c).
Definition ok_lazy : PrimArray.length ok = 4194303%uint63 := eq_refl.
Definition ok_vm : PrimArray.length ok = 4194303%uint63 :=
  (eq_refl 4194303%uint63 <: PrimArray.length ok = 4194303%uint63).

(* One element more is refused. *)
Fail Definition bad : array bool := ltac2:(let c := literal 4194304 in exact $c).
