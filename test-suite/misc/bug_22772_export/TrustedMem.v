(* Stands for a trusted task library that loads PrimArray and exports its operations. *)
From Corelib Require Export PrimInt63 PrimArray.
Definition mem := array bool.
Definition read (m : mem) (i : int) : bool := get m i.
Definition init (n : int) (b : bool) : mem := make n b.
