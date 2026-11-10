(* Negative control: the agent's copy differs from the trusted one by ONE
   constructor argument (SX takes two arguments, not one), so the blocks do not
   match and -merge-inductives must refuse to merge them. *)
Inductive sev : Set :=
  | SW (fd b : nat)
  | SX (code extra : nat).
