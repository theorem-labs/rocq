(* The grader's trusted TaskSpecification copy of one inductive type. *)
Inductive sev : Set :=
  | SW (fd b : nat)
  | SX (code : nat).
