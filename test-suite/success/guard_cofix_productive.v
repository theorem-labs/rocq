(* The erased-material rule in [check_one_cofix] must not touch an ordinary
   productive cofixpoint, including one whose body needs a delta step and a
   beta step before a constructor shows (every argument of that redex is
   read, so nothing is erased), one that destructs its argument, and a
   prefix whose erased material holds no recursive occurrence at all. *)
CoInductive SP : Type := consP : nat -> SP -> SP.

CoFixpoint onesP : SP := consP 1 onesP.

Definition mkP (n : nat) (s : SP) : SP := consP n s.
CoFixpoint twosP : SP := mkP 2 twosP.

CoFixpoint mapP (f : nat -> nat) (s : SP) : SP :=
  match s with consP n t => consP (f n) (mapP f t) end.

(* an erased let and an erased beta argument that mention nothing of the
   block: both are submitted to the analysis and both pass *)
CoFixpoint deadharmlessP : SP := let dead := 1 + 1 in consP 3 deadharmlessP.
CoFixpoint deadbetaP : SP := (fun _ : nat => consP 4 deadbetaP) (2 + 2).

Definition hdP (s : SP) : nat := match s with consP n _ => n end.

Print Assumptions onesP.
Print Assumptions twosP.
Print Assumptions mapP.
Print Assumptions deadharmlessP.
Print Assumptions deadbetaP.
Example mapP_computes : hdP (mapP S twosP) = 3 := eq_refl.
Example deadharmlessP_computes : hdP deadharmlessP = 3 := eq_refl.
Example deadbetaP_computes : hdP deadbetaP = 4 := eq_refl.
