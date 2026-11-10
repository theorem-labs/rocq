Require Spec Agent.
Definition H : Agent.get (Spec.mk 0) = Agent.get (Spec.mk 1) :=
  f_equal (A:=Spec.pos) Agent.get (Spec.pos_irr 0 1).
Definition bad : False :=
  eq_ind 0 (fun n => match n with 0 => True | S _ => False end) I 1 H.
Print Assumptions bad.
