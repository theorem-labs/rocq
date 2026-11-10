Require Spec.
Require Agent.

(* What a wrongly granted merge would buy: the spec's block has no base case,
   so induction on it proves False, while the agent's coinductive copy is
   inhabited by [zeros]. *)
Definition bad : False := Spec.empty Agent.zeros.
