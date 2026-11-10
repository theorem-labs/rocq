(* The trusted Checker: the one file of a grade that requires BOTH trees.
   It states the obligation over the TRUSTED copy of sev and discharges it with
   the agent's theorem, which is stated over the AGENT's copy. Without
   -merge-inductives the two copies are two types and this file does not
   compile; with it the agent's block takes the trusted block's canonical name
   and the file compiles. *)
Require Spec.Dup.
Require Agent.Proof.

Definition agent_weight : Spec.Dup.sev -> nat := Agent.Proof.weight.

Definition check : forall s : Spec.Dup.sev, agent_weight s = agent_weight s :=
  Agent.Proof.weight_refl.
