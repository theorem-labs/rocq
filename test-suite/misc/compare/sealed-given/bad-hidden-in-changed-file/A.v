(* The given Top.S.H.hx is hidden by a seal in the challenge file S.v, which
   the answer may change. The declaration comparison does not see a hidden
   field, so the comparator refuses it: fail-closed, though this answer
   leaves S.v as the challenge has it. *)

Require Top.S.
Require Top.S.Given.

Theorem thm : True.
Proof. exact Top.S.H.q. Qed.
