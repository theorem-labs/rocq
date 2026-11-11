Require Spec.
Require Agent.

(* What a wrongly granted merge would buy: Spec knows its colour is Red or
   Green, the agent has a third one, and if the two blocks were one type the
   agent's third colour would have to be one of Spec's two. *)
Definition bad : False :=
  match Spec.all Agent.b with
  | or_introl e => Agent.b_ne_red e
  | or_intror e => Agent.b_ne_green e
  end.
