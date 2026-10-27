(* Same defect with the erased position a branch that a match on a known
   constructor never selects. Accepted by febc57ac52, by d9061a3408 and by
   stock 9.2.0, 9.3+rc1 and 9.4+alpha with coqchk 0. This one evaluates
   normally — the hidden occurrence is unreachable for every strategy — so
   it is refused for the same reason as the other two and not for a
   measured divergence. *)
CoInductive SM : Type := consM : SM -> SM.
Definition hdM (s : SM) : SM := match s with consM t => t end.

Fail Definition cycleM : SM :=
  cofix recur : SM := match O with O => consM recur | S _ => hdM recur end.
