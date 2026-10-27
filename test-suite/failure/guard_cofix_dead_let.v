(* Same defect with the erased position the value of a let whose binder the
   body never reads. Accepted by febc57ac52, by d9061a3408 and by stock
   9.2.0, 9.3+rc1 and 9.4+alpha with coqchk 0; `Eval cbv in (hdL cycleL)`
   dies with "Error: Stack overflow". *)
CoInductive SL : Type := consL : SL -> SL.
Definition hdL (s : SL) : SL := match s with consL t => t end.

Fail Definition cycleL : SL :=
  cofix recur : SL := let dead := hdL recur in consL recur.
