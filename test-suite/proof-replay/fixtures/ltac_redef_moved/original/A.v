(* flag is redefined with ::=, as a file redefines a Zify flag. target runs
   use_flag, which reads flag. The edited tree moves the redefinition down
   three lines and keeps its value: only its source locations change, so
   target must replay. *)
Ltac flag := constr:(true).
Ltac use_flag := let b := flag in lazymatch b with false => exact I | true => exact I end.

Ltac flag ::= constr:(false).

Lemma target : True.
Proof. use_flag. Qed.
