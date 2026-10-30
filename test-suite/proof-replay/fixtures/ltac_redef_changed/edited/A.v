(* flag is redefined with ::=, as a file redefines a Zify flag. target runs
   use_flag, which reads flag and succeeds on either value. The edited tree
   changes the redefinition from false to true, so target must miss on the
   tactic_definition read. *)
Ltac flag := constr:(true).
Ltac use_flag := let b := flag in lazymatch b with false => exact I | true => exact I end.

Ltac flag ::= constr:(true).

Lemma target : True.
Proof. use_flag. Qed.
