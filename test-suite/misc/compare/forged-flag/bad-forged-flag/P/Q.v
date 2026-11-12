(* A file of the task the answer leaves unchanged, so the config declares it
   pre-checked. Its given inductive Top.P.Q.T skips the positivity check,
   and the config tolerates assumed-positive on that object alone. *)

#[bypass_check(positivity)]
Inductive T : Type := mk : (T -> False) -> T.
