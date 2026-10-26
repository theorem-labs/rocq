(* Checked with -vok against Lib's .vos: [hidden]'s body cannot be read. A
   walk that meets such a body is not recorded, so [use_hidden] and
   [use_both], whose walks meet it, are never replayed; [shown] and what it
   uses are. *)

Require Import Memo.Lib.

Definition use_hidden := hidden.
Definition use_both := hidden + shown.

Print Assumptions use_both.
Print Assumptions use_both.
Print Assumptions use_hidden.
Print Assumptions use_hidden.
Print Assumptions shown.
