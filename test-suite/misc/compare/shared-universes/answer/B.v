(* The agent's own file, which Requires one more shared library than the
   statement file does. Pre.Glue relates Pre.Base.b and Pre.Extra.e, the two
   levels the statements stand on, so the answer's universe graph holds a
   constraint the challenge files' own closure never reaches. The answer did
   not assert it: the image did, and the challenge loads the same file. *)

Require Pre.Glue.

Definition unused := Pre.Extra.Other.
