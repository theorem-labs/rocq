(* The agent's own file. Pre.Glue is a shared library that relates two of the
   levels the statements stand on, and the challenge files' own Require lines
   never reach it, so the answer's universe graph holds a constraint the
   challenge's closure does not. The answer did not assert it: a shared
   library did, and the challenge now loads the same shared libraries the
   answer loaded, so the constraint is in both graphs and no theorem fails
   for it.

   The answer's environment reaches Pre.Glue twice over: this Require, and
   the config's pre-checked list, which this harness must pin because it
   binds the shared tree with -Q. The image's own libraries need no -Q and
   are pinned by nothing, which is the production shape. *)

Require Pre.Glue.

Definition unused := Pre.Extra.Other.
