(* The agent's own file, doing the two things a real proof does to the
   universe graph, both of which must pass.

   It Requires one more of the image's libraries than the statement file
   does. Img.Glue relates two of the levels the statements stand on, and the
   challenge files' own Require lines never reach it, so the answer's graph
   holds a constraint the challenge's closure does not. The challenge loads
   the same shared libraries the answer loaded, so that constraint is in
   both graphs.

   It also asserts a constraint between two of the image's levels itself,
   which is what the kernel records when a proof instantiates the image's
   definitions: the real task's key failed on exactly this shape
   (LinuxProcessSemantics.LinuxProcessSem.Fs.33 <= Stdlib.Logic.Classical_Pred_Type.21)
   and so did its untouched control. A constraint between the image's levels
   is the price of using the library, not a claim about the task, and the
   grade of record accepts every one of them. *)

Require Img.Glue.
Require Img.Third.

Monomorphic Constraint Img.Base.b < Img.Third.t.

Definition unused := Img.Extra.Other.
