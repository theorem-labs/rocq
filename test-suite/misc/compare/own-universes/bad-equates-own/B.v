(* A file of the answer's own tree makes two universes the challenge left
   apart into one. The challenge's statement is about Type@{p} and
   Type@{q} separately; under p = q it is about one universe twice, which
   is a different claim, and a proof that needs the two to meet proves less
   than the challenge asks.

   Both ends are universes the challenge's own files declare, so this is
   the answer's claim about the task, not the price of using a library, and
   it must fail. *)

Require Top.A.

Monomorphic Constraint Top.A.p <= Top.A.q.
Monomorphic Constraint Top.A.q <= Top.A.p.
