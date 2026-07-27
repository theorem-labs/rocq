(* Printing Sort Quality Variables Anonymously: sort quality variables
   that have no name print as "_" (which parses back, denoting a fresh
   quality variable) instead of their raw α-names (which do not). *)
Set Universe Polymorphism.
Definition idT@{s;u} (A : Type@{s;u}) (a : A) := a.

(* On this branch [Check] collapses an undetermined sort quality to
   [Type], so the flag is exercised through a type-error message, where
   the fresh, unnameable sort quality variable of the instance is kept.
   It prints as a raw α-name by default... *)
Set Printing Universes.
Fail Definition bad := (idT : nat).
(* ...and as _ under the flag. *)
Set Printing Sort Quality Variables Anonymously.
Fail Definition bad := (idT : nat).
Unset Printing Sort Quality Variables Anonymously.
Unset Printing Universes.

(* Named quality variables are unaffected: the binder name is kept. *)
Print idT.
About idT.

(* The anonymous form parses back: "_" is accepted as the sort quality
   of a sort annotation (it was already accepted in universe
   instances), denoting a fresh quality variable. *)
Check Type@{_ ; Set}.
Check idT@{_ ; Set}.
