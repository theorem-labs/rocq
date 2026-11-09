(* [universes(template=no)] is not decoration: an [Inductive wrap (A : Type)]
   with no attribute is made template polymorphic automatically
   (vernac/comInductive.ml), and v1 never merges a template block. Spelling
   the attribute out is what makes this block monomorphic, which is the case
   this test is about: a Type-valued block whose universe level each file
   declares for itself, so the two copies match only once the levels are
   matched by the bijection and equated. *)
#[universes(template=no)]
Inductive wrap (A : Type) := Wrap : A -> wrap A.

Definition size (w : wrap nat) : nat := match w with Wrap _ a => S a end.

Definition Stmt := forall w : wrap nat, size w >= 1.
