(* SpecN.v word for word, over this library's own global universe [u]. *)

Universe u.

Inductive wrap (A : Type@{u}) := Wrap : A -> wrap A.
