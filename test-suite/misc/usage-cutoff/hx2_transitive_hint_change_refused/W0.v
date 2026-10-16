Definition w := 0.
Parameter p : nat -> Prop.
Axiom pp : p 0.
Create HintDb wdb.
#[export] Hint Resolve pp : wdb.
