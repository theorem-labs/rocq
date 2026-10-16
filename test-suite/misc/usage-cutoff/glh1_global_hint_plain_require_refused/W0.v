Definition w := 0.
Inductive P : Prop := mkP.
Create HintDb wdb.
#[global] Hint Resolve mkP : wdb.
