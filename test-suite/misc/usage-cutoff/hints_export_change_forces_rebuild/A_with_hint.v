Inductive P : Prop := mkP.
Create HintDb hintcutoff.
#[export] Hint Constructors P : hintcutoff.
