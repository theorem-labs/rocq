Private Inductive pos : Type := mk : nat -> pos.
Definition get (p : pos) : nat := match p with mk n => n end.
