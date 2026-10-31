
Set Universe Polymorphism.

Fail Cumulative Inductive token@{*u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

Fail Definition small@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (make_token@{u v}).

(* The position is invariant, not covariant: asking for covariance in the
   letin's universe must be refused too. *)
Fail Cumulative Inductive tokcov@{+u v | u < v} : Set :=
| make_tokcov (ghost : Type@{v} := Type@{u}).
