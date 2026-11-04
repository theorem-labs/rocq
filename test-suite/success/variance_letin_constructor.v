(* The body of a let-in of a constructor type is an extracted position: a match
   binds that let-in, and the constructor the body names brings its own let-ins
   with it. So the universes of a constructor applied there are inferred by the
   variance of that constructor's inductive, as for a value of it, even though
   the constructor is fully applied. *)

Set Universe Polymorphism.

Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Fail Cumulative Inductive outer@{*u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

Fail Cumulative Inductive outer@{+u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

Cumulative Inductive outer@{u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

(* what the inference produced, read through subtyping *)
Fail Definition up@{u1 u2 v | u1 < v, u2 < v} (x : outer@{u1 v}) : outer@{u2 v} := x.

(* under a binder *)
Fail Cumulative Inductive lazy_outer@{*u v | u < v} : Set :=
| make_lazy_outer (f : unit -> token@{u v} := fun _ => make_token@{u v}).

Cumulative Inductive lazy_outer@{u v | u < v} : Set :=
| make_lazy_outer (f : unit -> token@{u v} := fun _ => make_token@{u v}).

(* A universe which is irrelevant for the inductive the body names stays
   irrelevant: no let-in of its constructors can read it back. *)
Cumulative Inductive phantom@{*u} : Set := make_phantom.

Cumulative Inductive holder@{*u} : Set :=
| make_holder (x : phantom@{u} := make_phantom@{u}).

Cumulative Inductive holder2@{*u} : Set :=
| make_holder2 (x : holder@{u} := make_holder@{u}).
