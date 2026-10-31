(* A match binds a let-in of a constructor type and reads its body back as it
   stands. The type of the let-in is what gives the body a common supertype,
   so it is inferred as the type of an argument is, at CUMUL. These are the
   readings of that rule which test-suite/bugs/bug_22675.v does not make: the
   inferred variance read through subtyping, a let-in whose type is a function
   type, and a universe carried through a second inductive. *)

Set Universe Polymorphism.

Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Cumulative Inductive outer@{u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

(* what the inference produced, read through subtyping: u is invariant, so
   outer@{u2 v} is not a supertype of outer@{u1 v} even under u1 < u2. *)
Fail Definition up@{u1 u2 v | u1 < u2, u2 < v} (x : outer@{u1 v}) : outer@{u2 v} := x.

(* the let-in's type is a function type: u is reached through the codomain *)
Fail Cumulative Inductive lazy_outer@{*u v | u < v} : Set :=
| make_lazy_outer (f : unit -> token@{u v} := fun _ => make_token@{u v}).

Cumulative Inductive lazy_outer@{u v | u < v} : Set :=
| make_lazy_outer (f : unit -> token@{u v} := fun _ => make_token@{u v}).

(* A universe which is irrelevant for the inductive a let-in's type names stays
   irrelevant. holder is the base of holder2 below, whose let-in's type names an
   inductive which has a let-in of its own. *)
Cumulative Inductive phantom@{*u} : Set := make_phantom.

Cumulative Inductive holder@{*u} : Set :=
| make_holder (x : phantom@{u} := make_phantom@{u}).

Cumulative Inductive holder2@{*u} : Set :=
| make_holder2 (x : holder@{u} := make_holder@{u}).
