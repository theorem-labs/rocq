Inductive sUnit : SProp := stt.

Inductive pair_with_lets : Type :=
| pack (x y : bool)
    (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).

Definition left (p : pair_with_lets) : bool :=
  match p with pack x y ghost1 ghost2 => x end.

Definition right (p : pair_with_lets) : bool :=
  match p with pack x y ghost1 ghost2 => y end.

Fail
Definition collision (p : pair_with_lets) :
  left p = right p := eq_refl.

(* Guards: these must keep compiling. A case comparing two syntactically
   equal terms would prove nothing, since the syntactic fast path accepts it
   before the branch contexts are ever walked. *)

(* Two different branch bodies over the same context still convert. *)
Definition reaches_branches (p : pair_with_lets) :
  (match p with pack x y _ _ => x end)
  = (match p with pack x y _ _ => andb true x end) := eq_refl.

(* A surviving SProp FIELD, next to an SProp local definition: it must still
   be read as irrelevant, so proof irrelevance identifies the two. *)
Inductive with_sprop_field : Type :=
| packs (x : bool) (s : sUnit) (ghost : sUnit := stt).

Definition sprop_field_irrelevant (f : sUnit -> bool) (p : with_sprop_field) :
  (match p with packs x s ghost => f s end)
  = (match p with packs x s ghost => f ghost end) := eq_refl.
