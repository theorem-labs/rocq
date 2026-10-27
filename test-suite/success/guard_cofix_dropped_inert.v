(* An occurrence of a function of a cofixpoint block that the head reduction
   of check_one_cofix DROPS, and that is the head of its dropped term applied
   to any arguments that mention no function of the block, is a value that
   nothing forces: a cofixpoint is unfolded only as the scrutinee of a match
   or the argument of a projection, and a dropped term is never in either
   position. The co-recursive form of the fixpoint rule in
   success/guard_prefix_dropped_inert.v.

   Stock Rocq 9.2.0 accepts every definition here. The fork's check_erased
   (958e3aab1c) refused all of them before the commit that adds this file.
   The companion failure file guard_cofix_dropped_forced.v holds the shapes
   that are still refused: an occurrence something forces or reads. *)

CoInductive stream := Cons : nat -> stream -> stream.

(* A dead let value that is a bare occurrence. *)
CoFixpoint dropped_bare : stream :=
  let dead := dropped_bare in Cons O dropped_bare.

(* The occurrence is the branch a match on a known constructor does not
   select. *)
CoFixpoint dropped_branch : stream :=
  match O with O => Cons O dropped_branch | S _ => dropped_branch end.

(* The occurrence is the argument of a beta redex whose binder is unused. *)
CoFixpoint dropped_beta : stream :=
  (fun _ : stream => Cons O dropped_beta) dropped_beta.

(* A cofixpoint with an argument: the dropped term is the block applied to
   one argument, still a value. *)
CoFixpoint dropped_applied (k : nat) : stream :=
  let dead := dropped_applied (S k) in Cons k (dropped_applied (S k)).

(* A mutual block: the dropped occurrence names the other function. *)
CoFixpoint ev : stream := let dead := od in Cons O od
with od : stream := Cons (S O) ev.
