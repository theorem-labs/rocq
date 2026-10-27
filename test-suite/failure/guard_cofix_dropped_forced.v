(* The companion of success/guard_cofix_dropped_inert.v: dropped material of
   a cofixpoint that mentions the block in a position where a reduction can
   still force it, or that mentions it other than at the head. Each is
   refused on the guard checker's own line.

   The first three are the attacks the fork's check_erased exists for
   (test-suite/failure/guard_cofix_dead_{beta,let,match}.v): a dead
   position holds a DESTRUCTION of the cofixpoint, whose head is a constant
   that matches on it, not a function of the block. Accepting one is a
   cofixpoint whose evaluation does not terminate (`Eval cbv`
   stack-overflows). *)

CoInductive SL : Type := consL : SL -> SL.
Definition hdL (s : SL) : SL := match s with consL t => t end.

(* attack: a dead let holds a destruction of the cofixpoint. *)
Fail Definition cycleL : SL := cofix recur : SL := let dead := hdL recur in consL recur.

(* attack: the dead position is a beta argument. *)
Fail Definition cycleB : SL := cofix recur : SL := (fun _ : SL => consL recur) (hdL recur).

(* attack: the dead position is the unselected branch of a match. *)
Fail Definition cycleM : SL :=
  cofix recur : SL := match O with O => consL recur | S _ => hdL recur end.

(* A dropped term whose head is the block but one of whose arguments destroys
   the block: the argument is not inert. *)
CoInductive stream := Cons : nat -> stream -> stream.
Definition hd_ (s : stream) : nat := match s with Cons n _ => n end.
Fail Definition forced_arg : stream :=
  cofix recur (k : nat) : stream := let dead := recur (hd_ (recur k)) in Cons k (recur (S k)).

(* A recorded cost: the occurrence is inside a constructor, so its head is
   not the block. Stock accepts; the fork refuses. *)
Fail Definition inside_ctor : SL :=
  cofix recur : SL := let dead := consL recur in consL recur.

(* A constructor argument the selected branch does not read, but that a
   constructor-internal let-in DESTRUCTS: call-by-value computes the let-in
   value at iota, so the dropped occurrence is forced after all. *)
Inductive bx : Type := bk : forall (s : stream), let y := hd_ s in nat -> bx.
Fail Definition forced_by_letin : stream :=
  cofix fF : stream := match bk fF 0 with bk s n => Cons 0 fF end.

(* The case-inversion indices of a match on a constructor are dropped by
   iota, and keep the strict rule: a destruction of the block there is
   refused even when the scrutinee reaches the constructor only through an
   inert dropped occurrence. *)
Module CaseInvertIndices.
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.
Definition zz (s : stream) : nat := (fun _ : nat => 0) (hd_ s).
Definition mk (s : stream) : seq 0 (zz s) := @srefl nat 0.
Fail Definition forced_index : stream :=
  cofix r : stream := match mk r in seq _ _ return stream with srefl _ => Cons 0 r end.
End CaseInvertIndices.
