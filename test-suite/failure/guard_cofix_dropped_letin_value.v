(* A constructor whose own let-in DESTROYS one of its arguments. Iota
   computes the let-in value and call by value evaluates it, whether or not
   the selected branch reads the binder, and [apply_branch] substitutes it
   away, so it is dropped material that forces the block: `Eval cbv`
   overflows the stack. The rule before this file held only the UNREAD
   arguments of a let-in constructor to the strict rule, and never looked at
   the instantiated let-in VALUES, so each of these was accepted with a clean
   coqchk (BUGFINDV21-REPORT.md section 5c: b04, l02-l05 in dead material;
   b01, b02, b07, b09, b10 in live position, which stock Rocq 9.2.0 and the
   9.2 release also accept). *)

CoInductive SN : Type := ConsN : nat -> SN -> SN.
Definition hdN (s : SN) : nat := match s with ConsN a _ => a end.
Definition tlN (s : SN) : SN := match s with ConsN _ t => t end.

Inductive bx : Type := bk : forall (s : SN), let y := hdN s in nat -> bx.

(* The match is the body: live position. *)
Fail CoFixpoint b01 : SN := match bk b01 O with bk s n => ConsN n s end.

(* The same inside a dead let. *)
Fail CoFixpoint b04 : SN :=
  let dead := match bk b04 O with bk s n => ConsN n s end in ConsN O b04.

(* The dead position is a beta argument. *)
Fail CoFixpoint l02 : SN :=
  (fun _ : SN => ConsN O l02) (match bk l02 O with bk s n => ConsN n s end).

(* Two let-ins, the second reading the first. *)
Inductive bx2 : Type :=
  bk2 : forall (s : SN), let y := tlN s in let z := hdN y in nat -> bx2.
Fail CoFixpoint l03 : SN :=
  let dead := match bk2 l03 O with bk2 s n => ConsN n s end in ConsN O l03.

(* A record with a definitional field. *)
Record RL : Type := mkRL { rs : SN ; ry := hdN rs ; rn : nat }.
Fail CoFixpoint l04 : SN :=
  let dead := match mkRL l04 O with mkRL s n => ConsN n s end in ConsN O l04.

(* The cofixpoint takes a parameter. *)
Fail CoFixpoint l05 (k : nat) : SN :=
  let dead := match bk (l05 (S k)) k with bk s n => ConsN n s end in
  ConsN k (l05 (S k)).

(* The selected branch reads neither the argument nor the let-in binder: the
   let-in value is computed at iota all the same. *)
Fail CoFixpoint l06 : SN :=
  let dead := match bk l06 O with bk s n => ConsN O l06 end in ConsN O l06.
