(* A dropped term whose head is a STUCK match or projection applied to an
   occurrence of the block. The match is a redex in waiting: once its
   scrutinee resolves (the cofixpoint's own argument instantiated, an
   instance of a functor, call-by-value) the selected branch destroys the
   occurrence, so evaluation does not terminate (`Eval cbv` overflows the
   stack, as for guard_cofix_dead_let.v). The arguments of a stuck match or
   projection are held to the strict rule, like its scrutinee. Each case was
   accepted with a clean coqchk by the reconciled member before this file
   (BUGFINDV21-REPORT.md section 2: a01 a03 a19 n01 a14 d03). *)

CoInductive SN : Type := ConsN : nat -> SN -> SN.
Definition hdN (s : SN) : nat := match s with ConsN a _ => a end.
Definition tlN (s : SN) : SN := match s with ConsN _ t => t end.

(* The match is on the cofixpoint's own parameter. *)
Fail Definition a01 : bool -> SN :=
  cofix f (b : bool) : SN :=
    let dead := (match b with true => hdN | false => fun _ : SN => O end) (f b) in
    ConsN O (f b).

(* A primitive projection of a stuck record. *)
Set Primitive Projections.
Record R : Type := mkR { fld : SN -> nat }.
Unset Primitive Projections.
Fail Definition a03 : R -> SN :=
  cofix f (x : R) : SN := let dead := fld x (f x) in ConsN O (f x).

(* A non-primitive record projection. *)
Record RN : Type := mkRN { fldN : SN -> nat }.
Fail Definition a19 : RN -> SN :=
  cofix f (x : RN) : SN := let dead := fldN x (f x) in ConsN O (f x).

(* Ordinary stream code: the scrutinee is a value read from the input. *)
Fail CoFixpoint n01 (s : SN) : SN :=
  let dead := (match hdN s with O => hdN | S _ => fun _ : SN => O end) (n01 (tlN s)) in
  ConsN (S (hdN s)) (n01 (tlN s)).

(* In a functor the match on the parameter is stuck; refusing it at coqc keeps
   coqc and coqchk in agreement (an instance selects [hdN]). *)
Module Type PT. Parameter sel : bool. End PT.
Module Mk (X : PT).
  Fail CoFixpoint r : SN := let dead := (if X.sel then hdN else fun _ : SN => O) r in ConsN O r.
End Mk.

Module Type PR. Parameter x : R. End PR.
Module MkR (X : PR).
  Fail CoFixpoint r : SN := let dead := fld X.x r in ConsN O r.
End MkR.
