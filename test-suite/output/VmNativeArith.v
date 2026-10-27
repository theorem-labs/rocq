(* The bytecode machine evaluates Z.add, Z.pos_sub and Pos.add natively, as one
   machine word each, when it recognizes the definition (kernel/vmznative.ml and
   the CHECKZADD, CHECKZPOSSUB and CHECKPOSADD instructions of
   kernel/byterun/rocq_interp.c). This test holds the three definitions the
   expected encodings of kernel/vmznative.ml were taken from, and checks:

   (a) that each of the three is recognized, and each near miss is not, from the
       one line [Set Debug "vmznative"] prints per declaration;
   (b) that each copy IS the standard library's function, by the kernel's own
       conversion, so that a library definition that moves away from the pinned
       encoding fails here;
   (c) that the values the machine computes with the native path are the values
       cbv computes without it, below, at and above the 2^60 window the native
       code works in, for both signs and for Z0;
   (d) that a constant with a native operation is still the function its body
       defines: the machine compares it against the library's function, which
       is a conversion of two fixpoints or of two functions, and against a
       partial application of it.

   The copies go through the type alias [Id], which [Vmbinnum] refuses, because
   Corelib's own three constants are BINNUM routines and the native operation is
   put only where BINNUM is not (kernel/vmbytegen.ml). A copy is what exercises
   the native path, here and in the lane's review files. *)

Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef.
Local Open Scope positive_scope.

Ltac vmc := lazymatch goal with |- @eq ?T ?l ?r => vm_cast_no_check (@eq_refl T r) end.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).

Definition Id (T : Set) : Set := T.

Set Debug "vmznative".

(* Pos.add and Pos.add_carry. Only the function the constant denotes carries the
   operation: add_carry's own encoding is a different one, and is not pinned. *)
Fixpoint padd (x y : Id positive) : Id positive :=
  match x, y with
    | p~1, q~1 => (padd_carry p q)~0
    | p~1, q~0 => (padd p q)~1
    | p~1, 1 => (Pos.succ p)~0
    | p~0, q~1 => (padd p q)~1
    | p~0, q~0 => (padd p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (Pos.succ q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end
with padd_carry (x y : Id positive) : Id positive :=
  match x, y with
    | p~1, q~1 => (padd_carry p q)~1
    | p~1, q~0 => (padd_carry p q)~0
    | p~1, 1 => (Pos.succ p)~1
    | p~0, q~1 => (padd_carry p q)~0
    | p~0, q~0 => (padd p q)~1
    | p~0, 1 => (Pos.succ p)~0
    | 1, q~1 => (Pos.succ q)~1
    | 1, q~0 => (Pos.succ q)~0
    | 1, 1 => 1~1
  end.

(* Z.pos_sub. *)
Fixpoint zpos_sub (x y : Id positive) {struct y} : Id Z :=
  match x, y with
    | p~1, q~1 => Z.double (zpos_sub p q)
    | p~1, q~0 => Z.succ_double (zpos_sub p q)
    | p~1, xH => Zpos p~0
    | p~0, q~1 => Z.pred_double (zpos_sub p q)
    | p~0, q~0 => Z.double (zpos_sub p q)
    | p~0, xH => Zpos (Pos.pred_double p)
    | xH, q~1 => Zneg q~0
    | xH, q~0 => Zneg (Pos.pred_double q)
    | xH, xH => Z0
  end.

(* Z.add. *)
Definition zadd (x y : Id Z) : Id Z :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (Pos.add x' y')
    | Zpos x', Zneg y' => Z.pos_sub x' y'
    | Zneg x', Zpos y' => Z.pos_sub y' x'
    | Zneg x', Zneg y' => Zneg (Pos.add x' y')
  end.

(* Near misses: Z.sub is another definition, and a copy of Z.add with one branch
   changed is not Z.add. Neither is recognized. *)
Definition zsub (x y : Id Z) : Id Z := Z.sub x y.
Definition zadd_bad (x y : Id Z) : Id Z :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (Pos.add x' y')
    | Zpos x', Zneg y' => Z.pos_sub x' y'
    | Zneg x', Zpos y' => Z.pos_sub x' y'
    | Zneg x', Zneg y' => Zneg (Pos.add x' y')
  end.

Set Debug "-vmznative".

(* (b) Each copy is the library's function, by the kernel's conversion. *)
Definition is_padd : padd = Pos.add := eq_refl.
Definition is_zpos_sub : zpos_sub = Z.pos_sub := eq_refl.
Definition is_zadd : zadd = Z.add := eq_refl.

(* (c) The values. [two n] is 2^n as a chain the bytecode builds at check time,
   so the inputs are not literals the compiler could fold. 2^60 is the first
   magnitude the native code refuses; the machine then runs the body. *)
Fixpoint two (n : nat) : positive := match n with O => 1 | S m => (two m)~0 end.

Definition small_l : padd (two 10) 1~1 = cbv_val (padd (two 10) 1~1) := ltac:(vmc).
Definition edge58 : padd (two 58) (two 58) = cbv_val (padd (two 58) (two 58)) := ltac:(vmc).
Definition edge59 : padd (two 59) (two 59) = cbv_val (padd (two 59) (two 59)) := ltac:(vmc).
Definition over60 : padd (two 70) (two 70) = cbv_val (padd (two 70) (two 70)) := ltac:(vmc).
Definition carry_l : padd (two 40) (Pos.pred_double (two 39))
  = cbv_val (padd (two 40) (Pos.pred_double (two 39))) := ltac:(vmc).

Definition sub_lt : zpos_sub (two 20) (two 30) = cbv_val (zpos_sub (two 20) (two 30)) := ltac:(vmc).
Definition sub_gt : zpos_sub (two 30) (two 20) = cbv_val (zpos_sub (two 30) (two 20)) := ltac:(vmc).
Definition sub_eq : zpos_sub (two 30) (two 30) = cbv_val (zpos_sub (two 30) (two 30)) := ltac:(vmc).
Definition sub_big : zpos_sub (two 80) (two 20) = cbv_val (zpos_sub (two 80) (two 20)) := ltac:(vmc).

Definition add_pp : zadd (Zpos (two 20)) (Zpos (two 21)) = cbv_val (zadd (Zpos (two 20)) (Zpos (two 21)))
  := ltac:(vmc).
Definition add_pn : zadd (Zpos (two 20)) (Zneg (two 21)) = cbv_val (zadd (Zpos (two 20)) (Zneg (two 21)))
  := ltac:(vmc).
Definition add_nn : zadd (Zneg (two 20)) (Zneg (two 20)) = cbv_val (zadd (Zneg (two 20)) (Zneg (two 20)))
  := ltac:(vmc).
Definition add_z0 : zadd Z0 (Zneg (two 20)) = cbv_val (zadd Z0 (Zneg (two 20))) := ltac:(vmc).
Definition add_big : zadd (Zpos (two 80)) (Zneg (two 79)) = cbv_val (zadd (Zpos (two 80)) (Zneg (two 79)))
  := ltac:(vmc).

(* The native code refuses an argument it cannot read, and the body runs: the
   two sides of each equation below are the same stuck term. *)
Definition stuck_p (p : positive) : padd p (two 10) = padd p (two 10) := ltac:(vmc).
Definition stuck_z (z : Z) : zadd z (Zpos (two 10)) = zadd z (Zpos (two 10)) := ltac:(vmc).

(* (d) The constants are still the functions their bodies define: the machine
   converts each against the library's, which compares two fixpoints for padd
   and zpos_sub and two functions for zadd, and converts a partial application
   of one. A value that stood for the operation instead of the function would
   fail here. *)
Definition conv_padd : padd = Pos.add := ltac:(vmc).
Definition conv_zpos_sub : zpos_sub = Z.pos_sub := ltac:(vmc).
Definition conv_zadd : zadd = Z.add := ltac:(vmc).
Definition conv_partial : (fun x => zadd x (Zpos 1)) = (fun x => Z.add x (Zpos 1)) := ltac:(vmc).
Fail Definition conv_wrong : zadd = Z.sub := ltac:(vmc).
