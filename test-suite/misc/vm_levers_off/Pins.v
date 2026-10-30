(* The three functions kernel/vmznative.ml pins (Pos.add, Z.pos_sub, Z.add),
   copied from output/VmNativeArith.v, with a caller of each. The copies go
   through the type alias [Id], which [Vmbinnum] refuses, so what the machine
   does with them is the native path alone (kernel/vmbytegen.ml).

   misc/vm_levers_off.sh compiles this file with the VM levers on and off and
   reads the dumps. *)

Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef.
Local Open Scope positive_scope.

Definition Id (T : Set) : Set := T.

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

Definition zadd (x y : Id Z) : Id Z :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (Pos.add x' y')
    | Zpos x', Zneg y' => Z.pos_sub x' y'
    | Zneg x', Zpos y' => Z.pos_sub y' x'
    | Zneg x', Zneg y' => Zneg (Pos.add x' y')
  end.

(* Callers, so a dump holds the code of a call site as well as of the function. *)
Definition use_padd (x y : Id positive) : Id positive := padd x y.
Definition use_zpos_sub (x y : Id positive) : Id Z := zpos_sub x y.
Definition use_zadd (x y : Id Z) : Id Z := zadd x y.
