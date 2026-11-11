(* Three of the four routes to False through rocq#22772 collected by the
   BET-970 planner (dispatch://BET-970/artifact/rocq-22772-probes-md).  They
   all rest on the kernel taking [get [| x | x |] 0 = y] for [y = y]; each one
   reaches it by a different road, and the kernel must refuse all of them.
   The fourth route (a trusted library exporting the array operations, with an
   agent file that writes no array word, no literal and no exact_no_check) is
   test-suite/misc/bug_22772_export.sh. *)

From Corelib Require Import PrimInt63 PrimArray.

(* Route 1: the reproducer of the issue, verbatim. *)

Definition T (a : array bool) : Prop := forall y : bool, get a 0 = y.

Lemma bad : forall x : bool, T [| x | x |].
Proof.
  exact_no_check (fun (x y : bool) => @eq_refl bool y).
  Fail Qed.
Abort.

(* Route 2: the false equation routed through [true = false], so that
   [Print Assumptions] of the resulting [False] says "Closed under the global
   context" rather than naming the array axioms. *)

Fail Definition tf : true = false :=
  (fun x : bool => (fun y : bool => @eq_refl bool y) : T [| x | x |]) true false.

(* Route 3: no array word and no array literal in the statement.  The array
   operations are fetched by Ltac2 from identifiers built out of strings and
   the array is built with [make]. *)

From Corelib Require PrimArray.
From Ltac2 Require Import Ltac2.

Ltac2 i (s : string) := Option.get (Ident.of_string s).
Ltac2 g (s : string) :=
  Env.instantiate (Option.get (Env.get [i "Corelib"; i "Array"; i (String.app "Prim" "Array"); i s])).
Ltac2 n (k : int) := Constr.Unsafe.make (Constr.Unsafe.Uint63 (Uint63.of_int k)).

Definition Tok : bool -> Prop :=
  ltac2:(let get := g "get" in let mk := g "make" in let arr := g "array" in
         let z := n 0 in let o := n 1 in
         exact (fun x : bool =>
                  (fun (a : $arr bool) => forall y : bool, $get bool a $z = y)
                    ($mk bool $o x))).

Lemma bad_ok : forall x, Tok x.
Proof.
  ltac1:(exact_no_check (fun (x y : bool) => @eq_refl bool y)).
  Fail Qed.
Abort.
