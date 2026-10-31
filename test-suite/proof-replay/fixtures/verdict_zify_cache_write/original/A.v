(* zify keeps a process-wide copy of its spec table, which init_cache fills
   and zify_iter_specs reads without filling it. [warm] fills it (zify_op,
   the first step of lia). [later] runs zify_iter_specs alone, so it finds
   the spec of Z.min only through [warm]'s copy. The edited tree changes
   [later] only, so it runs its tactics in both compiles while [warm]
   replays. Replay must leave the copy as [warm]'s tactics would have left
   it, else [later] fails only in the replay compile (breadth audit gap
   BA4). [warm] runs zify_op and not lia: a replayed lia term shares the
   string "BinInt" differently in the .vo (see vm_lia_hit). *)
From Stdlib Require Import ZArith Zify.
Open Scope Z_scope.

Lemma warm (x : Z) : x = x.
Proof. zify_op. exact eq_refl. Qed.

Lemma later (x y : Z) (H : Z.min x y = Z.min x y) : True.
Proof.
  zify_iter_specs.
  lazymatch goal with
  | H : context [Z.min] |- _ => fail "zify_iter_specs posed no spec"
  | _ => exact I
  end.
Qed.
