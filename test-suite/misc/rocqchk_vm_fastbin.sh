#!/usr/bin/env bash
# The VM's binary-number acceleration is an execution optimization only: coqchk must accept the
# same VM-cast proofs with it enabled, and the test must exercise every installed fast path.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cat > "$d/FastBin.v" <<'EOF'
From Stdlib Require Import ZArith NArith PArith.

Definition x := 1234567890123%positive.
Definition y := 987654321011%positive.
Definition zx := Zpos x.
Definition zy := Zpos y.

Lemma compare_cont_vm : Pos.compare_cont Eq x y = Gt.
Proof. vm_compute. reflexivity. Qed.

Lemma eqb_vm : Pos.eqb x y = false.
Proof. vm_compute. reflexivity. Qed.

Lemma add_vm : Pos.add x y = 2222222211134%positive.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_vm : Pos.mul 12345%positive 6789%positive = 83810205%positive.
Proof. vm_compute. reflexivity. Qed.

Lemma zcompare_vm : Z.compare zx zy = Gt.
Proof. vm_compute. reflexivity. Qed.

Lemma zeqb_vm : Z.eqb zx zy = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nat_eqb_vm : Nat.eqb 12345 6789 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nat_leb_vm : Nat.leb 6789 12345 = true.
Proof. vm_compute. reflexivity. Qed.
EOF
rocq c -bytecode-compiler yes -Q "$d" "" "$d/FastBin.v"
rocqchk -bytecode-compiler yes -Q "$d" "" FastBin
ROCQ_VM_FASTBIN=1 ROCQ_VM_FASTBIN_STATS=1 rocqchk -bytecode-compiler yes -Q "$d" "" FastBin \
  > "$d/fastbin.out" 2> "$d/fastbin.err"
grep -Eq 'FASTBIN hits=[1-9][0-9]* fallbacks=[0-9]+' "$d/fastbin.err"
