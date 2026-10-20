#!/usr/bin/env bash
# A transparent Corelib Pos comparison implementation can declare the kernel
# binding used by the bytecode VM. The command must be accepted before VM
# execution can use the binding.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Good.v" <<'EOF'
From Corelib Require Import BinNums PosDef.
Register Pos.compare_cont as kernel.pos_compare_cont.
EOF

cat > "$d/VM.v" <<'EOF'
From Corelib Require Import BinNums PosDef.

Goal Pos.compare_cont Eq (xI (xO xH)) (xO (xO xH)) = Gt.
Proof. vm_compute. reflexivity. Qed.

Goal Pos.eqb (xI (xO xH)) (xI (xO xH)) = true.
Proof. vm_compute. reflexivity. Qed.

Goal Pos.add (xI (xO xH)) (xI xH) = xO (xO (xO xH)).
Proof. vm_compute. reflexivity. Qed.

Goal Pos.succ (xI (xO xH)) = xO (xI xH).
Proof. vm_compute. reflexivity. Qed.

Goal Pos.mul (xI (xO xH)) (xI xH) = xI (xI (xI xH)).
Proof. vm_compute. reflexivity. Qed.
EOF

ROCQ_VM_FASTBIN_STATS=1 rocq c -q -native-compiler no "$d/VM.v" 2> "$d/stderr"
grep -q '^VMPosFun compare_cont hits=[1-9]' "$d/stderr"
grep -q '^VMPosFun eqb hits=[1-9]' "$d/stderr"
grep -q '^VMPosFun add hits=[1-9]' "$d/stderr"
grep -q '^VMPosFun succ hits=[1-9]' "$d/stderr"
grep -q '^VMPosFun mul hits=[1-9]' "$d/stderr"

rocq c -q -native-compiler no "$d/Good.v"

cat > "$d/Arithmetic.v" <<'EOF'
From Corelib Require Import BinNums PosDef.

Register Pos.succ as kernel.pos_succ.
Register Pos.add as kernel.pos_add.
Register Pos.mul as kernel.pos_mul.
EOF

rocq c -q -native-compiler no "$d/Arithmetic.v"
