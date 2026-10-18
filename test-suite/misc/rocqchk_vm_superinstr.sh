#!/usr/bin/env bash
# The fused dispatch paths are semantic-preserving: coqchk must still accept the
# same VM-cast proof and must execute every intended fused successor sequence.
set -eu
export PATH="$BIN:$PATH"
coqlib=()
if [ -n "${ROCQCHK_COQLIB:-}" ]; then
  coqlib=(-coqlib "$ROCQCHK_COQLIB")
fi


d=$(mktemp -d)
# The test harness owns the temporary directory lifetime. Do not recursively
# remove a variable path here: the task's box policy forbids that blast radius.
cat > "$d/SuperInstr.v" <<'EOF'
From Stdlib Require Import ZArith PArith.

Fixpoint descend (n : nat) : positive :=
  match n with
  | 0 => 1%positive
  | S n => (descend n)~1
  end.

Fixpoint compare_many (n : nat) : comparison :=
  match n with
  | 0 => Eq
  | S n => Pos.compare_cont Eq (descend n) (descend (S n))
  end.

Lemma dispatch_vm : compare_many 1000 = Lt.
Proof. vm_compute. reflexivity. Qed.
EOF
rocq c -bytecode-compiler yes -Q "$d" "" "$d/SuperInstr.v"
ROCQ_VM_SUPERINSTR=0 rocqchk "${coqlib[@]}" -bytecode-compiler yes -Q "$d" "" SuperInstr
ROCQ_VM_SUPERINSTR=1 ROCQ_VM_SUPERINSTR_STATS=1 rocqchk "${coqlib[@]}" -bytecode-compiler yes -Q "$d" "" SuperInstr \
  > "$d/stats.out" 2> "$d/stats.err"
for fusion in switch_getfield0 getfield0_push grabrec_grab appterm_grabrec; do
  grep -Eq "SUPERINSTR ${fusion}=[1-9][0-9]*" "$d/stats.err" || {
    cat "$d/stats.err" >&2
    exit 1
  }
done
