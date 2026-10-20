#!/usr/bin/env bash
# A transparent Corelib Pos comparison implementation can declare the kernel
# binding used by the bytecode VM. The command must be accepted before VM
# execution can use the binding.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
if [ "${KEEP_TMP:-0}" != 1 ]; then
  trap 'rm -rf "$d"' EXIT
fi

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

ROCQ_VM_FASTBIN=0 rocq c -q -native-compiler no "$d/VM.v"

if ROCQ_VM_FASTBIN=enabled rocq c -q -native-compiler no "$d/VM.v" 2> "$d/invalid-env.err"; then
  echo "FAILURE: invalid ROCQ_VM_FASTBIN value was accepted" >&2
  exit 1
fi
grep -q 'ROCQ_VM_FASTBIN must be 0 or 1, got \\"enabled\\"' "$d/invalid-env.err"

python3 - "$d/GC.v" <<'PY'
import sys

term = "xH"
for _ in range(4096):
    term = f"xI ({term})"

open(sys.argv[1], "w").write(
    "From Corelib Require Import BinNums PosDef.\n"
    f"Definition p : positive := {term}.\n"
    "Goal Pos.add p p = xO p.\n"
    "Proof. vm_compute. reflexivity. Qed.\n"
    "Goal Pos.mul p (xO xH) = xO p.\n"
    "Proof. vm_compute. reflexivity. Qed.\n"
)
PY

OCAMLRUNPARAM=s=4k ROCQ_VM_FASTBIN=1 ROCQ_VM_FASTBIN_STATS=1 \
  rocq c -q -native-compiler no "$d/GC.v" 2> "$d/gc-on.err"
grep -q '^VMPosFun add hits=[1-9]' "$d/gc-on.err"
grep -q '^VMPosFun mul hits=[1-9]' "$d/gc-on.err"
OCAMLRUNPARAM=s=4k ROCQ_VM_FASTBIN=0 \
  rocq c -q -native-compiler no "$d/GC.v"

cat > "$d/Negative.v" <<'EOF'
From Corelib Require Import BinNums PosDef.

Goal Pos.compare (xI xH) (xO xH) = Lt.
Proof.
  vm_cast_no_check (eq_refl Gt).
  Fail Qed.
Abort.
EOF

ROCQ_VM_FASTBIN=1 rocq c -q -native-compiler no "$d/Negative.v"
ROCQ_VM_FASTBIN=0 rocq c -q -native-compiler no "$d/Negative.v"

python3 - "$d/Differential.v" <<'PY'
import random
import sys

header = r'''From Corelib Require Import BinNums PosDef.

Module Ref.
Fixpoint succ x :=
  match x with
  | xI p => xO (succ p)
  | xO p => xI p
  | xH => xO xH
  end.

Fixpoint add x y :=
  match x, y with
  | xI p, xI q => xO (add_carry p q)
  | xI p, xO q => xI (add p q)
  | xI p, xH => xO (succ p)
  | xO p, xI q => xI (add p q)
  | xO p, xO q => xO (add p q)
  | xO p, xH => xI p
  | xH, xI q => xO (succ q)
  | xH, xO q => xI q
  | xH, xH => xO xH
  end
with add_carry x y :=
  match x, y with
  | xI p, xI q => xI (add_carry p q)
  | xI p, xO q => xO (add_carry p q)
  | xI p, xH => xI (succ p)
  | xO p, xI q => xO (add_carry p q)
  | xO p, xO q => xI (add p q)
  | xO p, xH => xO (succ p)
  | xH, xI q => xI (succ q)
  | xH, xO q => xO (succ q)
  | xH, xH => xI xH
  end.

Fixpoint mul x y :=
  match x with
  | xI p => add y (xO (mul p y))
  | xO p => xO (mul p y)
  | xH => y
  end.

Fixpoint compare_cont (r : comparison) (x y : positive) {struct y} :=
  match x, y with
  | xI p, xI q => compare_cont r p q
  | xI p, xO q => compare_cont Gt p q
  | xI _, xH => Gt
  | xO p, xI q => compare_cont Lt p q
  | xO p, xO q => compare_cont r p q
  | xO _, xH => Gt
  | xH, xI _ => Lt
  | xH, xO _ => Lt
  | xH, xH => r
  end.

Fixpoint eqb p q {struct q} :=
  match p, q with
  | xI p, xI q => eqb p q
  | xO p, xO q => eqb p q
  | xH, xH => true
  | _, _ => false
  end.
End Ref.
'''

def pos(value):
    text = "xH"
    for bit in bin(value)[3:]:
        text = f"(xI {text})" if bit == "1" else f"(xO {text})"
    return text

values = [1, 2, 3, 4, 5, 7, 8, 9, (1 << 63) - 1, 1 << 64,
          (1 << 127) + 1, (1 << 257) - 1]
rng = random.Random(0)
values.extend(rng.getrandbits(rng.randrange(1, 258)) | 1 for _ in range(40))

goals = []
for value in values:
    p = pos(value)
    goals.append(f"Goal Pos.succ {p} = Ref.succ {p}. Proof. vm_compute. reflexivity. Qed.")
for left in values:
    for right in values[:8]:
        p, q = pos(left), pos(right)
        goals.extend([
            f"Goal Pos.add {p} {q} = Ref.add {p} {q}. Proof. vm_compute. reflexivity. Qed.",
            f"Goal Pos.mul {p} {q} = Ref.mul {p} {q}. Proof. vm_compute. reflexivity. Qed.",
            f"Goal Pos.eqb {p} {q} = Ref.eqb {p} {q}. Proof. vm_compute. reflexivity. Qed.",
        ])
        for continuation in ("Eq", "Lt", "Gt"):
            goals.append(
                f"Goal Pos.compare_cont {continuation} {p} {q} = "
                f"Ref.compare_cont {continuation} {p} {q}. Proof. vm_compute. reflexivity. Qed."
            )

open(sys.argv[1], "w").write(header + "\n".join(goals) + "\n")
PY

ROCQ_VM_FASTBIN=1 ROCQ_VM_FASTBIN_STATS=1 \
  rocq c -q -native-compiler no "$d/Differential.v" 2> "$d/differential-on.err"
for operation in compare_cont eqb add succ mul; do
  grep -q "^VMPosFun $operation hits=[1-9]" "$d/differential-on.err"
done
ROCQ_VM_FASTBIN=0 rocq c -q -native-compiler no "$d/Differential.v"

rocq c -q -native-compiler no "$d/Good.v"

cat > "$d/Arithmetic.v" <<'EOF'
From Corelib Require Import BinNums PosDef.

Register Pos.succ as kernel.pos_succ.
Register Pos.add as kernel.pos_add.
Register Pos.mul as kernel.pos_mul.
EOF

mkdir "$d/good" "$d/bad" "$d/Forge"

cat > "$d/good/Defs.v" <<'EOF'
Inductive positive : Set :=
xI : forall _ : positive, positive
| xO : forall _ : positive, positive
| xH : positive.
Register positive as kernel.ind_pos.
Inductive bool : Set :=
true : bool
| false : bool.
Register bool as kernel.ind_bool.
Inductive comparison : Set :=
Eq : comparison
| Lt : comparison
| Gt : comparison.
Register comparison as kernel.ind_cmp.

Fixpoint compare_cont (r : comparison) (x y : positive) {struct y} : comparison :=
  match x with
  | xI p =>
    match y with
    | xI q => compare_cont r p q
    | xO q => compare_cont Gt p q
    | xH => Gt
    end
  | xO p =>
    match y with
    | xI q => compare_cont Lt p q
    | xO q => compare_cont r p q
    | xH => Gt
    end
  | xH =>
    match y with
    | xI _ => Lt
    | xO _ => Lt
    | xH => r
    end
  end.
Register compare_cont as kernel.pos_compare_cont.
EOF

python3 - "$d/good/Defs.v" "$d/bad/Defs.v" <<'PY'
import pathlib
import sys

good, bad = map(pathlib.Path, sys.argv[1:])
source = good.read_text()
source = source.replace("Register compare_cont as kernel.pos_compare_cont.\n", "")
source = source.replace(
    "    | xH => Gt\n    end\n  | xO p =>",
    "    | xH => Lt\n    end\n  | xO p =>",
    1,
)
bad.write_text(
    source.replace(
        "  | xH =>\n    match y with\n    | xI _ => Lt",
        "  | xH =>\n    match y with\n    | xI _ => Gt",
        1,
    )
)
PY

mkdir "$d/bad-registered"
cp "$d/bad/Defs.v" "$d/bad-registered/Defs.v"
printf '%s\n' 'Register compare_cont as kernel.pos_compare_cont.' >> "$d/bad-registered/Defs.v"
if rocq c -q -noinit -native-compiler no -Q "$d/bad-registered" Forge "$d/bad-registered/Defs.v" \
    2> "$d/bad-registered.err"; then
  echo "FAILURE: rocq c accepted a mismatched positive-function registration" >&2
  exit 1
fi
grep -q 'Register positive function' "$d/bad-registered.err"

for kind in good bad; do
  rocq c -q -noinit -native-compiler no -Q "$d/$kind" Forge "$d/$kind/Defs.v"
done

root=${ROCQ_SOURCE_ROOT:-$PWD}
while [ ! -f "$root/dune-project" ] && [ "$root" != / ]; do
  root=$(dirname "$root")
done
[ -f "$root/dune-project" ]
"$root/_build/default/test-suite/forge_posfun.exe" \
  "$d/good/Defs.vo" "$d/bad/Defs.vo" "$d/Forge/Defs.vo"

if rocqchk -bytecode-compiler yes -Q "$d/Forge" Forge Forge.Defs 2> "$d/forged.err"; then
  echo "FAILURE: rocqchk accepted a forged positive-function registration" >&2
  exit 1
fi
grep -q 'Register positive function' "$d/forged.err"

rocq c -q -native-compiler no "$d/Arithmetic.v"
