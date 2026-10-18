#!/usr/bin/env bash
# The VM's binary-number acceleration is an execution optimization only. This
# test compiles fixed expected results, then makes rocqchk check the same VM
# casts twice: with ROCQ_VM_FASTBIN=0 (bytecode only) and with the default
# (every registered C operation). Their checker reports must be identical
# after removing fast-path diagnostics.
set -eu
PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'find -- "$d" -depth -delete' EXIT

# The oracle is generated independently with Python arbitrary-precision
# integers. Literals use Corelib's postfix constructor notation, so the test
# needs no Stdlib. The corpus includes xH, deep xO and xI chains,
# deterministic random positives, both Z signs, a Corelib-shaped copy of
# Pos.compare_cont with one changed case (it must stay on bytecode), and a
# positive beyond the C fast path's depth limit.
python3 - "$d/FastBin.v" <<'PY'
import random
import sys

out = open(sys.argv[1], "w", encoding="utf-8")
write = out.write
write("From Corelib Require Import PosDef IntDef.\nLocal Open Scope positive_scope.\n\n")

def pos(value):
    return "(1" + "".join("~" + bit for bit in bin(value)[3:]) + ")"

rng = random.Random(0xF457B1)
values = [
    1,
    2,
    3,
    (1 << 63) - 1,
    1 << 63,
    (1 << 64) - 1,
    1 << 64,
    (1 << 64) + 1,
    (1 << 127) - 1,
    1 << 127,
    1 << 128,
    (1 << 128) - 1,
    1 << 256,
    (1 << 257) - 1,
]
values.extend(rng.getrandbits(bits) | (1 << (bits - 1)) | 1 for bits in (5, 37, 65, 129, 257))

for i, value in enumerate(values):
    write(f"Definition p{i} : positive := {pos(value)}.\n")
write("\n")
write("""
Module ShadowPos.
Fixpoint compare_cont (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
  | p~1, q~1 => compare_cont r p q
  | p~1, q~0 => compare_cont Gt p q
  | p~1, 1 => Gt
  | p~0, q~1 => compare_cont Lt p q
  | p~0, q~0 => compare_cont r p q
  | p~0, 1 => Gt
  | 1, q~1 => Gt
  | 1, q~0 => Lt
  | 1, 1 => r
  end.
End ShadowPos.
Definition shadow_compare : ShadowPos.compare_cont Eq 1 1~1 = Gt :=
  ltac:(vm_compute; reflexivity).

""")

def comparison(x, y):
    return "Lt" if x < y else "Gt" if x > y else "Eq"

def z_literal(value):
    if value == 0:
        return "Z0"
    return f"({'Zpos' if value > 0 else 'Zneg'} {pos(abs(value))})"

pairs = [(i, (i * 7 + 3) % len(values)) for i in range(len(values))]
for i, j in pairs:
    x, y = values[i], values[j]
    r = ("Eq", "Lt", "Gt")[i % 3]
    write(f"Definition compare_cont_kernel_{i} : Pos.compare_cont {r} p{i} p{j} = "
          f"{r if x == y else comparison(x, y)} := eq_refl.\n")
    write(f"Definition compare_cont_{i} : Pos.compare_cont {r} p{i} p{j} = "
          f"{r if x == y else comparison(x, y)} := ltac:(vm_compute; reflexivity).\n")
    write(f"Definition eqb_kernel_{i} : Pos.eqb p{i} p{j} = "
          f"{'true' if x == y else 'false'} := eq_refl.\n")
    write(f"Definition eqb_{i} : Pos.eqb p{i} p{j} = "
          f"{'true' if x == y else 'false'} := ltac:(vm_compute; reflexivity).\n")

    zx = x if i % 3 == 0 else -x
    zy = y if i % 2 == 0 else -y
    write(f"Definition zcompare_kernel_{i} : Z.compare {z_literal(zx)} {z_literal(zy)} = "
          f"{comparison(zx, zy)} := eq_refl.\n")
    write(f"Definition zcompare_{i} : Z.compare {z_literal(zx)} {z_literal(zy)} = "
          f"{comparison(zx, zy)} := ltac:(vm_compute; reflexivity).\n")

write("Definition zcompare_zero_kernel : Z.compare Z0 (Zpos p0) = Lt := eq_refl.\n")
write("Definition zcompare_zero : Z.compare Z0 (Zpos p0) = Lt := ltac:(vm_compute; reflexivity).\n")

write(f"Definition p_too_deep : positive := Eval vm_compute in Pos.iter xO 1 {pos(4096)}.\n")
write("Definition eqb_too_deep_kernel : Pos.eqb p_too_deep p_too_deep = true := eq_refl.\n")
write("Definition eqb_too_deep : Pos.eqb p_too_deep p_too_deep = true := ltac:(vm_compute; reflexivity).\n")
out.close()
PY

rocq c -bytecode-compiler yes -Q "$d" "" "$d/FastBin.v"
rocqchk_args=(-bytecode-compiler yes -Q "$d" "")
if [ -n "${ROCQCHK_COQLIB:-}" ]; then
  rocqchk_args=(-coqlib "$ROCQCHK_COQLIB" "${rocqchk_args[@]}")
fi
if ! ROCQ_VM_FASTBIN=0 rocqchk "${rocqchk_args[@]}" FastBin > "$d/bytecode.out" 2> "$d/bytecode.err"; then
  cat "$d/bytecode.err" >&2
  exit 1
fi
if ! ROCQ_VM_FASTBIN_STATS=1 rocqchk "${rocqchk_args[@]}" FastBin \
  > "$d/fastbin.out" 2> "$d/fastbin.err"; then
  cat "$d/fastbin.err" >&2
  exit 1
fi

grep -v '^FASTBIN ' "$d/bytecode.err" > "$d/bytecode.clean.err"
grep -v '^FASTBIN ' "$d/fastbin.err" > "$d/fastbin.clean.err"
diff -u "$d/bytecode.out" "$d/fastbin.out"
diff -u "$d/bytecode.clean.err" "$d/fastbin.clean.err"
for op in 0 1; do
  if ! grep -Eq "^FASTBIN op=$op hits=[1-9][0-9]* fallbacks=[0-9]+$" "$d/fastbin.err"; then
    grep '^FASTBIN ' "$d/fastbin.err" >&2
    exit 1
  fi
done
grep -Eq '^FASTBIN op=1 hits=[1-9][0-9]* fallbacks=[1-9][0-9]*$' "$d/fastbin.err"
