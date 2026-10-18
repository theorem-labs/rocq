#!/usr/bin/env bash
# The VM's binary-number acceleration is an execution optimization only. This
# test compiles fixed expected results without the fast path, then makes
# rocqchk check the same VM casts with bytecode and with every registered C
# operation. Their checker reports must be identical after removing fast-path
# diagnostics.
set -eu
PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'find -- "$d" -depth -delete' EXIT

# The oracle is generated independently with Python arbitrary-precision
# integers. The corpus includes xH, deep xO and xI chains, deterministic random
# positives, both Z signs, and a positive beyond the C fast path's depth limit.
python3 - "$d/FastBin.v" <<'PY'
import random
import sys

out = open(sys.argv[1], "w", encoding="utf-8")
write = out.write
write("From Stdlib Require Import ZArith NArith PArith.\n\n")

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
    write(f"Definition p{i} := {value}%positive.\n")
write("\n")

def comparison(x, y):
    return "Lt" if x < y else "Gt" if x > y else "Eq"

def z_literal(value):
    return f"({value})%Z"

pairs = [(i, (i * 7 + 3) % len(values)) for i in range(len(values))]
for i, j in pairs:
    x, y = values[i], values[j]
    r = ("Eq", "Lt", "Gt")[i % 3]
    write(f"Definition compare_cont_{i} : Pos.compare_cont {r} p{i} p{j} = "
          f"{r if x == y else comparison(x, y)} := ltac:(vm_compute; reflexivity).\n")
    write(f"Definition eqb_{i} : Pos.eqb p{i} p{j} = "
          f"{'true' if x == y else 'false'} := ltac:(vm_compute; reflexivity).\n")

    zx = x if i % 3 == 0 else -x
    zy = y if i % 2 == 0 else -y
    write(f"Definition zcompare_{i} : Z.compare {z_literal(zx)} {z_literal(zy)} = "
          f"{comparison(zx, zy)} := ltac:(vm_compute; reflexivity).\n")

write("Definition zcompare_zero : Z.compare 0%Z (Zpos p0) = Lt := ltac:(vm_compute; reflexivity).\n")

deep = 1 << 4096
write(f"Definition p_too_deep := {deep}%positive.\n")
write("Definition eqb_too_deep : Pos.eqb p_too_deep p_too_deep = true := ltac:(vm_compute; reflexivity).\n")
out.close()
PY

rocq c -bytecode-compiler yes -Q "$d" "" "$d/FastBin.v"
rocqchk_args=(-bytecode-compiler yes -Q "$d" "")
if [ -n "${ROCQCHK_COQLIB:-}" ]; then
  rocqchk_args=(-coqlib "$ROCQCHK_COQLIB" "${rocqchk_args[@]}")
fi
if ! rocqchk "${rocqchk_args[@]}" FastBin > "$d/bytecode.out" 2> "$d/bytecode.err"; then
  cat "$d/bytecode.err" >&2
  exit 1
fi
if ! ROCQ_VM_FASTBIN=1 ROCQ_VM_FASTBIN_STATS=1 rocqchk "${rocqchk_args[@]}" FastBin \
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
