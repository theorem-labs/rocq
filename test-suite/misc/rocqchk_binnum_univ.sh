#!/usr/bin/env bash
# The packing of literals (Vmvalues.val_of_str_const, kernel/byterun/
# rocq_binnum.h) applies to the VM values of structured constants alone. A
# closed universe instance is a structured constant too, but its value is
# the OCaml value of the instance, which SUBSTINSTANCE and uni_instance read
# as OCaml data; the quality QConstant QProp has the shape of a chain (a
# block of tag 1 and size 1 over Val_int 0), and packing it turned Prop into
# Set. See misc/rocqchk_binnum_literal.sh for the packing of literals.
#
#  (a) true equations on sort-polymorphic and universe-polymorphic
#      definitions at closed instances (Prop, SProp, Type, Set), and one
#      that also holds a number literal, proved by vm_compute in coqc and
#      checked by rocqchk, with all packing on, with ROCQ_VM_BINNUM=-packlit
#      and with ROCQ_VM_BINNUM=0;
#  (b) in coqc, VM casts to the wrong sort fail;
#  (c) a forged library: UL proves qsort@{Prop ; Set} = Set by vm_compute
#      against a UF where it holds, and is then checked against the UF where
#      qsort@{s ; u} is Type@{s ; u}, with its recorded digest patched: only
#      the VM evaluation of the instance tells the two apart, so rocqchk
#      must refuse it, in all three modes.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

cat > "$d/Univ.v" <<'EOF'
Require Import Corelib.BinNums.PosDef.
Set Universe Polymorphism.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
Definition qsort@{s ; u} := Type@{s ; u}.
Definition lsort@{u} := Type@{u}.
Definition qid@{s ; u} (A : Type@{s ; u}) : Type@{s ; u} := A.
Definition pk@{u} (A : Type@{u}) (p : positive) := p.
Lemma tp : qsort@{Prop ; Set} = Prop. Proof. vm_compute. reflexivity. Qed.
Lemma ts : qsort@{SProp ; Set} = SProp. Proof. vm_compute. reflexivity. Qed.
Lemma tt : qsort@{Type ; Set} = Set. Proof. vm_compute. reflexivity. Qed.
Lemma tl : lsort@{Set} = Set. Proof. vm_compute. reflexivity. Qed.
Lemma tc : qsort@{Prop ; Set} = cbv_val (qsort@{Prop ; Set}). Proof. vm_compute. reflexivity. Qed.
Lemma tq : qid@{Prop ; Set} True = True. Proof. vm_compute. reflexivity. Qed.
Lemma tk : pk@{Set} nat (xO (xI xH)) = xO (xI xH). Proof. vm_compute. reflexivity. Qed.
EOF

cat > "$d/UnivBad.v" <<'EOF'
Require Import Univ.
Fail Definition bad0 := (@eq_refl _ Set <: qsort@{Prop ; Set} = Set).
Fail Definition bad1 := (@eq_refl _ Prop <: qsort@{SProp ; Set} = Prop).
Fail Definition bad2 : qsort@{Prop ; Set} = Set := ltac:(vm_compute; reflexivity).
EOF

cat > "$d/UF1.v" <<'EOF'
Set Universe Polymorphism.
Definition qsort@{s ; u} : Type@{u+1} := Type@{u}.
EOF
cat > "$d/UF2.v" <<'EOF'
Set Universe Polymorphism.
Definition qsort@{s ; u} : Type@{u+1} := Type@{s ; u}.
EOF
cat > "$d/UL.v" <<'EOF'
Require Import UF.
Lemma forged : qsort@{Prop ; Set} = Set.
Proof. vm_compute. reflexivity. Qed.
EOF

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# line LOG LINE FIELD: FIELD of the line LINE, summed over every process.
line() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

MODES="on -packlit 0"
mode_env() { [ "$1" = on ] && echo "" || echo "$1"; }

# (a) and (b), in each mode, for coqc and rocqchk.
for m in $MODES; do
  v=$(mode_env "$m")
  for lib in Univ UnivBad; do
    env ${v:+ROCQ_VM_BINNUM=$v} rocq c -native-compiler no -R "$d" "" "$d/$lib.v" \
      > "$d/$lib-coqc-$m.log" 2>&1 || { cat "$d/$lib-coqc-$m.log" >&2; fail "coqc $lib.v ($m) failed"; }
  done
  env ${v:+ROCQ_VM_BINNUM=$v} ROCQ_VM_BINNUM_STATS=1 rocqchk -silent -bytecode-compiler yes \
    -R "$d" "" -norec Univ > "$d/Univ-$m.log" 2>&1 \
    || { cat "$d/Univ-$m.log" >&2; fail "rocqchk Univ ($m) failed"; }
done
# Where literals are packed (64-bit builds with OCaml before 5.0,
# kernel/byterun/rocq_binnum.h), the literal of pk still is: the fix keeps
# the packing of VM values. The state that the build prints must be the
# one that the toolchain implies; without a readable configuration, the
# build's own state is taken.
literals=$(awk '$2 == "packed:" { for (i = 3; i <= NF; i++) { split($i, kv, "=");
    if (kv[1] == "packing-literals") { print kv[2]; exit } } }' "$d/Univ-on.log")
config=$( { ocamlfind ocamlc -config || ocamlc -config; } 2>/dev/null || true)
word=$(printf '%s\n' "$config" | awk '$1 == "word_size:" { print $2 }')
major=$(printf '%s\n' "$config" | awk '$1 == "version:" { split($2, v, "."); print v[1] }')
if [ -z "$word" ] || [ -z "$major" ]; then want=$literals
elif [ "$word" = 64 ] && [ "$major" -lt 5 ]; then want=on
else want=off; fi
[ "$literals" = "$want" ] || fail "the packing of literals is $literals, expected $want"
if [ "$want" = on ]; then
  [ "$(line Univ-on.log packed literals)" -gt 0 ] || fail "(a) no literal packed"
else
  [ "$(line Univ-on.log packed literals)" -eq 0 ] || fail "(a) a literal packed without packing"
fi
[ "$(line Univ--packlit.log packed literals)" -eq 0 ] || fail "(a) -packlit packed a literal"

# (c) The forged library.
cp "$d/UF1.v" "$d/UF.v"
rocq c -native-compiler no -R "$d" "" "$d/UF.v"
rocq c -native-compiler no -R "$d" "" "$d/UL.v"
for m in $MODES; do
  v=$(mode_env "$m")
  env ${v:+ROCQ_VM_BINNUM=$v} rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec UL \
    > "$d/UL-true-$m.log" 2>&1 || { cat "$d/UL-true-$m.log" >&2; fail "(c) rocqchk refused the true UL ($m)"; }
done
cp "$d/UF.vo" "$d/UF1.vo"
cp "$d/UF2.v" "$d/UF.v"
rocq c -native-compiler no -R "$d" "" "$d/UF.v"
python3 - "$d" <<'PY'
import hashlib, sys

d = sys.argv[1]

def segments(data):
    """The segment table of a .vo (lib/objFile.ml): name, position, length,
    and the offset of its 16-byte hash."""
    pos = int.from_bytes(data[8:16], "big")
    n = int.from_bytes(data[pos:pos + 4], "big")
    p, out = pos + 4, []
    for _ in range(n):
        length = int.from_bytes(data[p:p + 4], "big")
        name = data[p + 4:p + 4 + length].decode()
        p += 4 + length
        out.append((name, int.from_bytes(data[p:p + 8], "big"),
                    int.from_bytes(data[p + 8:p + 16], "big"), p + 16))
        p += 32
    return out

def library_digest(data):
    """The MD5 of the library segment, which each dependent records
    (Safe_typing.vodigest)."""
    return next(hashlib.md5(data[p:p + n]).digest()
                for name, p, n, _ in segments(data) if name == "library")

old = library_digest(open(d + "/UF1.vo", "rb").read())
new = library_digest(open(d + "/UF.vo", "rb").read())
data = bytearray(open(d + "/UL.vo", "rb").read())
for name, pos, length, hash_at in segments(bytes(data)):
    if name not in ("summary", "library"):
        continue
    seg = bytes(data[pos:pos + length])
    if seg.count(old) == 0:
        raise SystemExit("the %s segment does not record the digest of UF" % name)
    seg = seg.replace(old, new)
    digest = hashlib.md5(seg).digest()
    data[pos:pos + length] = seg
    data[pos + length:pos + length + 16] = digest
    data[hash_at:hash_at + 16] = digest
open(d + "/UL.vo", "wb").write(bytes(data))
PY
for m in $MODES; do
  v=$(mode_env "$m")
  if env ${v:+ROCQ_VM_BINNUM=$v} rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec UL \
      > "$d/UL-forged-$m.log" 2>&1; then
    cat "$d/UL-forged-$m.log" >&2
    fail "(c) rocqchk accepted the forged UL ($m)"
  fi
  grep -q "Type error" "$d/UL-forged-$m.log" \
    || { cat "$d/UL-forged-$m.log" >&2; fail "(c) rocqchk refused the forged UL for another reason ($m)"; }
done

exit 0
