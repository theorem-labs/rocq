#!/usr/bin/env bash
# The routines of the BINNUM family for the conversions between primitive
# 63-bit integers and binary numbers (Uint63Axioms.to_Z_rec and of_pos_rec),
# and for Z.pow. See misc/rocqchk_binnum*.sh for the other routines.
#
# Each lemma states [e = c] where c was computed by cbv, which does not use
# the VM, and is proved by vm_compute, so that rocqchk recomputes e with its
# own bytecode. ROCQ_VM_BINNUM_STATS=1 prints the calls, hits and refusals
# of each routine, and ROCQ_VM_BINNUM_STATS=2 the bodies that bind and the
# near misses:
#  (a) to_Z_rec on nat literals of 0 to 200 nodes and integers from 0 to
#      2^63 - 1, and to_Z; of_pos_rec on nat literals of 0 to 70 nodes and
#      positives of 1 to 200 bits, as literals and as packed results of
#      Pos.add and Pos.mul, and of_pos: one hit each with a 64-bit word,
#      and one refused call each on a 32-bit build, where both routines
#      refuse every call (packed arguments only where packing exists);
#  (b) the stuck terms to_Z_rec (S (S (S x))) 5 and of_pos_rec 2 (xO (xO p)),
#      with x and p free, which the routines must refuse, at each level the
#      bytecode runs;
#  (c) Z.pow on 0, 1, 62, 63, 64 and 200 as exponents of 2, odd powers of a
#      negative base, 0^7, x^0 and a negative exponent, on literal and
#      packed arguments, and with a free base when the exponent is Z0 or
#      Zneg q: one hit each;
#  (d) the bounds of Z.pow: a result of b p = 4096 bits is computed, one of
#      b p > 4096 bits is refused, as are p = 4097 with x = 1 and a base of
#      more than 4096 bits, and a free base with a positive exponent;
#  (e) copies of Z.pow: with Pos.iter at another universe level it binds;
#      with Z.add in Pos.iter's place, or with Pos.iter's xI branch nested
#      differently, it is a near miss; with Pos.iter's type binder in Prop
#      or SProp, over a Z-shaped inductive of that sort, it does not bind;
#  (f) all of these with the statistics off, with ROCQ_VM_BINNUM=-pack and
#      with ROCQ_VM_BINNUM=0.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

python3 - "$d" <<'PY'
import random, sys

d = sys.argv[1]
rng = random.Random(20261030)

def pos(n):
    t = "xH"
    for c in bin(n)[3:]:
        t = "(%s %s)" % ("xI" if c == "1" else "xO", t)
    return t

def z(n): return "Z0" if n == 0 else "(Zpos %s)" % pos(n) if n > 0 else "(Zneg %s)" % pos(-n)

def bits(k):
    return 1 if k == 1 else rng.randrange(1 << (k - 1), 1 << k)

HEADER = """Require Import Corelib.Numbers.Cyclic.Int63.PrimInt63.
Require Import Corelib.Numbers.Cyclic.Int63.Uint63Axioms.
Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef Corelib.Init.Nat.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
"""

def lemma(name, lhs):
    return ("Lemma %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))

counts = {}
def count(key, n=1):
    counts[key] = counts.get(key, 0) + n

# (a) The conversions, one routine call per lemma.
out = [HEADER]
NS = [0, 1, 2, 5, 30, 61, 62, 63, 64, 70, 200]
IS = [0, 1, 2, 5, (1 << 62) - 1, 1 << 62, (1 << 63) - 1, rng.randrange(1 << 63),
      rng.randrange(1 << 40)]
for n in NS:
    for i in IS:
        out.append(lemma("tz%d" % len(out), "to_Z_rec %d%%nat %d%%uint63" % (n, i)))
        count("TZ")
        count("TZ_SITE")
for i in IS:
    out.append(lemma("tz%d" % len(out), "to_Z %d%%uint63" % i))
    count("TZ")
NS2 = [0, 1, 2, 5, 61, 62, 63, 64, 70]
PS = [1, 2, 3, 5, bits(60), bits(62), bits(63), bits(64), bits(100), bits(200)]
for n in NS2:
    for p in PS:
        out.append(lemma("op%d" % len(out), "of_pos_rec %d%%nat %s" % (n, pos(p))))
        count("OP")
        count("OP_SITE")
for p in PS:
    out.append(lemma("op%d" % len(out), "of_pos %s" % pos(p)))
    count("OP")
# Packed results of Pos.add and Pos.mul as the positive.
for _ in range(6):
    a, b = bits(rng.randint(20, 60)), bits(rng.randint(20, 60))
    for n in (5, 63, 70):
        out.append(lemma("oq%d" % len(out), "of_pos_rec %d%%nat (Pos.add %s %s)" % (n, pos(a), pos(b))))
        count("OP")
        count("OP_SITE")
    out.append(lemma("oq%d" % len(out), "of_pos (Pos.mul %s %s)" % (pos(a), pos(b))))
    count("OP")
    out.append(lemma("oq%d" % len(out), "of_pos (xO (xI (Pos.add %s %s)))" % (pos(a), pos(b))))
    count("OP")
open(d + "/Conv.v", "w").write("".join(out))

# (b) Stuck terms. Each side of the equation is evaluated, and the two
# sides differ in syntax only, so that the conversion reads both.
open(d + "/Stuck.v", "w").write(HEADER + """
Lemma sz (x : nat) :
  to_Z_rec (S (S (S x))) 5%uint63 = to_Z_rec (S (S (S x))) (lsr 10%uint63 1%uint63).
Proof. vm_compute. reflexivity. Qed.
Lemma sp (p : positive) : of_pos_rec 2 (xO (xO p)) = of_pos_rec (Nat.add 1 1) (xO (xO p)).
Proof. vm_compute. reflexivity. Qed.
(* Both stuck terms equal a constant for every x and p (5 and 0), but only
   by induction: neither reduces to it, so a VM cast to it must fail. A
   routine that stopped reading early would answer that constant. *)
Fail Definition nz (x : nat) := (@eq_refl Z (Zpos (xI (xO xH))) <:
  to_Z_rec (S (S (S x))) 5%uint63 = Zpos (xI (xO xH))).
Fail Definition nz70 (x : nat) := (@eq_refl Z (Zpos (xI (xO xH))) <:
  to_Z_rec (Nat.add 70 x) 5%uint63 = Zpos (xI (xO xH))).
Fail Definition np (p : positive) := (@eq_refl int 0%uint63 <:
  of_pos_rec 2 (xO (xO p)) = 0%uint63).
""")

# (c) Z.pow, one call per lemma.
out = [HEADER]
for e in (0, 1, 2, 62, 63, 64, 200):
    out.append(lemma("p%d" % len(out), "Z.pow %s %s" % (z(2), z(e))))
    count("POW_HIT")
for x, e in ((-3, 5), (-3, 4), (-2, 63), (-7, 1), (0, 7), (5, 0), (-5, 0), (0, 0),
             (12345, 3), (bits(64), 9), (2, -1), (-3, -5), (bits(100), -1)):
    out.append(lemma("p%d" % len(out), "Z.pow %s %s" % (z(x), z(e))))
    count("POW_HIT")
# A packed base and a packed exponent.
out.append(lemma("p%d" % len(out), "Z.pow (Z.add %s %s) %s" % (z(1), z(2), z(40))))
out.append(lemma("p%d" % len(out), "Z.pow %s (Z.add %s %s)" % (z(-3), z(20), z(21))))
count("POW_HIT", 2)
# A free base, which the bytecode does not read when y is Z0 or Zneg q.
out.append("Lemma pf0 (acc : Z) : Z.pow acc Z0 = Zpos xH.\nProof. vm_compute. reflexivity. Qed.\n")
out.append("Lemma pfn (acc : Z) (q : positive) : Z.pow acc (Zneg q) = Z0.\n"
           "Proof. vm_compute. reflexivity. Qed.\n")
count("POW_HIT", 2)
open(d + "/Pow.v", "w").write("".join(out))

# (d) The bounds: b is the bit length of |x|, and the routine refuses
# b p > 4096, p > 4096, and b > 4096 with p >= 2. Each refused call runs
# Z.pow's bytecode, whose Z.mul calls are routine calls of their own.
out = [HEADER]
for x, e, hit in ((3, 2048, True), (3, 2049, False),          # b = 2
                  ((1 << 63) + 1, 64, True), ((1 << 63) + 1, 65, False),  # b = 64
                  (-((1 << 4095) + 1), 1, True), ((1 << 4096) + 1, 1, False),  # b = 4096, 4097
                  ((1 << 4096) + 1, 2, False),
                  (1, 4096, True), (1, 4097, False), (-1, 4097, False), (0, 4097, False)):
    out.append(lemma("b%d" % len(out), "Z.pow %s %s" % (z(x), z(e))))
    count("BOUND_HIT" if hit else "BOUND_REFUSE")
out.append("Lemma bfree (x : Z) : Z.pow x (Zpos (xO xH)) = Z.mul x (Z.mul x (Zpos xH)).\n"
           "Proof. vm_compute. reflexivity. Qed.\n")
count("BOUND_REFUSE")
open(d + "/Bound.v", "w").write("".join(out))

# (e) Copies of Z.pow.
COPY = """
Definition iter2 {A : Type} (f : A -> A) : A -> positive -> A :=
  fix iter_fix x n := match n with
    | xH => f x
    | xO n1 => iter_fix (iter_fix x n1) n1
    | xI n1 => f (iter_fix (iter_fix x n1) n1)
  end.
Definition pow_pos2 (z : Z) := iter2 (Z.mul z) (Zpos xH).
Definition pow2 (x y : Z) := match y with Zpos p => pow_pos2 x p | Z0 => Zpos xH | Zneg _ => Z0 end.

Definition pow_pos_add (z : Z) := iter2 (Z.add z) (Zpos xH).
Definition pow_add (x y : Z) :=
  match y with Zpos p => pow_pos_add x p | Z0 => Zpos xH | Zneg _ => Z0 end.

Definition iter_bad {A : Type} (f : A -> A) : A -> positive -> A :=
  fix iter_fix x n := match n with
    | xH => f x
    | xO n1 => iter_fix (iter_fix x n1) n1
    | xI n1 => iter_fix (f (iter_fix x n1)) n1
  end.
Definition pow_pos_bad (z : Z) := iter_bad (Z.mul z) (Zpos xH).
Definition pow_bad (x y : Z) :=
  match y with Zpos p => pow_pos_bad x p | Z0 => Zpos xH | Zneg _ => Z0 end.
"""
SORT = """
Inductive Z{s} : {sort} := Z{s}0 | Z{s}pos (p : positive) | Z{s}neg (p : positive).
Definition Z{s}mul (x y : Z{s}) : Z{s} :=
  match x, y with
  | Z{s}0, _ => Z{s}0
  | _, Z{s}0 => Z{s}0
  | Z{s}pos x1, Z{s}pos y1 => Z{s}pos (Pos.mul x1 y1)
  | Z{s}pos x1, Z{s}neg y1 => Z{s}neg (Pos.mul x1 y1)
  | Z{s}neg x1, Z{s}pos y1 => Z{s}neg (Pos.mul x1 y1)
  | Z{s}neg x1, Z{s}neg y1 => Z{s}pos (Pos.mul x1 y1)
  end.
Definition iter{s} {{A : {sort}}} (f : A -> A) : A -> positive -> A :=
  fix iter_fix x n := match n with
    | xH => f x
    | xO n1 => iter_fix (iter_fix x n1) n1
    | xI n1 => f (iter_fix (iter_fix x n1) n1)
  end.
Definition pow_pos{s} (z : Z{s}) := iter{s} (Z{s}mul z) (Z{s}pos xH).
Definition pow{s} (x y : Z{s}) :=
  match y with Z{s}pos p => pow_pos{s} x p | Z{s}0 => Z{s}pos xH | Z{s}neg _ => Z{s}0 end.
"""
out = [HEADER, COPY, SORT.format(s="P", sort="Prop"), SORT.format(s="S", sort="SProp")]
for f in ("pow2", "pow_add", "pow_bad"):
    for x, e in ((3, 5), (-2, 7), (bits(30), 3)):
        out.append(lemma("c%d" % len(out), "%s %s %s" % (f, z(x), z(e))))
count("COPY_HIT", 3)
out.append("Lemma cP : powP (ZPpos (xO xH)) (ZPpos (xI xH)) = ZPpos (xO (xO (xO xH))).\n"
           "Proof. vm_compute. reflexivity. Qed.\n")
# powS cannot be stated as an equation: its type is in SProp, which eq does
# not take, and conversion of SProp terms never runs them. coqc compiles
# every definition, so its statistics show that it does not bind.
open(d + "/Copy.v", "w").write("".join(out))

with open(d + "/counts", "w") as f:
    for k, v in sorted(counts.items()):
        f.write("%s=%d\n" % (k, v))
PY
. "$d/counts"

LIBS="Conv Stuck Pow Bound Copy"
for lib in $LIBS; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

chk() {
  local log=$1 level=$2; shift 2
  ROCQ_VM_BINNUM_STATS=$level rocqchk -silent -bytecode-compiler yes -R "$d" "" "$@" \
    > "$d/$log" 2>&1 || { cat "$d/$log" >&2; fail "rocqchk $* failed"; }
}

# stat LOG ROUTINE FIELD: FIELD of ROUTINE, summed over every process.
stat() {
  awk -v r="$2:" -v f="$3" '$2 == "routine" && $3 == r {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

# total LOG FIELD: FIELD summed over every routine and process.
total() {
  awk -v f="$2" '$2 == "routine" {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

for lib in $LIBS; do chk "$lib.log" 2 -norec "$lib"; done

# field LOG LINE FIELD: the value of FIELD on the line LINE, as printed.
field() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) { print kv[2]; exit } } }' "$d/$1"
}

# What the OCaml that built rocq allows: packing needs a 64-bit word and
# OCaml before 5 (kernel/byterun/rocq_binnum.h), and the routines of the
# uint63 conversions a 64-bit word, without which they refuse every call
# (kernel/byterun/rocq_binnum.c). The packing state that the build prints
# must be the one that the toolchain implies, so that a wrongly
# compiled-out build still fails. Without a readable configuration, the
# build's own state is taken, and the word size of the host.
config=$( { ocamlfind ocamlc -config || ocamlc -config; } 2>/dev/null || true)
word=$(printf '%s\n' "$config" | awk '$1 == "word_size:" { print $2 }')
major=$(printf '%s\n' "$config" | awk '$1 == "version:" { split($2, v, "."); print v[1] }')
packing=$(field Conv.log packed packing)
if [ -n "$word" ] && [ -n "$major" ]; then
  if [ "$word" = 64 ] && [ "$major" -lt 5 ]; then want=on; else want=off; fi
  expect "the packing of results" "$packing" = "$want"
else
  word=$(getconf LONG_BIT)
fi

# (a) One routine call per lemma: at its call site for to_Z_rec and
# of_pos_rec, and at function entry for to_Z and of_pos, whose bodies are the
# partial applications to_Z_rec size and of_pos_rec size. With a 64-bit word
# every call is a hit and reads packed arguments where packing exists. On a
# 32-bit build both routines refuse, and the bytecode then computes the
# value, which the lemma still states.
expect "(a) to_Z_rec site calls" "$(stat Conv.log Uint63.to_Z_rec site-calls)" -eq "$TZ_SITE"
expect "(a) of_pos_rec site calls" "$(stat Conv.log Uint63.of_pos_rec site-calls)" -eq "$OP_SITE"
if [ "$word" = 64 ]; then
  expect "(a) to_Z_rec calls" "$(stat Conv.log Uint63.to_Z_rec calls)" -eq "$TZ"
  expect "(a) to_Z_rec hits" "$(stat Conv.log Uint63.to_Z_rec hits)" -eq "$TZ"
  expect "(a) of_pos_rec calls" "$(stat Conv.log Uint63.of_pos_rec calls)" -eq "$OP"
  expect "(a) of_pos_rec hits" "$(stat Conv.log Uint63.of_pos_rec hits)" -eq "$OP"
  expect "(a) refusals" "$(total Conv.log refusals)" -eq 0
else
  for r in Uint63.to_Z_rec Uint63.of_pos_rec; do
    expect "(a) $r hits on a 32-bit build" "$(stat Conv.log "$r" hits)" -eq 0
  done
  expect "(a) refusals of the other routines" \
    "$(( $(total Conv.log refusals) - $(stat Conv.log Uint63.to_Z_rec refusals) \
         - $(stat Conv.log Uint63.of_pos_rec refusals) ))" -eq 0
fi
if [ "$packing" = on ]; then
  expect "(a) of_pos_rec packed arguments" "$(stat Conv.log Uint63.of_pos_rec args-packed)" -gt 0
  expect "(a) of_pos_rec tail arguments" "$(stat Conv.log Uint63.of_pos_rec args-tail)" -gt 0
else
  expect "(a) packed arguments without packing" "$(total Conv.log args-packed)" -eq 0
  expect "(a) tail arguments without packing" "$(total Conv.log args-tail)" -eq 0
fi

# (b) The stuck terms, on each side of the equation:
#  - the call site runs the routine (BINNUMCALL), which refuses;
#  - then the function runs, and each level where the fixpoint unfolds
#    runs it at function entry (BINNUM), which refuses: for to_Z_rec the
#    levels of S (S (S x)), S (S x) and S x, where the routine reads n to x;
#    for of_pos_rec 2 (xO (xO p)) the levels of 2 and 1, where it reads the
#    positive to p; at the next level the fixpoint does not unfold, because
#    its recursive argument (n = x, or p) is an accumulator;
#  - the two stuck fixpoints are then compared, and the conversion runs
#    each body on fresh variables (Vconv.conv_fix), once more at entry.
# So to_Z_rec refuses 2 (1 + 3 + 1) = 10 calls and of_pos_rec 2 (1 + 2 + 1)
# = 8, and neither has a hit. The bytecode is the same on a 32-bit build,
# where the routines refuse at once, so the counts are too.
expect "(b) to_Z_rec refusals" "$(stat Stuck.log Uint63.to_Z_rec refusals)" -eq 10
expect "(b) to_Z_rec site refusals" "$(stat Stuck.log Uint63.to_Z_rec site-refusals)" -eq 2
expect "(b) to_Z_rec hits" "$(stat Stuck.log Uint63.to_Z_rec hits)" -eq 0
expect "(b) of_pos_rec refusals" "$(stat Stuck.log Uint63.of_pos_rec refusals)" -eq 8
expect "(b) of_pos_rec site refusals" "$(stat Stuck.log Uint63.of_pos_rec site-refusals)" -eq 2
expect "(b) of_pos_rec hits" "$(stat Stuck.log Uint63.of_pos_rec hits)" -eq 0

# (c) Z.pow: one hit per lemma.
expect "(c) Z.pow calls" "$(stat Pow.log Z.pow calls)" -eq "$POW_HIT"
expect "(c) Z.pow hits" "$(stat Pow.log Z.pow hits)" -eq "$POW_HIT"
expect "(c) refusals" "$(total Pow.log refusals)" -eq 0
expect "(c) Z.mul calls" "$(stat Pow.log Z.mul calls)" -eq 0

# (d) The bounds, exactly. A call that the routine refuses at its call
# site runs the function, whose entry runs the routine again, which
# refuses again; a call that it accepts at the site is done.
expect "(d) Z.pow hits" "$(stat Bound.log Z.pow hits)" -eq "$BOUND_HIT"
expect "(d) Z.pow site refusals" "$(stat Bound.log Z.pow site-refusals)" -eq "$BOUND_REFUSE"
expect "(d) Z.pow entry refusals" "$(stat Bound.log Z.pow entry-refusals)" -eq "$BOUND_REFUSE"
expect "(d) Z.pow entry calls" "$(stat Bound.log Z.pow entry-calls)" -eq "$BOUND_REFUSE"

# (e) The copies: pow2 binds as Z.pow; pow_add and pow_bad are near misses
# of Z.pow; powP and powS do not bind, while ZPmul, over the Prop inductive
# ZP, binds as Z.mul.
grep -q "bind Copy.pow2: Z.pow$" "$d/Copy.log" || { cat "$d/Copy.log" >&2; fail "(e) pow2 did not bind"; }
for f in pow_add pow_bad; do
  grep -q "near-miss Copy.$f: Z.pow:" "$d/Copy.log" \
    || { cat "$d/Copy.log" >&2; fail "(e) $f is not a near miss of Z.pow"; }
  ! grep -q "bind Copy.$f:" "$d/Copy.log" || fail "(e) $f bound"
done
for f in powP powS pow_posP pow_posS iterP iterS; do
  ! grep -q "bind Copy.$f:" "$d/Copy.log" || fail "(e) $f bound"
done
grep -q "bind Copy.ZPmul: Z.mul$" "$d/Copy.log" || fail "(e) ZPmul did not bind"
expect "(e) Z.pow hits" "$(stat Copy.log Z.pow hits)" -eq "$COPY_HIT"

# coqc compiles every definition, and so runs the recognizer on powS and
# its callees too, which no conversion of rocqchk runs. powS fails at its
# first binder, which is irrelevant; powP fails at the sort of iterP's type
# binder, in a type annotation, which is not a near miss.
ROCQ_VM_BINNUM_STATS=2 rocq c -native-compiler no -R "$d" "" "$d/Copy.v" > "$d/Copy-coqc.log" 2>&1 \
  || { cat "$d/Copy-coqc.log" >&2; fail "coqc Copy.v failed"; }
grep -q "bind Copy.pow2: Z.pow$" "$d/Copy-coqc.log" || fail "(e) coqc did not bind pow2"
for f in powP powS pow_posP pow_posS iterP iterS; do
  ! grep -q "bind Copy.$f:" "$d/Copy-coqc.log" || fail "(e) coqc bound $f"
done
grep -q "near-miss Copy.powS: Z.pow: binder relevance$" "$d/Copy-coqc.log" \
  || { cat "$d/Copy-coqc.log" >&2; fail "(e) powS is not a near miss of Z.pow on relevance"; }

# (f) The statistics off; no packing; no routine.
for lib in $LIBS; do
  rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" > "$d/$lib-nostats.log" 2>&1 \
    || { cat "$d/$lib-nostats.log" >&2; fail "rocqchk -norec $lib without statistics failed"; }
  ! grep -q "^binnum\[" "$d/$lib-nostats.log" || fail "(f) $lib printed statistics"
  ROCQ_VM_BINNUM=-pack chk "$lib-nopack.log" 1 -norec "$lib"
  expect "(f) $lib -pack packed arguments" "$(total "$lib-nopack.log" args-packed)" -eq 0
  ROCQ_VM_BINNUM=0 chk "$lib-off.log" 1 -norec "$lib"
  expect "(f) $lib off calls" "$(total "$lib-off.log" calls)" -eq 0
done

exit 0
