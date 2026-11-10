#!/usr/bin/env bash
# The routines of the BINNUM family return a positive number that they
# compute whole, of 2 to 62 bits, as one packed block (kernel/byterun/
# rocq_binnum.h), which SWITCH and whd_val read as the chain of its number,
# and the routines as its number. See misc/rocqchk_binnum*.sh for the
# routines themselves.
#
# Each lemma states [e = c] where c was computed by cbv, which does not use
# the VM, and is proved by vm_compute (or by a VM cast), so that rocqchk
# recomputes e with its own bytecode. ROCQ_VM_BINNUM_STATS=1 prints, for each
# routine, its positive arguments read as chains, packed blocks and chains
# over a packed tail, and the packed results it made, and the expansions of
# packed blocks by SWITCH and whd_val:
#  (a) bytecode that matches on routine results (a user fix over positive
#      applied to Pos.add a b, and others), for results of 2, 3, 2^62 - 1,
#      2^62, 2^62 + 1 and 200 bits and random ones: one SWITCH expansion per
#      packed result, and none for a result of 63 bits or more;
#  (b) routines on chains over a packed tail (xI (Pos.add a b),
#      xO (xO (Pos.mul a b)), 100 xO over a packed tail) and on mixed packed
#      and chain arguments;
#  (c) the routines that share a suffix of a chain argument, on chains (the
#      suffix stays shared) and on packed arguments (the result is computed
#      whole): the packed results of each, exactly;
#  (d) conversion of a packed result against a chain literal, in both
#      orders, by vm_compute; reflexivity and by a VM cast: one whd_val
#      expansion each; and, in coqc, casts to a wrong literal fail;
#  (e) a packed value matched 50 times: 50 SWITCH expansions;
#  (f) all of these with a minor heap of 4096 words, with the statistics
#      off, with ROCQ_VM_BINNUM=-pack (no packed value at all) and with
#      ROCQ_VM_BINNUM=0;
#  (g) the packing of literals on: the same calls and refusals. The models
#      of (a) to (f) count chain literals, so those checks run with
#      ROCQ_VM_BINNUM=-packlit.
# Review.v and Refuse.v reach the branches named in the review of slice 4:
# packed rests with an accumulated comparison, read_pos going to limbs in
# its first loop, refused calls next to a packed argument, and two packed
# blocks of one number compared. Where packing is compiled out (a 32-bit
# build, or OCaml 5 and later), the lemmas still hold and every packed count
# is 0; the state that the toolchain implies is checked first.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

python3 - "$d" <<'PY'
import random, sys

d = sys.argv[1]
rng = random.Random(20261027)
LIMIT = 1 << 62

def bits(k):
    return 1 if k == 1 else rng.randrange(1 << (k - 1), 1 << k)

def pos(n):
    t = "xH"
    for c in bin(n)[3:]:
        t = "(%s %s)" % ("xI" if c == "1" else "xO", t)
    return t

def z(n): return "Z0" if n == 0 else "(Zpos %s)" % pos(n) if n > 0 else "(Zneg %s)" % pos(-n)
def packed(n): return 2 <= n < LIMIT

def is_pow2(v): return v & (v - 1) == 0

def padd(v):
    """An expression whose value v >= 2 a routine computes whole (a sum that
    keeps a suffix of a chain argument would share it): Pos.succ of 2^k - 1
    for a power of two, Pos.mul v 1 otherwise."""
    return "(Pos.succ %s)" % pos(v - 1) if is_pow2(v) else "(Pos.mul %s xH)" % pos(v)

HEADER = """Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
Fixpoint walk (p : positive) : positive :=
  match p with xI q => xI (walk q) | xO q => xO (walk q) | xH => xH end.
Fixpoint bits (p : positive) : list bool :=
  match p with xI q => cons true (bits q) | xO q => cons false (bits q) | xH => nil end.
Definition zwalk (x : Z) : Z :=
  match x with Z0 => Z0 | Zpos p => Zpos (walk p) | Zneg p => Zneg (walk p) end.
Fixpoint xo (n : nat) (p : positive) : positive :=
  match n with O => p | S n => xO (xo n p) end.
Fixpoint xi (n : nat) (p : positive) : positive :=
  match n with O => p | S n => xI (xi n p) end.
"""

def lemma(name, lhs):
    return ("Lemma %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))

counts = {}
def count(key, n=1):
    counts[key] = counts.get(key, 0) + n

EDGE = [2, 3, 4, 5, 7, LIMIT - 1, LIMIT, LIMIT + 1, bits(200), bits(61), bits(62), bits(63)]

# (a) Matches on routine results. One SWITCH expansion per packed result
# that walk, bits or zwalk matches; a chain result (63 bits or more) has
# none.
out = [HEADER]
def expand(v):
    if packed(v):
        count("A_EXP")
        count("A_NODES", v.bit_length() - 1)
for v in EDGE + [bits(rng.randint(2, 62)) for _ in range(20)]:
    out.append(lemma("w%d" % len(out), "walk %s" % padd(v)))
    expand(v)
    out.append(lemma("b%d" % len(out), "bits %s" % padd(v)))
    expand(v)
    out.append(lemma("z%d" % len(out), "zwalk (Z.pos_sub xH %s)" % pos(v + 1)))
    expand(v)
for _ in range(10):
    a, b = bits(rng.randint(1, 40)), bits(rng.randint(1, 40))
    # Pos.mul shares b below the xO nodes when a is a power of two.
    whole = a & (a - 1) != 0
    out.append(lemma("m%d" % len(out), "walk (Pos.mul %s %s)" % (pos(a), pos(b))))
    if whole: expand(a * b)
    out.append(lemma("zm%d" % len(out), "zwalk (Z.mul (Zneg %s) (Zpos %s))" % (pos(a), pos(b))))
    if whole: expand(a * b)
for k in (1, 2, 3, 100, 1000):
    out.append(lemma("n%d" % len(out), "walk (Pos.of_succ_nat %d%%nat)" % k))
    expand(k + 1)
    out.append(lemma("zn%d" % len(out), "zwalk (Z.of_nat %d%%nat)" % k))
    expand(k)
for k in (1, 2, 5, 61, 62, 63):
    v = (1 << k) - 1
    out.append(lemma("s%d" % len(out), "walk (Pos.succ %s)" % pos(v)))
    expand(v + 1)
for _ in range(8):
    a, b = bits(rng.randint(2, 120)), bits(rng.randint(1, 60))
    q, r = divmod(a, b)
    out.append(lemma("dv%d" % len(out),
                     "let (q, r) := Z.pos_div_eucl %s (Zpos %s) in (zwalk q, zwalk r)" % (pos(a), pos(b))))
    expand(q)
    expand(r)
open(d + "/Match.v", "w").write("".join(out))

# (b) Chains over a packed tail, and mixed arguments. P and Q are packed
# results, C a chain literal.
out = [HEADER]
for i in range(6):
    u, w, c = bits(rng.randint(20, 58)), bits(rng.randint(20, 58)), bits(rng.randint(1, 80))
    P, Q, C = padd(u), padd(w), pos(c)
    for lhs in (
            # one or two chain nodes over a packed tail
            "Pos.add (xI %s) %s" % (P, C), "Pos.add %s (xI %s)" % (C, P),
            "Pos.add_carry (xO %s) (xI %s)" % (P, Q),
            "Pos.mul (xO (xO (Pos.mul %s %s))) %s" % (pos(u), pos(w), C),
            "Pos.mul %s (xI %s)" % (C, P),
            "Pos.compare (xI %s) (xI %s)" % (P, Q), "Pos.compare (xO %s) (xO %s)" % (P, P),
            "Pos.eqb (xI %s) (xI %s)" % (P, P), "Pos.eqb (xI %s) (xO %s)" % (P, P),
            "Z.pos_sub (xI %s) %s" % (P, C), "Z.pos_sub (xO %s) (xO %s)" % (P, Q),
            "Z.pos_div_eucl (xO %s) (Zpos %s)" % (P, C),
            "Z.pos_div_eucl %s (Zpos (xI %s))" % (C, P),
            "Pos.succ (xi 3 %s)" % P, "Pos.pred_double (xo 3 %s)" % P,
            "Pos.div2 (xO %s)" % P, "Z.div2 (Zneg (xI %s))" % P,
            "Z.compare (Zpos (xI %s)) (Zpos (xI %s))" % (P, Q),
            "Z.eqb (Zneg (xO %s)) (Zneg (xO %s))" % (P, P),
            # more than 64 chain nodes over a packed tail
            "Pos.add (xo 100 %s) %s" % (P, C), "Pos.add (xo 100 %s) (xo 100 %s)" % (P, Q),
            "Pos.mul (xo 100 %s) %s" % (P, C), "Pos.mul %s (xo 100 %s)" % (pos(3), P),
            "Pos.compare (xo 100 %s) (xo 100 %s)" % (P, Q),
            "Pos.eqb (xo 100 %s) (xo 100 %s)" % (P, P),
            "Z.pos_sub (xo 100 %s) (xo 99 %s)" % (P, Q),
            "Z.pos_div_eucl (xo 100 %s) (Zpos %s)" % (P, C),
            "Z.pos_div_eucl (xo 100 %s) (Zpos (xo 70 %s))" % (P, Q),
            "Pos.succ (xi 70 %s)" % P, "Pos.pred_double (xo 70 %s)" % P,
            # mixed packed and chain arguments
            "Pos.add %s %s" % (P, C), "Pos.add %s %s" % (C, P), "Pos.add %s %s" % (P, Q),
            "Pos.compare %s %s" % (P, pos(u)), "Pos.compare %s %s" % (pos(u), P),
            "Pos.compare %s %s" % (P, C), "Pos.eqb %s %s" % (P, pos(u)),
            "Pos.eqb %s %s" % (pos(u), P), "Pos.eqb %s %s" % (P, Q),
            "Pos.mul %s %s" % (P, C), "Pos.mul %s %s" % (P, Q),
            "Z.pos_sub %s %s" % (P, C), "Z.pos_sub %s %s" % (P, pos(u)),
            "Z.pos_div_eucl %s (Zpos %s)" % (P, Q),
            "Z.add (Zpos %s) (Zneg %s)" % (P, C), "Z.add (Zneg %s) (Zneg %s)" % (P, Q),
            "Z.mul (Zneg %s) (Zpos %s)" % (P, C),
            "Z.eqb (Zpos %s) (Zpos %s)" % (P, pos(u)), "Z.leb (Zpos %s) (Zpos %s)" % (P, C),
            "Z.ltb (Zneg %s) (Zneg %s)" % (P, Q)):
        out.append(lemma("t%d" % len(out), lhs))
open(d + "/Tail.v", "w").write("".join(out))

# (c) The sharing routines, on chain literals and on packed arguments. The
# packed results of each routine, modelled exactly: on a chain, a result
# that keeps a suffix of the argument is shared, and one that does not is
# computed whole; on a packed argument the result is computed whole. A
# whole result of 2 to 62 bits is packed.
out = [HEADER]
def res(r, v):
    if packed(v):
        count("C_" + r.replace(".", "_"))

def all_ones(v): return v & (v + 1) == 0
def power2(v): return v & (v - 1) == 0

CHAINS = [1, 2, 3, 6, 7, 8, 15, 16, 21, (1 << 61) - 1, (1 << 61), (1 << 62) - 1, 1 << 62,
          bits(30), bits(62), bits(70)]
PACKS = [2, 3, 6, 7, 8, (1 << 61) - 1, (1 << 61) + 1, (1 << 62) - 1, bits(30), bits(61)]
for v in CHAINS:
    c = pos(v)
    out.append(lemma("cs%d" % len(out), "Pos.succ %s" % c))
    if all_ones(v): res("Pos.succ", v + 1)
    out.append(lemma("cp%d" % len(out), "Pos.pred_double %s" % c))
    if power2(v): res("Pos.pred_double", 2 * v - 1)
    out.append(lemma("cd%d" % len(out), "Pos.div2 %s" % c))
    out.append(lemma("czd%d" % len(out), "Z.double (Zpos %s)" % c))
    out.append(lemma("czs%d" % len(out), "Z.succ_double (Zpos %s)" % c))
    out.append(lemma("czsn%d" % len(out), "Z.succ_double (Zneg %s)" % c))
    if power2(v): res("Z.succ_double", 2 * v - 1)
    out.append(lemma("czp%d" % len(out), "Z.pred_double (Zneg %s)" % c))
    out.append(lemma("czpp%d" % len(out), "Z.pred_double (Zpos %s)" % c))
    if power2(v): res("Z.pred_double", 2 * v - 1)
    out.append(lemma("czv%d" % len(out), "Z.div2 (Zpos %s)" % c))
    out.append(lemma("czvn%d" % len(out), "Z.div2 (Zneg %s)" % c))
    if v & 1 and v > 1 and all_ones(v >> 1): res("Z.div2", (v >> 1) + 1)
for v in PACKS:
    p = padd(v)
    # padd(v) is itself Pos.succ (v - 1), a packed result, for a power of
    # two; it is evaluated once in each of the 10 lemmas below.
    if is_pow2(v):
        for _ in range(10): res("Pos.succ", v)
    out.append(lemma("ps%d" % len(out), "Pos.succ %s" % p))
    res("Pos.succ", v + 1)
    out.append(lemma("pp%d" % len(out), "Pos.pred_double %s" % p))
    res("Pos.pred_double", 2 * v - 1)
    out.append(lemma("pd%d" % len(out), "Pos.div2 %s" % p))
    res("Pos.div2", v >> 1)
    out.append(lemma("pzd%d" % len(out), "Z.double (Zpos %s)" % p))
    res("Z.double", 2 * v)
    out.append(lemma("pzs%d" % len(out), "Z.succ_double (Zpos %s)" % p))
    res("Z.succ_double", 2 * v + 1)
    out.append(lemma("pzsn%d" % len(out), "Z.succ_double (Zneg %s)" % p))
    res("Z.succ_double", 2 * v - 1)
    out.append(lemma("pzp%d" % len(out), "Z.pred_double (Zneg %s)" % p))
    res("Z.pred_double", 2 * v + 1)
    out.append(lemma("pzpp%d" % len(out), "Z.pred_double (Zpos %s)" % p))
    res("Z.pred_double", 2 * v - 1)
    out.append(lemma("pzv%d" % len(out), "Z.div2 (Zpos %s)" % p))
    res("Z.div2", v >> 1)
    out.append(lemma("pzvn%d" % len(out), "Z.div2 (Zneg %s)" % p))
    res("Z.div2", (v + 1) >> 1)
    count("C_PACKS", 10)
open(d + "/Share.v", "w").write("".join(out))

# (d) Conversion of a packed result against a chain literal, in both orders,
# by vm_compute; reflexivity and by a VM cast (vm_cast_no_check in a proof,
# and <: in a definition). Each conversion reads the packed value once
# through whd_val. In coqc, casts to a wrong literal fail.
out = [HEADER]
bad = [HEADER]
for v in [2, 3, 5, LIMIT - 1, LIMIT + 1, bits(40), bits(62), bits(100)]:
    e, c = padd(v), pos(v)
    ze, zc = "(Z.add (Zneg %s) (Zneg %s))" % (pos(v), pos(v)), z(-2 * v)
    for lhs, rhs, ty, pk in ((e, c, "positive", packed(v)), (ze, zc, "Z", packed(2 * v))):
        i = len(out)
        out.append("Lemma cv%d : %s = %s.\nProof. vm_compute. reflexivity. Qed.\n" % (i, lhs, rhs))
        out.append("Lemma cw%d : %s = %s.\nProof. vm_compute. reflexivity. Qed.\n" % (i, rhs, lhs))
        out.append("Lemma cx%d : %s = %s.\nProof. vm_cast_no_check (@eq_refl %s %s). Qed.\n"
                   % (i, lhs, rhs, ty, rhs))
        out.append("Lemma cy%d : %s = %s.\nProof. vm_cast_no_check (@eq_refl %s %s). Qed.\n"
                   % (i, rhs, lhs, ty, rhs))
        out.append("Definition cz%d := (@eq_refl %s %s <: %s = %s).\n" % (i, ty, rhs, lhs, rhs))
        if pk: count("D_WHD", 5)
        wrong = pos(v + 1) if ty == "positive" else z(-2 * v - 2)
        bad.append("Fail Check (@eq_refl %s %s <: %s = %s).\n" % (ty, wrong, lhs, wrong))
        bad.append("Fail Check (@eq_refl %s %s <: %s = %s).\n" % (ty, wrong, wrong, lhs))
open(d + "/Conv.v", "w").write("".join(out))
open(d + "/ConvBad.v", "w").write("".join(bad))

# (e) A packed value matched 50 times: each match expands it.
out = [HEADER, """
Fixpoint rep (n : nat) (p : positive) (acc : nat) : nat :=
  match n with
  | O => acc
  | S n => rep n p (match p with xI _ => S acc | _ => acc end)
  end.
"""]
for v in (5, 6, bits(40), LIMIT - 1):
    out.append(lemma("r%d" % len(out), "rep 50 %s O" % padd(v)))
    count("E_EXP", 50)
    count("E_NODES", 50 * (v.bit_length() - 1))
open(d + "/Many.v", "w").write("".join(out))

# Branches that the libraries above do not reach (review notes of slice 4):
#  (a) Pos.compare_cont with an accumulated r other than Eq when both rests
#      are packed and equal, P2 being a second packed block of P's number;
#  (b) read_pos on a chain of 3 to 63 nodes over a packed tail, of more than
#      64 bits in all, which goes to limbs in its first loop;
#  (d) the conversion of two distinct packed blocks of the same number.
out = [HEADER]
for _ in range(4):
    u = bits(rng.randint(20, 58))
    P, P2 = padd(u), padd(u)
    for lhs in ("Pos.compare_cont Lt %s %s" % (P, P2), "Pos.compare_cont Gt %s %s" % (P, P2),
                "Pos.compare (xI %s) (xO %s)" % (P, P2), "Pos.compare (xO %s) (xI %s)" % (P, P2)):
        out.append(lemma("na%d" % len(out), lhs))
P62, P60, C = padd(bits(62)), padd(bits(60)), pos(bits(rng.randint(2, 80)))
for lhs in ("Pos.mul (xo 10 %s) %s" % (P62, C), "Pos.mul (xo 40 %s) %s" % (P62, C),
            "Z.pos_sub (xo 40 %s) %s" % (P60, C), "Z.pos_sub %s (xo 40 %s)" % (C, P60)):
    out.append(lemma("nb%d" % len(out), lhs))
for _ in range(4):
    a, b = bits(rng.randint(2, 30)), bits(rng.randint(2, 30))
    out.append("Lemma nd%d : Pos.mul %s %s = Pos.mul %s %s.\n"
               "Proof. vm_cast_no_check (@eq_refl positive (Pos.mul %s %s)). Qed.\n"
               % (len(out), pos(a), pos(b), pos(b), pos(a), pos(a), pos(b)))
open(d + "/Review.v", "w").write("".join(out))

#  (c) Refused calls whose other argument is packed: p is free, and P a
#      packed result of 8 to 12 bits.
out = [HEADER]
for _ in range(3):
    P = padd(bits(rng.randint(8, 12)))
    for lhs in ("Pos.add_carry (xI p) %s" % P, "Pos.compare_cont Gt (xO p) %s" % P,
                "Z.add (Zneg (xI p)) (Zneg %s)" % P):
        out.append("Lemma nc%d (p : positive) : %s = cbv_val (%s).\n"
                   "Proof. vm_compute. reflexivity. Qed.\n" % (len(out), lhs, lhs))
open(d + "/Refuse.v", "w").write("".join(out))

with open(d + "/counts", "w") as f:
    for k, v in sorted(counts.items()):
        f.write("%s=%d\n" % (k, v))
PY
. "$d/counts"

LIBS="Match Tail Share Conv Many Review"
for lib in $LIBS ConvBad Refuse; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# chk LOG ARGS...: rocqchk with the counters on; its output goes to LOG.
# The models below count chain literals, which slice 5 packs as well (see
# rocqchk_binnum_literal.sh): ROCQ_VM_BINNUM defaults to -packlit here, and
# (g) checks the same calls with the packing of literals on.
chk() {
  local log=$1; shift
  ROCQ_VM_BINNUM=${ROCQ_VM_BINNUM--packlit} ROCQ_VM_BINNUM_STATS=1 \
    rocqchk -silent -bytecode-compiler yes -R "$d" "" "$@" \
    > "$d/$log" 2>&1 || { cat "$d/$log" >&2; fail "rocqchk $* failed"; }
}

# field LOG LINE FIELD: the value of FIELD on the line LINE, as printed.
field() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) { print kv[2]; exit } } }' "$d/$1"
}

# stat LOG ROUTINE FIELD: FIELD of ROUTINE, summed over every process.
stat() {
  awk -v r="$2:" -v f="$3" '$2 == "routine" && $3 == r {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

# line LOG LINE FIELD: FIELD of the line LINE ("packed", "recognizer"),
# summed over every process.
line() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
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

SHARING="Pos.succ Pos.pred_double Pos.div2 Z.double Z.succ_double Z.pred_double Z.div2"

for lib in $LIBS Refuse; do chk "$lib.log" -norec "$lib"; done
for lib in $LIBS; do
  expect "$lib refusals" "$(total "$lib.log" refusals)" -eq 0
done

# The state of packing, which is compiled out on a 32-bit build and with
# OCaml 5 or later (kernel/byterun/rocq_binnum.h). The expected state is
# read from the toolchain, so that a wrongly compiled-out build still fails.
packing=$(field Match.log packed packing)
config=$( { ocamlfind ocamlc -config || ocamlc -config; } 2>/dev/null || true)
word=$(printf '%s\n' "$config" | awk '$1 == "word_size:" { print $2 }')
major=$(printf '%s\n' "$config" | awk '$1 == "version:" { split($2, v, "."); print v[1] }')
if [ -z "$word" ] || [ -z "$major" ]; then want=$packing
elif [ "$word" = 64 ] && [ "$major" -lt 5 ]; then want=on
else want=off; fi
expect "the packing of results" "$packing" = "$want"

# (c) of the review notes: refused calls next to a packed argument, which
# the routine read before it met p. Packing or not, the calls are refused.
for r in Pos.add_carry Pos.compare_cont Z.add; do
  expect "(n1c) $r refusals" "$(stat Refuse.log "$r" refusals)" -gt 0
done

if [ "$want" = on ]; then
for lib in $LIBS; do
  expect "$lib packed results" "$(total "$lib.log" packed-results)" -gt 0
done

# (a) One SWITCH expansion per packed result matched, with its nodes; no
# whd_val expansion, since the values that conversion reads are the chains
# that walk, bits and zwalk build.
expect "(a) switch expansions" "$(line Match.log packed switch-expansions)" -eq "$A_EXP"
expect "(a) switch nodes" "$(line Match.log packed switch-nodes)" -eq "$A_NODES"
expect "(a) whd expansions" "$(line Match.log packed whd-expansions)" -eq 0

# (b) Chains over a packed tail were read, by each kind of routine.
for r in Pos.add Pos.add_carry Pos.mul Pos.compare_cont Pos.eqb Z.pos_sub Z.pos_div_eucl \
         Pos.succ Pos.pred_double Z.compare Z.eqb; do
  expect "(b) $r args-tail" "$(stat Tail.log "$r" args-tail)" -gt 0
done
for r in Pos.add Pos.mul Pos.compare_cont Pos.eqb Z.pos_sub Z.pos_div_eucl; do
  expect "(b) $r args-packed" "$(stat Tail.log "$r" args-packed)" -gt 0
done
# A routine reads a Z from its node, so the packed positive of Zpos P is a
# packed tail one node down.
for r in Z.add Z.mul; do
  expect "(b) $r args-tail" "$(stat Tail.log "$r" args-tail)" -gt 0
done

# (c) The sharing routines: packed results exactly as modelled; each packed
# argument is read as one: as a packed argument of the Pos routines, and as
# a packed tail of the Z routines, which read the Zpos or Zneg node above it.
for r in $SHARING; do
  k="C_$(echo "$r" | tr . _)"
  expect "(c) $r packed results" "$(stat Share.log "$r" packed-results)" -eq "${!k:-0}"
done
expect "(c) packed arguments of the sharing routines" \
  "$(for r in $SHARING; do stat Share.log "$r" args-packed; stat Share.log "$r" args-tail; done \
     | awk '{ s += $1 } END { print s }')" \
  -eq "$C_PACKS"

# (d) One whd_val expansion per conversion of a packed value.
expect "(d) whd expansions" "$(line Conv.log packed whd-expansions)" -eq "$D_WHD"

# (e) 50 expansions per lemma, each building the whole chain.
expect "(e) switch expansions" "$(line Many.log packed switch-expansions)" -eq "$E_EXP"
expect "(e) switch nodes" "$(line Many.log packed switch-nodes)" -eq "$E_NODES"

# The review notes: (a) packed rests on both sides of compare_cont; (b)
# chains over a packed tail of more than 64 bits; (c) a packed argument
# read before a refusal; (d) two packed blocks of one number compared.
expect "(n1a) Pos.compare_cont args-packed" "$(stat Review.log Pos.compare_cont args-packed)" -gt 0
expect "(n1a) Pos.compare_cont args-tail" "$(stat Review.log Pos.compare_cont args-tail)" -gt 0
for r in Pos.mul Z.pos_sub; do
  expect "(n1b) $r args-tail" "$(stat Review.log "$r" args-tail)" -gt 0
done
for r in Pos.add_carry Pos.compare_cont; do
  expect "(n1c) $r args-packed" "$(stat Refuse.log "$r" args-packed)" -gt 0
done
expect "(n1c) Z.add args-tail" "$(stat Refuse.log Z.add args-tail)" -gt 0
expect "(n1d) whd expansions" "$(line Review.log packed whd-expansions)" -ge 8
else
# Packing is compiled out: the lemmas above still hold, and no value is
# packed or expanded.
for lib in $LIBS Refuse; do
  expect "$lib packed results" "$(total "$lib.log" packed-results)" -eq 0
  expect "$lib packed arguments" "$(total "$lib.log" args-packed)" -eq 0
  expect "$lib switch expansions" "$(line "$lib.log" packed switch-expansions)" -eq 0
  expect "$lib whd expansions" "$(line "$lib.log" packed whd-expansions)" -eq 0
done
fi

# (f) A minor heap of 4096 words; the statistics off; no packing; no
# routine.
for lib in $LIBS; do
  OCAMLRUNPARAM=s=4096 chk "$lib-small.log" -norec "$lib"
  expect "(f) $lib small heap refusals" "$(total "$lib-small.log" refusals)" -eq 0
  rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" > "$d/$lib-nostats.log" 2>&1 \
    || { cat "$d/$lib-nostats.log" >&2; fail "rocqchk -norec $lib without statistics failed"; }
  ! grep -q "^binnum\[" "$d/$lib-nostats.log" || fail "(f) $lib printed statistics"
  ROCQ_VM_BINNUM=-pack chk "$lib-nopack.log" -norec "$lib"
  expect "(f) $lib -pack packed results" "$(total "$lib-nopack.log" packed-results)" -eq 0
  expect "(f) $lib -pack packed arguments" "$(total "$lib-nopack.log" args-packed)" -eq 0
  expect "(f) $lib -pack switch expansions" "$(line "$lib-nopack.log" packed switch-expansions)" -eq 0
  expect "(f) $lib -pack whd expansions" "$(line "$lib-nopack.log" packed whd-expansions)" -eq 0
  expect "(f) $lib -pack refusals" "$(total "$lib-nopack.log" refusals)" -eq 0
  ROCQ_VM_BINNUM=0 chk "$lib-off.log" -norec "$lib"
  expect "(f) $lib off calls" "$(total "$lib-off.log" calls)" -eq 0
done

# (g) The packing of literals on, as by default: no routine makes or
# refuses another call.
per_routine() {
  awk -v f="$2" '$2 == "routine" {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s[$3] += kv[2] } }
    END { for (r in s) print r, s[r] }' "$d/$1" | sort
}
for lib in $LIBS Refuse; do
  ROCQ_VM_BINNUM_STATS=1 rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" \
    > "$d/$lib-lit.log" 2>&1 || { cat "$d/$lib-lit.log" >&2; fail "(g) rocqchk -norec $lib failed"; }
  for f in entry-calls entry-refusals site-calls site-refusals; do
    [ "$(per_routine "$lib.log" $f)" = "$(per_routine "$lib-lit.log" $f)" ] \
      || fail "(g) $lib: the $f of the routines change with the packing of literals"
  done
done

exit 0
