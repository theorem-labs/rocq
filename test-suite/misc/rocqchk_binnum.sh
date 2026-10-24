#!/usr/bin/env bash
# rocqchk runs Pos.compare_cont and Pos.eqb as C routines (the BINNUM
# instruction, kernel/vmbinnum.ml and kernel/byterun/rocq_binnum.c) when it
# recognizes their bodies, and runs the bytecode for every other body and for
# every input that the routine refuses.
#
# Each lemma below states [f a b = c] where c was computed by cbv, which does
# not use the VM, and is proved by vm_compute, so that rocqchk recomputes
# [f a b] with its own bytecode. The counters that ROCQ_VM_BINNUM_STATS=1
# prints at the exit of every process show which code ran:
#  (a) the Corelib functions, with random and edge inputs: one routine call
#      per lemma, every call a hit;
#  (b) the same with ROCQ_VM_BINNUM=0: nothing is bound and no routine runs;
#      -Pos.eqb turns off only that routine; a bad value stops rocqchk;
#  (c) copies over a user inductive of the same shape (and a copy of the
#      Stdlib body over Corelib's types) bind, and their results are right;
#  (d) a copy with one branch changed, and a copy over an inductive with its
#      constructors in another order, do not bind, and their own results
#      still check;
#  (e) inputs with a free variable: the routine refuses them and the bytecode
#      computes; a partial application gets its last argument later and hits;
#  (f) the -j 2 run of (a): each worker prints its own counters.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS

d=$(mktemp -d)

python3 - "$d" <<'PY'
import random, sys

d = sys.argv[1]
rng = random.Random(20261024)

def bits(k):
    """A random number of exactly k bits."""
    return 1 if k == 1 else rng.randrange(1 << (k - 1), 1 << k)

def pos(n):
    """Corelib positive, most significant bit first: (1~0~1) is 5."""
    b = bin(n)[2:]
    return "(1" + "".join("~" + c for c in b[1:]) + ")"

def upos(n):
    """The same number in the user inductive pos of Copy.v."""
    t = "pH"
    for c in bin(n)[3:]:
        t = ("(pI %s)" if c == "1" else "(pO %s)") % t
    return t

def opos(n):
    """The same number in the reordered inductive opos of Bad.v."""
    t = "oH"
    for c in bin(n)[3:]:
        t = ("(oI %s)" if c == "1" else "(oO %s)") % t
    return t

def compare_pairs(nrandom):
    p = [(1, 1), (1, 2), (2, 1), (1, 3), (3, 1)]
    for k in (1, 63, 64, 65, 200):
        a = bits(k)
        p += [(a, a), ((1 << k) - 1, (1 << k) - 1), (1 << (k - 1), 1 << (k - 1))]
        if k > 1:
            p += [(a, a ^ 1), (a ^ (1 << (k - 2)), a), ((1 << k) - 1, 1 << (k - 1))]
    p += [(bits(63), bits(64)), (bits(64), bits(63)), (bits(64), bits(65)),
          (bits(65), bits(64)), (bits(200), bits(199)), (bits(199), bits(200)),
          ((1 << 64) - 1, 1 << 64), (1 << 64, (1 << 64) - 1),
          (1, bits(200)), (bits(200), 1)]
    for i in range(nrandom):
        ka = rng.randint(1, 200)
        kb = ka if i % 2 == 0 else rng.randint(1, 200)
        p.append((bits(ka), bits(kb)))
    return p

def flip(a):
    k = a.bit_length()
    return 2 if k == 1 else a ^ (1 << rng.randrange(k - 1))

def eqb_pairs(nrandom):
    p = [(1, 1), (1, 2), (2, 1), (1, 3)]
    for k in (1, 63, 64, 65, 200):
        a = bits(k)
        p += [(a, a), (a, a + (1 << k)), (a + (1 << k), a)]
        if k > 1:
            p += [(a, a ^ 1), (a, a ^ (1 << (k - 2)))]
    for i in range(nrandom):
        a = bits(rng.randint(1, 200))
        b = (a, flip(a), bits(rng.randint(1, 200)))[i % 3]
        p.append((a, b))
    return p

HEADER = """Require Import Corelib.BinNums.PosDef.
Local Open Scope positive_scope.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
"""

def lemma(name, lhs):
    return ("Lemma %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))

counts = {}

# (a) Corelib's Pos.compare_cont and Pos.eqb.
out = [HEADER]
n = 0
for a, b in compare_pairs(70):
    for r in ("Eq", "Lt", "Gt"):
        out.append(lemma("cc%d" % n, "Pos.compare_cont %s %s %s" % (r, pos(a), pos(b))))
        n += 1
counts["N_CC"] = n
n = 0
for a, b in eqb_pairs(200):
    out.append(lemma("eq%d" % n, "Pos.eqb %s %s" % (pos(a), pos(b))))
    n += 1
counts["N_EQB"] = n
open(d + "/Diff.v", "w").write("".join(out))

# (c) Copies: over a user inductive of the same shape as positive (and a user
# comparison), and the Stdlib text of the functions over Corelib's types.
out = [HEADER, """
Inductive pos : Set := pI : pos -> pos | pO : pos -> pos | pH : pos.
Inductive cmp : Set := cEq | cLt | cGt.

Fixpoint cc (r:cmp) (x y:pos) {struct y} : cmp :=
  match x, y with
    | pI p, pI q => cc r p q
    | pI p, pO q => cc cGt p q
    | pI p, pH => cGt
    | pO p, pI q => cc cLt p q
    | pO p, pO q => cc r p q
    | pO p, pH => cGt
    | pH, pI q => cLt
    | pH, pO q => cLt
    | pH, pH => r
  end.

Fixpoint peqb p q {struct q} :=
  match p, q with
    | pI p, pI q => peqb p q
    | pO p, pO q => peqb p q
    | pH, pH => true
    | _, _ => false
  end.

Module StdPos.
Fixpoint compare_cont (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
    | p~1, q~1 => compare_cont r p q
    | p~1, q~0 => compare_cont Gt p q
    | p~1, 1 => Gt
    | p~0, q~1 => compare_cont Lt p q
    | p~0, q~0 => compare_cont r p q
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

Fixpoint eqb p q {struct q} :=
  match p, q with
    | p~1, q~1 => eqb p q
    | p~0, q~0 => eqb p q
    | 1, 1 => true
    | _, _ => false
  end.
End StdPos.
"""]
ncc = neq = 0
for a, b in compare_pairs(10):
    for r, ur in (("Eq", "cEq"), ("Lt", "cLt"), ("Gt", "cGt")):
        out.append(lemma("ucc%d" % ncc, "cc %s %s %s" % (ur, upos(a), upos(b))))
        out.append(lemma("scc%d" % ncc, "StdPos.compare_cont %s %s %s" % (r, pos(a), pos(b))))
        ncc += 1
for a, b in eqb_pairs(30):
    out.append(lemma("ueq%d" % neq, "peqb %s %s" % (upos(a), upos(b))))
    out.append(lemma("seq%d" % neq, "StdPos.eqb %s %s" % (pos(a), pos(b))))
    neq += 1
counts["N_COPY_CC"] = 2 * ncc
counts["N_COPY_EQB"] = 2 * neq
open(d + "/Copy.v", "w").write("".join(out))

# (d) Near misses: one branch changed (p~1, 1 => Lt instead of Gt), and the
# same function over an inductive whose constant constructor comes first.
out = [HEADER, """
Fixpoint cc_bad (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
    | p~1, q~1 => cc_bad r p q
    | p~1, q~0 => cc_bad Gt p q
    | p~1, 1 => Lt
    | p~0, q~1 => cc_bad Lt p q
    | p~0, q~0 => cc_bad r p q
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

Inductive opos : Set := oH : opos | oI : opos -> opos | oO : opos -> opos.

Fixpoint cc_ord (r:comparison) (x y:opos) {struct y} : comparison :=
  match x, y with
    | oI p, oI q => cc_ord r p q
    | oI p, oO q => cc_ord Gt p q
    | oI p, oH => Gt
    | oO p, oI q => cc_ord Lt p q
    | oO p, oO q => cc_ord r p q
    | oO p, oH => Gt
    | oH, oI q => Lt
    | oH, oO q => Lt
    | oH, oH => r
  end.

(* Where cc_bad differs from Pos.compare_cont. *)
Lemma bad_differs : cc_bad Eq (1~1) 1 = Lt.
Proof. vm_compute. reflexivity. Qed.
"""]
n = 0
for a, b in compare_pairs(10):
    for r in ("Eq", "Lt", "Gt"):
        out.append(lemma("bcc%d" % n, "cc_bad %s %s %s" % (r, pos(a), pos(b))))
        out.append(lemma("occ%d" % n, "cc_ord %s %s %s" % (r, opos(a), opos(b))))
        n += 1
open(d + "/Bad.v", "w").write("".join(out))

# (e) Free variables. A free variable in a non-recursive argument; in the
# recursive argument under 1 and under 65 constructors; in the recursive
# argument itself, where GRABREC returns before BINNUM.
def refl(name, lhs):
    return ("Lemma %s (p : positive) : %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))
open(d + "/Free0.v", "w").write(HEADER + refl("f0", "Pos.compare_cont Eq p (1~1)"))
open(d + "/Free1.v", "w").write(HEADER + refl("f1", "Pos.compare_cont Eq (1~0~1) (p~0)"))
open(d + "/Free65.v", "w").write(
    HEADER + refl("f65", "Pos.compare_cont Eq %s (p%s)" % (pos(bits(70)), "~0" * 65)))
open(d + "/FreeRec.v", "w").write(HEADER + refl("frec", "Pos.compare_cont Eq (1~1) p"))

# (e) A partial application that gets its last argument from map.
open(d + "/Partial.v", "w").write(HEADER + """
Fixpoint map {A B} (f : A -> B) (l : list A) : list B :=
  match l with nil => nil | cons x l => cons (f x) (map f l) end.
""" + lemma("partial", "map (Pos.compare_cont Eq (1~1)) (cons (1~0) (cons (1~1) (cons (1~0~0) nil)))"))

with open(d + "/counts", "w") as f:
    for k, v in counts.items():
        f.write("%s=%d\n" % (k, v))
PY
. "$d/counts"

for lib in Diff Copy Bad Free0 Free1 Free65 FreeRec Partial; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# chk LOG ARGS...: rocqchk with the counters on; its output goes to LOG.
chk() {
  local log=$1; shift
  ROCQ_VM_BINNUM_STATS=${STATS:-1} rocqchk -silent -bytecode-compiler yes -R "$d" "" "$@" \
    > "$d/$log" 2>&1 || { cat "$d/$log" >&2; fail "rocqchk $* failed"; }
}

# stat LOG ROUTINE FIELD: FIELD of ROUTINE, summed over every process.
stat() {
  awk -v r="$2:" -v f="$3" '$2 == "routine" && $3 == r {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

# recog LOG FIELD: FIELD of the recognizer line, summed over every process.
recog() {
  awk -v f="$2" '$2 == "recognizer:" {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

# expect WHAT ACTUAL OP EXPECTED
expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

bound() { grep -q "^binnum\[[0-9]*\] bind $2: $3\$" "$d/$1"; }
missed() { grep -q "^binnum\[[0-9]*\] near-miss $2: " "$d/$1"; }

# (a) One call per lemma: the cast of each proof is checked once.
chk a.log -norec Diff
expect "(a) Pos.compare_cont hits" "$(stat a.log Pos.compare_cont hits)" -eq "$N_CC"
expect "(a) Pos.compare_cont calls" "$(stat a.log Pos.compare_cont calls)" -eq "$N_CC"
expect "(a) Pos.compare_cont refusals" "$(stat a.log Pos.compare_cont refusals)" -eq 0
expect "(a) Pos.eqb hits" "$(stat a.log Pos.eqb hits)" -eq "$N_EQB"
expect "(a) Pos.eqb calls" "$(stat a.log Pos.eqb calls)" -eq "$N_EQB"
expect "(a) Pos.eqb refusals" "$(stat a.log Pos.eqb refusals)" -eq 0
bound a.log Corelib.BinNums.PosDef.Pos.compare_cont Pos.compare_cont \
  || fail "(a) Corelib's Pos.compare_cont is not bound"
bound a.log Corelib.BinNums.PosDef.Pos.eqb Pos.eqb || fail "(a) Corelib's Pos.eqb is not bound"
binds_a=$(recog a.log binds)

# (b) Recognition off: nothing is bound and no routine runs.
ROCQ_VM_BINNUM=0 chk b.log -norec Diff
expect "(b) binds" "$(recog b.log binds)" -eq 0
expect "(b) Pos.compare_cont calls" "$(stat b.log Pos.compare_cont calls)" -eq 0
expect "(b) Pos.eqb calls" "$(stat b.log Pos.eqb calls)" -eq 0
# Only Pos.eqb off.
ROCQ_VM_BINNUM=-Pos.eqb chk b2.log -norec Diff
expect "(b) -Pos.eqb: Pos.compare_cont hits" "$(stat b2.log Pos.compare_cont hits)" -eq "$N_CC"
expect "(b) -Pos.eqb: Pos.eqb calls" "$(stat b2.log Pos.eqb calls)" -eq 0
# A value that is neither 0 nor a list of -name stops rocqchk, and the message
# lists the routines.
for v in 1 -Pos.nope; do
  if ROCQ_VM_BINNUM=$v rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec Diff > "$d/b3.log" 2>&1; then
    fail "(b) ROCQ_VM_BINNUM=$v was accepted"
  fi
  grep -q "Pos.compare_cont" "$d/b3.log" && grep -q "Pos.eqb" "$d/b3.log" \
    || { cat "$d/b3.log" >&2; fail "(b) ROCQ_VM_BINNUM=$v: the message does not list the routines"; }
done
# Without ROCQ_VM_BINNUM_STATS nothing is printed.
rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec Diff > "$d/b4.log" 2>&1
! grep -q "^binnum\[" "$d/b4.log" || fail "(b) counters printed without ROCQ_VM_BINNUM_STATS"

# (c) The copies bind, and their results are right.
chk c.log -norec Copy
bound c.log Copy.cc Pos.compare_cont || fail "(c) Copy.cc is not bound"
bound c.log Copy.peqb Pos.eqb || fail "(c) Copy.peqb is not bound"
bound c.log Copy.StdPos.compare_cont Pos.compare_cont || fail "(c) Copy.StdPos.compare_cont is not bound"
bound c.log Copy.StdPos.eqb Pos.eqb || fail "(c) Copy.StdPos.eqb is not bound"
expect "(c) Pos.compare_cont hits" "$(stat c.log Pos.compare_cont hits)" -eq "$N_COPY_CC"
expect "(c) Pos.compare_cont refusals" "$(stat c.log Pos.compare_cont refusals)" -eq 0
expect "(c) Pos.eqb hits" "$(stat c.log Pos.eqb hits)" -eq "$N_COPY_EQB"
expect "(c) Pos.eqb refusals" "$(stat c.log Pos.eqb refusals)" -eq 0

# (d) The near misses do not bind: no routine runs for their lemmas.
STATS=2 chk d.log -norec Bad
missed d.log Bad.cc_bad || fail "(d) Bad.cc_bad is not reported as a near miss"
missed d.log Bad.cc_ord || fail "(d) Bad.cc_ord is not reported as a near miss"
! bound d.log Bad.cc_bad Pos.compare_cont || fail "(d) Bad.cc_bad is bound"
! bound d.log Bad.cc_ord Pos.compare_cont || fail "(d) Bad.cc_ord is bound"
grep -q "^binnum\[[0-9]*\]   at " "$d/d.log" || fail "(d) ROCQ_VM_BINNUM_STATS=2 prints no first difference"
expect "(d) Pos.compare_cont calls" "$(stat d.log Pos.compare_cont calls)" -eq 0

# (e) Refusals. Each lemma is [l = l] with a free variable p in l, proved by
# vm_compute, so rocqchk compares the normal form of the goal (which no
# longer calls Pos.compare_cont) with the goal, whose two sides it evaluates.
# A stuck match is compared by running each of its branches on a fresh
# variable, and a stuck fixpoint by running its body on fresh variables:
# BINNUM refuses that call at once, since r is then a variable.
#
# l = Pos.compare_cont Eq p 3. Each side: the call is refused (p in x), the
# match on x is stuck, and its branches p'~1 and p'~0 call
# Pos.compare_cont Eq p' 1 and Pos.compare_cont Lt p' 1, both refused: 6.
chk e0.log -norec Free0
expect "(e) Free0 hits" "$(stat e0.log Pos.compare_cont hits)" -eq 0
expect "(e) Free0 refusals" "$(stat e0.log Pos.compare_cont refusals)" -eq 6
# l = Pos.compare_cont Eq 5 p~0. Each side: the call is refused (p under one
# constructor of y); the recursive call has y = p, so GRABREC returns a stuck
# fixpoint before BINNUM; reading back that fixpoint is refused once: 4.
chk e1.log -norec Free1
expect "(e) Free1 hits" "$(stat e1.log Pos.compare_cont hits)" -eq 0
expect "(e) Free1 refusals" "$(stat e1.log Pos.compare_cont refusals)" -eq 4
# l = Pos.compare_cont Eq x (p~0...~0), x of 70 bits, 65 constructors above
# p. Each side recurses 65 times while y is still a constructor, and each of
# these calls is refused, then the stuck fixpoint is read back once: 132. The
# call at depth k reads the k constructors of y above p before it refuses, so
# the words read are at least 2 x (1 + ... + 65) = 4290.
chk e65.log -norec Free65
expect "(e) Free65 hits" "$(stat e65.log Pos.compare_cont hits)" -eq 0
expect "(e) Free65 refusals" "$(stat e65.log Pos.compare_cont refusals)" -eq 132
expect "(e) Free65 words" "$(stat e65.log Pos.compare_cont words)" -ge 4290
# l = Pos.compare_cont Eq 3 p. The variable is the recursive argument:
# GRABREC returns a stuck fixpoint before BINNUM, so evaluation never calls
# the routine; only the read-back of each side's stuck fixpoint does: 2.
chk erec.log -norec FreeRec
expect "(e) FreeRec hits" "$(stat erec.log Pos.compare_cont hits)" -eq 0
expect "(e) FreeRec refusals" "$(stat erec.log Pos.compare_cont refusals)" -eq 2
# The partial application Pos.compare_cont Eq 3 is a closure until map gives
# it its last argument; then all three arguments are closed numbers: three
# hits, no refusal.
chk ep.log -norec Partial
expect "(e) Partial hits" "$(stat ep.log Pos.compare_cont hits)" -eq 3
expect "(e) Partial refusals" "$(stat ep.log Pos.compare_cont refusals)" -eq 0

# (f) -j 2: the workers check the proofs and print their own counters; the
# counters they inherit from the main process are zeroed at the fork.
chk f.log -j 2 -norec Diff
expect "(f) Pos.compare_cont hits" "$(stat f.log Pos.compare_cont hits)" -eq "$N_CC"
expect "(f) Pos.eqb hits" "$(stat f.log Pos.eqb hits)" -eq "$N_EQB"
expect "(f) binds" "$(recog f.log binds)" -eq "$binds_a"
pids=$(awk '$2 == "routine" { print $1 }' "$d/f.log" | sort -u | wc -l)
expect "(f) processes that print counters" "$pids" -ge 3

exit 0
