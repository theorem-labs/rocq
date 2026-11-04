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
#  (d) a copy with one branch changed, a copy over an inductive with its
#      constructors in another order, and two copies that differ in one
#      variable only (a call argument, a match scrutinee) do not bind, each
#      for the reason the recognizer gives, and their own results still
#      check;
#  (e) inputs of both routines with a free variable: where the bytecode
#      inspects it, the routine refuses and the bytecode computes; where
#      the bytecode stops before it, the routine hits; with exact counts. A
#      partial application gets its last argument later and hits;
#  (f) the -j 2 run of (a): each worker prints its own counters;
#  (g) the packing of literals on: the same calls and refusals. The words
#      of (a) to (f) are those of chain literals, so those checks run with
#      ROCQ_VM_BINNUM=-packlit.
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

# (d) Near misses: one branch changed (p~1, 1 => Lt instead of Gt), the same
# function over an inductive whose constant constructor comes first, and two
# bodies that differ from the reference in one variable only.
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

(* The reference with one variable changed: in the branch p~1, q~1 the
   second argument of the recursive call is q, not p. *)
Fixpoint cc_swap (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
    | _~1, q~1 => cc_swap r q q
    | p~1, q~0 => cc_swap Gt p q
    | p~1, 1 => Gt
    | p~0, q~1 => cc_swap Lt p q
    | p~0, q~0 => cc_swap r p q
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

(* The reference with one variable changed: the branch x = 1 matches x, not
   y. *)
Fixpoint cc_scr (r:comparison) (x y:positive) {struct y} : comparison :=
  match x with
    | p~1 => match y with q~1 => cc_scr r p q | q~0 => cc_scr Gt p q | 1 => Gt end
    | p~0 => match y with q~1 => cc_scr Lt p q | q~0 => cc_scr r p q | 1 => Gt end
    | 1 => match x with _~1 => Lt | _~0 => Lt | 1 => r end
  end.

(* Where each of them differs from Pos.compare_cont. The values of
   Pos.compare_cont are checked by the kernel's own conversion, not by the
   VM, so that no lemma of this library calls the routine. *)
Lemma bad_differs : cc_bad Eq (1~1) 1 = Lt.
Proof. vm_compute. reflexivity. Qed.
Lemma bad_ref : Pos.compare_cont Eq (1~1) 1 = Gt.
Proof. reflexivity. Qed.
Lemma swap_differs : cc_swap Eq (1~1) (1~0~1) = Eq.
Proof. vm_compute. reflexivity. Qed.
Lemma swap_ref : Pos.compare_cont Eq (1~1) (1~0~1) = Lt.
Proof. reflexivity. Qed.
Lemma scr_differs : cc_scr Eq 1 (1~1) = Eq.
Proof. vm_compute. reflexivity. Qed.
Lemma scr_ref : Pos.compare_cont Eq 1 (1~1) = Lt.
Proof. reflexivity. Qed.
"""]
n = 0
for a, b in compare_pairs(10):
    for r in ("Eq", "Lt", "Gt"):
        out.append(lemma("bcc%d" % n, "cc_bad %s %s %s" % (r, pos(a), pos(b))))
        out.append(lemma("occ%d" % n, "cc_ord %s %s %s" % (r, opos(a), opos(b))))
        out.append(lemma("wcc%d" % n, "cc_swap %s %s %s" % (r, pos(a), pos(b))))
        out.append(lemma("scc%d" % n, "cc_scr %s %s %s" % (r, pos(a), pos(b))))
        n += 1
open(d + "/Bad.v", "w").write("".join(out))

# (e) Free variables. For Pos.compare_cont: a free variable in a
# non-recursive argument; in the recursive argument under 1 and under 65
# constructors; the recursive argument itself, where GRABREC returns before
# BINNUM. For Pos.eqb: a free variable under 1 constructor of p; under 1 and
# under 65 constructors of q; q itself. The lemmas named *f have a constructor
# (computed by cbv) as their right side, so that the value the bytecode
# computes after a refusal is checked too.
def refl(name, lhs):
    return ("Lemma %s (p : positive) : %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))
def free_cbv(name, lhs):
    return ("Lemma %s (p : positive) : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))
open(d + "/Free0.v", "w").write(HEADER + refl("f0", "Pos.compare_cont Eq p (1~1)"))
open(d + "/Free1.v", "w").write(HEADER + refl("f1", "Pos.compare_cont Eq (1~0~1) (p~0)"))
open(d + "/Free65.v", "w").write(
    HEADER + refl("f65", "Pos.compare_cont Eq %s (p%s)" % (pos(bits(70)), "~0" * 65)))
open(d + "/FreeRec.v", "w").write(HEADER + refl("frec", "Pos.compare_cont Eq (1~1) p"))
open(d + "/EqP1.v", "w").write(HEADER + refl("ep1", "Pos.eqb (p~1) (1~1)"))
open(d + "/EqP1f.v", "w").write(HEADER + free_cbv("ep1f", "Pos.eqb (p~1) (1~0)"))
open(d + "/EqQ1.v", "w").write(HEADER + refl("eq1", "Pos.eqb (1~0~0) (p~0)"))
open(d + "/EqQ1f.v", "w").write(HEADER + free_cbv("eq1f", "Pos.eqb (1~0~1) (p~0)"))
open(d + "/EqQ65.v", "w").write(
    HEADER + refl("eq65", "Pos.eqb %s (p%s)" % (pos(1 << 69), "~0" * 65)))
open(d + "/EqRec.v", "w").write(HEADER + refl("erec", "Pos.eqb (1~1) p"))

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

for lib in Diff Copy Bad Free0 Free1 Free65 FreeRec EqP1 EqP1f EqQ1 EqQ1f EqQ65 EqRec Partial; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# chk LOG ARGS...: rocqchk with the counters on; its output goes to LOG.
# The words counted below are those of chain literals: ROCQ_VM_BINNUM
# defaults to -packlit here, since a packed literal is one word (see (g)).
chk() {
  local log=$1; shift
  ROCQ_VM_BINNUM=${ROCQ_VM_BINNUM--packlit} ROCQ_VM_BINNUM_STATS=${STATS:-1} \
    rocqchk -silent -bytecode-compiler yes -R "$d" "" "$@" \
    > "$d/$log" 2>&1 || { cat "$d/$log" >&2; fail "rocqchk $* failed"; }
}

# per_routine LOG FIELD: "routine value" lines of FIELD, summed over every
# process.
per_routine() {
  awk -v f="$2" '$2 == "routine" {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s[$3] += kv[2] } }
    END { for (r in s) print r, s[r] }' "$d/$1" | sort
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
# missed LOG NAME REASON: NAME is a near miss of the reference of
# Pos.compare_cont, rejected for REASON.
missed() { grep -q "^binnum\[[0-9]*\] near-miss $2: Pos.compare_cont: $3\$" "$d/$1"; }
# first_diff LOG NAME: with ROCQ_VM_BINNUM_STATS=2, the path to the first node
# where NAME differs from the reference.
first_diff() {
  awk -v n="near-miss $2: " 'hit { sub(/^binnum\[[0-9]*\]   at /, ""); print; exit }
    index($0, n) { hit = 1 }' "$d/$1"
}

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

# (d) The near misses do not bind: no routine runs for their lemmas. Each is
# rejected by the guard named in its reason; cc_swap and cc_scr only by the
# comparison of a variable, at the path given.
STATS=2 chk d.log -norec Bad
missed d.log Bad.cc_bad constructor || fail "(d) Bad.cc_bad is not a near miss for its constructor"
missed d.log Bad.cc_ord "case info" || fail "(d) Bad.cc_ord is not a near miss for its case info"
missed d.log Bad.cc_swap "de Bruijn index" || fail "(d) Bad.cc_swap is not a near miss for a variable"
missed d.log Bad.cc_scr "de Bruijn index" || fail "(d) Bad.cc_scr is not a near miss for a variable"
for f in cc_bad cc_ord cc_swap cc_scr; do
  ! bound d.log "Bad.$f" Pos.compare_cont || fail "(d) Bad.$f is bound"
done
top="fixpoint body 1 > lambda body > lambda body > lambda body"
expect "(d) first difference of cc_swap" "'$(first_diff d.log Bad.cc_swap)'" = \
  "'$top > branch 1 > branch 1 > argument 2'"
expect "(d) first difference of cc_scr" "'$(first_diff d.log Bad.cc_scr)'" = \
  "'$top > branch 3 > match scrutinee'"
expect "(d) Pos.compare_cont calls" "$(stat d.log Pos.compare_cont calls)" -eq 0

# (e) Refusals. Each lemma has a free variable p in its left side l and is
# proved by vm_compute, so rocqchk compares the normal form of the goal (which
# no longer calls the routine) with the goal, and evaluates each occurrence of
# l in it: twice for [l = l], once for [l = c]. A stuck match is compared by
# running each of its branches on a fresh variable, and a stuck fixpoint by
# running its body on fresh variables (mk_fix_body, kernel/vmvalues.ml): the
# routine refuses that call at its first argument.
#
# Words read (since slice 7 of the design, misc/rocqchk_binnum_inspect.sh):
# both routines read what the bytecode inspects, 2 per step (one node of
# each number) up to and including the step that finds the variable, or
# where one number ends, and nothing below. Pos.compare_cont reads r (1)
# only when the result is r itself: both numbers end at the same step with
# no difference. Pos.eqb stops at the first step whose nodes differ.
#
# Each occurrence of l is a call at a call site: BINNUMCALL runs the routine
# there first. When it refuses, the call runs, and the routine runs again at
# the entry of the function (BINNUM), with the same reads, unless GRABREC
# returns first. The counts at function entry are those described below for
# each case; the counts at the call sites are one call per occurrence of l,
# with the reads of the first entry call of that occurrence.
#
# ecase LIB ROUTINE HITS REFUSALS WORDS SHITS SREFUSALS SWORDS: rocqchk LIB;
# the counts of ROUTINE at function entry, then at call sites.
ecase() {
  chk "$1.log" -norec "$1"
  expect "(e) $1 $2 entry hits" "$(( $(stat "$1.log" "$2" entry-calls) - $(stat "$1.log" "$2" entry-refusals) ))" -eq "$3"
  expect "(e) $1 $2 entry refusals" "$(stat "$1.log" "$2" entry-refusals)" -eq "$4"
  expect "(e) $1 $2 entry words" "$(stat "$1.log" "$2" entry-words)" -eq "$5"
  expect "(e) $1 $2 site hits" "$(( $(stat "$1.log" "$2" site-calls) - $(stat "$1.log" "$2" site-refusals) ))" -eq "$6"
  expect "(e) $1 $2 site refusals" "$(stat "$1.log" "$2" site-refusals)" -eq "$7"
  expect "(e) $1 $2 site words" "$(stat "$1.log" "$2" site-words)" -eq "$8"
}
# l = Pos.compare_cont Eq p 3. Each side: the call is refused (p is x), the
# match on x is stuck, and its branches p'~1 and p'~0 call
# Pos.compare_cont Eq p' 1 and Pos.compare_cont Lt p' 1, both refused: 6.
# Each reads the two nodes of the first step: 6 x 2 = 12 words. At the call
# site, each side is refused after that step: 2 refusals, 4 words.
ecase Free0 Pos.compare_cont 0 6 12 0 2 4
# l = Pos.compare_cont Eq 5 p~0. Each side: the call is refused (p under one
# constructor of y; two steps, 4 words); the recursive call has y = p, so
# GRABREC returns a stuck fixpoint before BINNUM; its read-back, on fresh
# variables, is refused at the first step (2 words): 4 refusals, 12 words.
# At the call site: 2 x 4.
ecase Free1 Pos.compare_cont 0 4 12 0 2 8
# l = Pos.compare_cont Eq x (p~0...~0), x of 70 bits, 65 constructors above
# p. Each side: the calls with m = 65, ..., 1 constructors of y above p are
# refused, each after m + 1 steps; then y = p, and the read-back is refused
# after one step: 2 x 66 = 132 refusals, 2 x (2 x (2145 + 65) + 2) = 8844
# words. At the call site, m = 65: 2 x 2 x 66 = 264 words.
ecase Free65 Pos.compare_cont 0 132 8844 0 2 264
# l = Pos.compare_cont Eq 3 p. The variable is the recursive argument:
# GRABREC returns a stuck fixpoint before BINNUM, so the entry runs the
# routine only for the read-back of each side's stuck fixpoint, refused
# after one step: 2 refusals, 4 words. The call site reads one step: 2 x 2.
ecase FreeRec Pos.compare_cont 0 2 4 0 2 4
# l = Pos.eqb (p~1) 3. Each side: the call is refused (p under one
# constructor of x, two steps, 4 words); the bytecode calls Pos.eqb p 1,
# refused at once (p is x, 2 words); the match on p is then stuck, and its
# branches do not call Pos.eqb: 4 refusals, 12 words. Call site: 2 x 4.
ecase EqP1 Pos.eqb 0 4 12 0 2 8
# Pos.eqb (p~1) 2 = false. The first step differs (xI against xO), where the
# bytecode answers false without inspecting p: a hit at the call site, 2
# words, and no entry. Before slice 7 the routine read on to p and refused.
ecase EqP1f Pos.eqb 0 0 0 1 0 2
# l = Pos.eqb 4 (p~0). Each side: the call is refused (p under one constructor
# of y, 4 words); the recursive call has y = p, so GRABREC returns a stuck
# fixpoint; its read-back is refused (2 words): 4 refusals, 12 words. Call
# site: 2 x 4.
ecase EqQ1 Pos.eqb 0 4 12 0 2 8
# Pos.eqb 5 (p~0) = false: the first step differs; a hit at the call site.
ecase EqQ1f Pos.eqb 0 0 0 1 0 2
# l = Pos.eqb x (p~0...~0), x = 2^69, 65 constructors above p, all xO as the
# 69 of x. Each side: the calls with m = 65, ..., 1 constructors of y above p
# are refused, each after m + 1 steps; then y = p, and the read-back is
# refused: 2 x 66 = 132 refusals, 2 x (2 x (2145 + 65) + 2) = 8844 words.
# Call site, m = 65: 2 x 2 x 66 = 264 words.
ecase EqQ65 Pos.eqb 0 132 8844 0 2 264
# l = Pos.eqb 3 p. Only the read-back of each side's stuck fixpoint runs the
# routine at the entry: 2 refusals, 4 words. Call site: 2 x 2.
ecase EqRec Pos.eqb 0 2 4 0 2 4
# The partial application Pos.compare_cont Eq 3 is a closure until map gives
# it its last argument (APPLY1 to the closure, then its entry); then all
# three arguments are closed numbers: three hits at the entry, none at a
# call site. Words: 4 for 2 (two steps; the first differs, so r is not
# read), 5 for 3 (two steps and r, since 3 = 3), 4 for 4 (two steps: 3 ends
# first, and the xH of 4 is not read): 13.
ecase Partial Pos.compare_cont 3 0 13 0 0 0

# (f) -j 2: the workers check the proofs and print their own counters; the
# counters they inherit from the main process are zeroed at the fork.
chk f.log -j 2 -norec Diff
expect "(f) Pos.compare_cont hits" "$(stat f.log Pos.compare_cont hits)" -eq "$N_CC"
expect "(f) Pos.eqb hits" "$(stat f.log Pos.eqb hits)" -eq "$N_EQB"
expect "(f) binds" "$(recog f.log binds)" -eq "$binds_a"
pids=$(awk '$2 == "routine" { print $1 }' "$d/f.log" | sort -u | wc -l)
expect "(f) processes that print counters" "$pids" -ge 3

# (g) The packing of literals on, as by default (rocqchk_binnum_literal.sh
# tests it): a literal is then read as one packed word, which changes the
# words above, but no routine makes or refuses another call.
for lib in Diff Copy Bad Free0 Free1 Free65 FreeRec EqP1 EqP1f EqQ1 EqQ1f EqQ65 EqRec Partial; do
  chk "g-$lib.log" -norec "$lib"
  ROCQ_VM_BINNUM_STATS=1 rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" \
    > "$d/g-$lib-lit.log" 2>&1 || { cat "$d/g-$lib-lit.log" >&2; fail "(g) rocqchk -norec $lib failed"; }
  for f in entry-calls entry-refusals site-calls site-refusals; do
    [ "$(per_routine "g-$lib.log" $f)" = "$(per_routine "g-$lib-lit.log" $f)" ] \
      || fail "(g) $lib: the $f of the routines change with the packing of literals"
  done
done

exit 0
