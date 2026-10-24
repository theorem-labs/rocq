#!/usr/bin/env bash
# rocqchk runs a routine of the BINNUM family at the call site of a
# recognized function (BINNUMCALL, kernel/vmbytegen.ml compile_constant), not
# only at its entry (BINNUM). See misc/rocqchk_binnum.sh and
# misc/rocqchk_binnum_arith.sh for the routines themselves.
#
# Each lemma states [e = c] where c was computed by cbv, which does not use
# the VM, and is proved by vm_compute, so that rocqchk recomputes e with its
# own bytecode. ROCQ_VM_BINNUM_STATS=1 prints, for each routine, its calls at
# function entry (entry-*) and at call sites (site-*):
#  (a) each call form: a call in the lemma itself; a tail call (APPTERM); a
#      call that is not a tail call (APPLY); a tail and a non-tail call in a
#      match branch; for Pos.add_carry, which is function 1 of the block of
#      Pos.add, and for others. Each runs at its call site, never at entry;
#  (b) calls that stay normal calls: a partial application, which runs at
#      entry once it gets its last argument; a universe polymorphic copy,
#      which is never bound; a call through a variable;
#  (c) numbers around 64 bits, where a routine leaves its 64-bit word path
#      for limbs: 62, 63, 64, 65, 126, 127 and 128 bits, for Pos.add,
#      Pos.add_carry, Pos.mul, Z.pos_sub, Z.add, Z.mul and Z.pos_div_eucl
#      (carries out of 63 and 64 bits, products that overflow 64 bits,
#      borrows from limbs into a word);
#  (d) a refused call at a call site runs the normal call, whose entry
#      refuses again: the counts of both;
#  (e) ROCQ_VM_BINNUM=0: nothing is bound and no routine runs; -j 2: each
#      worker prints its own counters.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

python3 - "$d" <<'PY'
import random, sys

d = sys.argv[1]
rng = random.Random(20261026)

def bits(k):
    """A random number of exactly k bits."""
    return 1 if k == 1 else rng.randrange(1 << (k - 1), 1 << k)

def pos(n):
    t = "xH"
    for c in bin(n)[3:]:
        t = "(%s %s)" % ("xI" if c == "1" else "xO", t)
    return t

def z(n): return "Z0" if n == 0 else "(Zpos %s)" % pos(n) if n > 0 else "(Zneg %s)" % pos(-n)

HEADER = """Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
"""

def lemma(name, lhs):
    return ("Lemma %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))

counts = {}
def count(key, n=1):
    counts[key] = counts.get(key, 0) + n

# (a) Call forms. Each wrapper is a plain function, not recognized, whose
# body calls the routines: its lemma [w args = c] calls w once, at a call
# site that is not bound, and w's body then makes the calls below.
out = [HEADER, """
(* A tail call (APPTERM): Pos.add_carry is function 1 of Pos.add's block. *)
Definition tail_carry (x y : positive) := Pos.add_carry x y.
Definition tail_add (x y : positive) := Pos.add x y.
(* Not a tail call (APPLY2), inside a tail call (APPTERM1) of Pos.succ. *)
Definition apply_carry (x y : positive) := Pos.succ (Pos.add_carry x y).
(* Tail calls in the branches of a match in tail position. *)
Definition branch_tail (b : bool) (x y : positive) :=
  match b with true => Pos.add_carry x y | false => Pos.mul x y end.
(* Calls that are not tail calls, in the branches of a match that is the
   argument of a call: the branches end with a jump to the match's return
   address. *)
Definition branch_apply (b : bool) (x y : positive) :=
  Pos.succ (match b with true => Pos.add_carry x y | false => Z.to_pos (Z.add (Zpos x) (Zneg y)) end).
(* Three arguments (APPLY3 and APPTERM3), and a call whose result is
   matched. *)
Definition three (x y : positive) :=
  match Pos.compare_cont Eq x y with Lt => Pos.compare_cont Gt y x | _ => Pos.compare_cont Lt x y end.
(* A call of a function of one argument, not in tail position. *)
Definition one (z : Z) := Z.add (Z.div2 z) (Z.double z).
"""]
for i in range(12):
    a, b = bits(rng.randint(1, 140)), bits(rng.randint(1, 140))
    for fn, args, routines in (
            ("Pos.add_carry", (pos(a), pos(b)), ["Pos.add_carry"]),
            ("tail_carry", (pos(a), pos(b)), ["Pos.add_carry"]),
            ("tail_add", (pos(a), pos(b)), ["Pos.add"]),
            ("apply_carry", (pos(a), pos(b)), ["Pos.add_carry", "Pos.succ"]),
            ("branch_tail true", (pos(a), pos(b)), ["Pos.add_carry"]),
            ("branch_tail false", (pos(a), pos(b)), ["Pos.mul"]),
            ("branch_apply true", (pos(a), pos(b)), ["Pos.add_carry", "Pos.succ"]),
            ("three", (pos(a), pos(b)), ["Pos.compare_cont", "Pos.compare_cont"]),
            ("one", (z(rng.choice([1, -1]) * a),), ["Z.div2", "Z.double", "Z.add"])):
        out.append(lemma("f%d" % len(out), "%s %s" % (fn, " ".join(args))))
        for r in routines:
            count("FORM_" + r.replace(".", "_"))
# Pos.add_carry at its edges, at a call site in the lemma itself.
for a, b in ((1, 1), (1, 2), (2, 1), (3, 3), ((1 << 64) - 1, 1), (1, (1 << 64) - 1)):
    out.append(lemma("c%d" % len(out), "Pos.add_carry %s %s" % (pos(a), pos(b))))
    out.append(lemma("t%d" % len(out), "tail_carry %s %s" % (pos(a), pos(b))))
    count("FORM_Pos_add_carry", 2)
open(d + "/Forms.v", "w").write("".join(out))

# (b) Calls that stay normal calls.
open(d + "/Normal.v", "w").write(HEADER + """
Fixpoint map {A B} (f : A -> B) (l : list A) : list B :=
  match l with nil => nil | cons x l => cons (f x) (map f l) end.
(* A partial application: Pos.add_carry 3 is a closure until map gives it
   its last argument; the call then goes through APPLY1 to the entry. *)
""" + lemma("partial", "map (Pos.add_carry (xI xH)) (cons (xO xH) (cons (xI xH) (cons xH nil)))") + """
(* A copy of Pos.add_carry's block with a universe: never bound, at entry or
   at a call site. *)
Polymorphic Fixpoint padd@{u} (x y : positive) : positive :=
  match x, y with
    | xI p, xI q => xO (padd_carry p q)
    | xI p, xO q => xI (padd p q)
    | xI p, xH => xO (Pos.succ p)
    | xO p, xI q => xI (padd p q)
    | xO p, xO q => xO (padd p q)
    | xO p, xH => xI p
    | xH, xI q => xO (Pos.succ q)
    | xH, xO q => xI q
    | xH, xH => xO xH
  end
with padd_carry@{u} (x y : positive) : positive :=
  match x, y with
    | xI p, xI q => xI (padd_carry p q)
    | xI p, xO q => xO (padd_carry p q)
    | xI p, xH => xI (Pos.succ p)
    | xO p, xI q => xO (padd_carry p q)
    | xO p, xO q => xI (padd p q)
    | xO p, xH => xO (Pos.succ p)
    | xH, xI q => xI (Pos.succ q)
    | xH, xO q => xO (Pos.succ q)
    | xH, xH => xI xH
  end.
""" + lemma("poly", "padd_carry (xI (xO xH)) (xI xH)") + """
(* A call through a variable: [f] is not a constant at its call site. *)
Definition through (f : positive -> positive -> positive) (x y : positive) := f x y.
""" + lemma("var", "through Pos.add_carry (xI (xO xH)) (xI xH)"))

# (c) Around 64 bits.
B = [62, 63, 64, 65, 126, 127, 128]
def edge(k):
    return [(1 << k) - 1, 1 << (k - 1), (1 << (k - 1)) + 1, bits(k)]
out = [HEADER]
for k in B:
    for j in B:
        for a in edge(k)[:2] + [bits(k)]:
            for b in edge(j)[:2] + [bits(j)]:
                for f, lhs in (("Pos.add", "Pos.add %s %s" % (pos(a), pos(b))),
                               ("Pos.add_carry", "Pos.add_carry %s %s" % (pos(a), pos(b))),
                               ("Pos.mul", "Pos.mul %s %s" % (pos(a), pos(b))),
                               ("Z.pos_sub", "Z.pos_sub %s %s" % (pos(a), pos(b))),
                               ("Z.pos_div_eucl", "Z.pos_div_eucl %s %s" % (pos(a), z(b)))):
                    out.append(lemma("b%d" % len(out), lhs))
                    count("EDGE_" + f.replace(".", "_"))
# Signs, through Z.add (Pos.add or Z.pos_sub) and Z.mul.
for k in B:
    for a in edge(k):
        for b in edge(rng.choice(B)) + [a, a - 1, a + 1]:
            for sa, sb in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                out.append(lemma("b%d" % len(out), "Z.add %s %s" % (z(sa * a), z(sb * b))))
                out.append(lemma("b%d" % len(out), "Z.mul %s %s" % (z(sa * a), z(sb * b))))
                count("EDGE_Z_add")
                count("EDGE_Z_mul")
# Products that fit in 64 bits exactly, and the first that do not.
for a, b in (((1 << 32) - 1, (1 << 32) + 1), (1 << 32, 1 << 32), (1 << 32, (1 << 32) - 1),
             ((1 << 63) - 1, 2), ((1 << 63) + 1, 2), (3, (1 << 62) + 1), (3, (1 << 63) - 1)):
    out.append(lemma("b%d" % len(out), "Pos.mul %s %s" % (pos(a), pos(b))))
    count("EDGE_Pos_mul")
# Divisions: dividend smaller than, equal to and just above the divisor.
for k in B:
    for b in edge(k):
        for a in (b - 1 or 1, b, b + 1, 2 * b, b * b, (b << 64) + 1):
            out.append(lemma("b%d" % len(out), "Z.pos_div_eucl %s %s" % (pos(a), z(b))))
            count("EDGE_Z_pos_div_eucl")
open(d + "/Edges.v", "w").write("".join(out))

# (d) Refusals at a call site: a free variable in an argument.
open(d + "/Refuse.v", "w").write(HEADER + """
Lemma r1 (p : positive) : Pos.add_carry (xO p) xH = Pos.add_carry (xO p) xH.
Proof. vm_compute. reflexivity. Qed.
""")

with open(d + "/counts", "w") as f:
    for k, v in sorted(counts.items()):
        f.write("%s=%d\n" % (k, v))
PY
. "$d/counts"

for lib in Forms Normal Edges Refuse; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

chk() {
  local log=$1; shift
  ROCQ_VM_BINNUM_STATS=1 rocqchk -silent -bytecode-compiler yes -R "$d" "" "$@" \
    > "$d/$log" 2>&1 || { cat "$d/$log" >&2; fail "rocqchk $* failed"; }
}

# stat LOG ROUTINE FIELD: FIELD of ROUTINE, summed over every process.
stat() {
  awk -v r="$2:" -v f="$3" '$2 == "routine" && $3 == r {
      for (i = 4; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

line_stat() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

key() { echo "$1_$(echo "$2" | tr . _)"; }
count_of() { local k; k=$(key "$1" "$2"); echo "${!k:-0}"; }

# site LOG ROUTINE CALLS REFUSALS, entry LOG ROUTINE CALLS REFUSALS
site() {
  expect "$1 $2 site-calls" "$(stat "$1" "$2" site-calls)" -eq "$3"
  expect "$1 $2 site-refusals" "$(stat "$1" "$2" site-refusals)" -eq "$4"
}
entry() {
  expect "$1 $2 entry-calls" "$(stat "$1" "$2" entry-calls)" -eq "$3"
  expect "$1 $2 entry-refusals" "$(stat "$1" "$2" entry-refusals)" -eq "$4"
}

# (a) Every call of the call forms runs at its call site and hits.
chk forms.log -norec Forms
for r in Pos.add_carry Pos.add Pos.succ Pos.mul Pos.compare_cont Z.div2 Z.double Z.add; do
  site forms.log "$r" "$(count_of FORM "$r")" 0
  entry forms.log "$r" 0 0
done
expect "forms call-sites binds" "$(line_stat forms.log call-sites binds)" -ge 1

# (b) Normal calls. The partial application: 3 calls at entry, none at a call
# site. The polymorphic copy: padd and padd_carry are never bound, so
# padd_carry 5 3 runs its bytecode; its step padd_carry 2 1 = xO (Pos.succ 1)
# calls Pos.succ, whose call site in padd_carry's body is bound (Pos.succ is
# monomorphic): 1 hit there. The call through a variable: Pos.add_carry is
# called by APPLY2 on a closure, so it runs at entry.
chk normal.log -norec Normal
site normal.log Pos.add_carry 0 0
entry normal.log Pos.add_carry 4 0
site normal.log Pos.succ 1 0
entry normal.log Pos.succ 0 0
! grep -q "^binnum\[[0-9]*\] bind Normal\.padd" "$d/normal.log" || fail "Normal.padd is bound"

# (c) Around 64 bits: every call hits, at its call site.
chk edges.log -norec Edges
for r in Pos.add Pos.add_carry Pos.mul Z.pos_sub Z.pos_div_eucl Z.add Z.mul; do
  site edges.log "$r" "$(count_of EDGE "$r")" 0
  entry edges.log "$r" 0 0
done

# (d) Pos.add_carry (xO p) 1: per side of the lemma, the call site refuses
# (p is reached by the carry, 3 words), then the call's entry refuses again
# (3 words); the bytecode's Pos.succ p is then stuck, and its read-back
# refused at entry (1 word).
chk refuse.log -norec Refuse
site refuse.log Pos.add_carry 2 2
entry refuse.log Pos.add_carry 2 2
expect "refuse Pos.add_carry site-words" "$(stat refuse.log Pos.add_carry site-words)" -eq 6
expect "refuse Pos.add_carry entry-words" "$(stat refuse.log Pos.add_carry entry-words)" -eq 6
entry refuse.log Pos.succ 2 2

# (e) Recognition off, and -j 2.
for lib in Forms Normal Edges Refuse; do
  ROCQ_VM_BINNUM=0 chk "off-$lib.log" -norec "$lib"
  expect "$lib off binds" "$(line_stat "off-$lib.log" recognizer binds)" -eq 0
  expect "$lib off call-site binds" "$(line_stat "off-$lib.log" call-sites binds)" -eq 0
  for r in Pos.add_carry Pos.add Pos.mul Z.add; do
    expect "$lib off $r calls" "$(stat "off-$lib.log" "$r" calls)" -eq 0
  done
done
chk j2.log -j 2 -norec Edges
for r in Pos.add Pos.add_carry Pos.mul Z.pos_sub Z.pos_div_eucl Z.add Z.mul; do
  expect "-j 2 $r site hits" "$(stat j2.log "$r" site-calls)" -eq "$(count_of EDGE "$r")"
done
pids=$(awk '$2 == "routine" { print $1 }' "$d/j2.log" | sort -u | wc -l)
expect "-j 2 processes that print counters" "$pids" -ge 3

exit 0
