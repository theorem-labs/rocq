#!/usr/bin/env bash
# The comparison routines of the BINNUM family read exactly the nodes that
# the bytecode of their reference inspects, and no more: the scrutinee of
# each SWITCH, and the structural argument that GRABREC tests at every entry
# of a fixpoint, including the first one, since BINNUMCALL runs before it.
# PUSHFIELDS and GETFIELD copy a field without reading its tag, so the nodes
# below a comparison's last SWITCH are not inspected, and may be anything,
# such as a free variable. See misc/rocqchk_binnum*.sh for the routines.
#
# The inspection order, from the stock bodies (kernel/vmbinnum.ml):
#  - Pos.compare_cont r x y {struct y}: at each level, GRABREC's test of y,
#    then the node of x, then the node of y (every branch on x matches y).
#    It stops at the first level where x or y is xH. r is never matched; it
#    is the result when both numbers end together with no difference.
#  - Pos.eqb p q {struct q}: at each level, GRABREC's test of q, the node of
#    p, the node of q. It stops at the first level whose nodes differ, or
#    where both are xH.
#  - Z.compare x y: the node of x, the node of y, and when both have the
#    same sign Pos.compare (compare_cont Eq) of their magnitudes. Z.leb and
#    Z.ltb match the result of Z.compare. Z.eqb: the node of x, the node of
#    y, and Pos.eqb of the magnitudes when both are Zpos or both Zneg.
#  - Nat.eqb and Nat.leb, unchanged by this, are in misc/rocqchk_binnum.sh.
#
# ROCQ_VM_BINNUM_STATS=1 prints, for each routine, its calls, refusals and
# words read, at function entry (entry-*) and at call sites (site-*):
#  (a) lemmas whose part that the bytecode does not inspect is a free
#      variable, at a call site (Hit) and at function entry through a
#      variable (HitE): each is a hit, and checks as with ROCQ_VM_BINNUM=0;
#  (b) closed lemmas over a 65-node chain that the bytecode builds, too wide
#      to pack: the exact words read at each call (Wide, WideE), with the
#      literals as chains on every build, and as packed blocks where the
#      toolchain says packing is compiled in, which the build must confirm;
#  (c) lemmas where a node that the bytecode inspects is a free variable,
#      at a call site and at entry: the exact refusals (Stuck); and casts of
#      such stuck terms to the value a routine would give had it not read
#      that node, which coqc must refuse;
#  (d) the earlier differential tests against cbv stay in
#      misc/rocqchk_binnum*.sh.
# Every library is also checked with ROCQ_VM_BINNUM=-packlit, which makes
# the literals chains, as on a build where packing is compiled out (32-bit,
# OCaml 5): the calls, hits and refusals of (a) and (c) are the same.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

python3 - "$d" <<'PY'
import sys
d = sys.argv[1]

def pos(n):
    t = "xH"
    for c in bin(n)[3:]:
        t = "(%s %s)" % ("xI" if c == "1" else "xO", t)
    return t

HEADER = """Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef.
(* A call through a variable is not a call site of the routine: the
   function runs from its entry. *)
Definition through2 {A B C} (f : A -> B -> C) (x : A) (y : B) := f x y.
Definition through3 {A B C D} (f : A -> B -> C -> D) (x : A) (y : B) (z : C) := f x y z.
(* 2^n, built by the bytecode at check time: a chain of n + 1 nodes, which
   no literal packing reaches. *)
Fixpoint pw (n : nat) : positive := match n with O => xH | S n => xO (pw n) end.
"""

counts = {}
def count(key, n=1):
    counts[key] = counts.get(key, 0) + n

# (a) The part the bytecode does not inspect is a free variable. [binders]
# are the lemma's variables; [args] the routine's arguments; [rhs] the
# value. The literals 2, 3 and 5 are packed blocks where packing is compiled
# in and chains elsewhere; the terms with a variable are chains built at
# check time. No assertion of (a) depends on which.
HITS = [
    # compare_cont: x ends at level 1 (xH against y's xO); p is never read.
    ("Pos.compare_cont", "(p : positive)", ["Eq", pos(3), "(xO (xO p))"], "Lt"),
    # y ends at level 1; p is below x's node there.
    ("Pos.compare_cont", "(p : positive)", ["Lt", "(xO (xO p))", pos(3)], "Gt"),
    # r is not read when the numbers differ (before this slice the routine
    # read r first, and refused a free one). Each exit of pos_compare_core
    # that does not return r: two packed rests that differ, or 3 and 2 as
    # chains (the first level differs, then both end); x ends first; y ends
    # first; and chains that the bytecode builds, so that even with packing
    # on the walk stays in chain mode (pw 0 is xH).
    ("Pos.compare_cont", "(c : comparison)", ["c", pos(3), pos(2)], "Gt"),
    ("Pos.compare_cont", "(c : comparison) (p : positive)", ["c", "xH", "(xO p)"], "Lt"),
    ("Pos.compare_cont", "(c : comparison) (p : positive)", ["c", "(xO p)", "xH"], "Gt"),
    ("Pos.compare_cont", "(c : comparison)", ["c", "(xI (pw 0))", "(xO (pw 0))"], "Gt"),
    # eqb: a mismatch at level 0, then at level 1, with variables below.
    ("Pos.eqb", "(p q : positive)", ["(xI p)", "(xO q)"], "false"),
    ("Pos.eqb", "(p q : positive)", ["(xO (xI p))", "(xO (xO q))"], "false"),
    ("Pos.eqb", "(q : positive)", ["xH", "(xO q)"], "false"),
    ("Pos.eqb", "(p : positive)", ["(xI p)", "xH"], "false"),
    # Z.compare: the same sign, and Pos.compare stops at level 1; different
    # signs read no magnitude; Zneg goes through CompOpp.
    ("Z.compare", "(p : positive)", ["(Zpos %s)" % pos(3), "(Zpos (xO (xO p)))"], "Lt"),
    ("Z.compare", "(p q : positive)", ["(Zneg p)", "(Zpos q)"], "Lt"),
    ("Z.compare", "(p : positive)", ["Z0", "(Zneg p)"], "Gt"),
    ("Z.compare", "(p : positive)", ["(Zneg %s)" % pos(3), "(Zneg (xO (xO p)))"], "Gt"),
    ("Z.leb", "(p : positive)", ["(Zpos %s)" % pos(3), "(Zpos (xO (xO p)))"], "true"),
    ("Z.leb", "(p : positive)", ["(Zpos (xO (xO p)))", "(Zpos %s)" % pos(3)], "false"),
    ("Z.ltb", "(p : positive)", ["(Zpos %s)" % pos(3), "(Zpos (xO (xO p)))"], "true"),
    # The literal 5, and the chain's variable lies past where the comparison
    # stops (level 2 of 4).
    ("Z.ltb", "(p : positive)", ["(Zpos %s)" % pos(5), "(Zpos (xO (xO (xO (xO p)))))"], "true"),
    ("Z.ltb", "(p q : positive)", ["(Zneg p)", "(Zpos q)"], "true"),
    ("Z.eqb", "(p q : positive)", ["(Zpos (xI p))", "(Zpos (xO q))"], "false"),
    ("Z.eqb", "(p q : positive)", ["(Zneg p)", "(Zpos q)"], "false"),
    ("Z.eqb", "(p : positive)", ["(Zneg (xO (xI p)))", "(Zneg (xO (xO %s)))" % pos(3)], "false"),
]

def through(args):
    return "through3" if len(args) == 3 else "through2"

site, entry = [HEADER], [HEADER]
for i, (r, binders, args, rhs) in enumerate(HITS):
    site.append("Lemma h%d %s : %s %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
                % (i, binders, r, " ".join(args), rhs))
    entry.append("Lemma h%d %s : %s %s %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
                 % (i, binders, through(args), r, " ".join(args), rhs))
    count("HIT_" + r.replace(".", "_"))
open(d + "/Hit.v", "w").write("".join(site))
open(d + "/HitE.v", "w").write("".join(entry))

# (b) Closed, over a 65-node chain built at check time, with the exact words
# each call reads: one per chain node it inspects, one per packed block it
# enters, and none for the bits of a packed block. [chain] is the count when
# the literals 3 and 6, Zpos 3, Zpos 6 and Zneg 3 are chains: under
# ROCQ_VM_BINNUM=-packlit, and on every build where packing is compiled out
# (32-bit, OCaml 5). [packed] is the count when they are packed blocks. A
# routine that read the rest of the 65-node chain, as before this slice,
# reads about 60 words more.
WIDE = [
    # Packed: the block of 3 (1); y: xO (1), then xO (1), where x is xH.
    # Chains: xI, xO; xH, xO.
    ("Pos.compare_cont", ["Eq", pos(3), "(pw 64)"], "Lt", 3, 4),
    # pw 64 = xO^64 xH against 6 = xO (xI xH). Packed: xO (1), the block of
    # 6 (1); then xO (1) against the bit 1 of 6, a mismatch. Chains: xO, xO;
    # xO, xI.
    ("Pos.eqb", ["(pw 64)", pos(6)], "false", 3, 4),
    # The node of x and of y (2), then as compare_cont above, where the block
    # of 3 is the Zpos node's, and its bits cost nothing: xO, xO (2). Chains:
    # the two Z nodes, then two levels of two (4).
    ("Z.ltb", ["(Zpos %s)" % pos(3), "(Zpos (pw 64))"], "true", 4, 6),
    ("Z.leb", ["(Zpos (pw 64))", "(Zpos %s)" % pos(3)], "false", 4, 6),
    ("Z.compare", ["(Zpos %s)" % pos(3), "(Zpos (pw 64))"], "Lt", 4, 6),
    # The node of x, Zpos (1); the packed Zpos 6 (1); then xO (1) against
    # bit 0 of 6, xO (1) against bit 1, a mismatch. Chains: 2 + 2 + 2.
    ("Z.eqb", ["(Zpos (pw 64))", "(Zpos %s)" % pos(6)], "false", 4, 6),
    # Different signs: the two nodes only, as before this slice.
    ("Z.compare", ["(Zpos (pw 64))", "(Zneg %s)" % pos(3)], "Gt", 2, 2),
]
site, entry = [HEADER], [HEADER]
for i, (r, args, rhs, packed, chain) in enumerate(WIDE):
    site.append("Lemma w%d : %s %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
                % (i, r, " ".join(args), rhs))
    entry.append("Lemma w%d : %s %s %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
                 % (i, through(args), r, " ".join(args), rhs))
    count("WIDE_" + r.replace(".", "_"))
    count("WIDEP_" + r.replace(".", "_"), packed)
    count("WIDEC_" + r.replace(".", "_"), chain)
open(d + "/Wide.v", "w").write("".join(site))
open(d + "/WideE.v", "w").write("".join(entry))

# (c) A node that the bytecode inspects is a free variable: each side of
# the equation is stuck there. The two sides differ in syntax only, so the
# conversion evaluates both.
STUCK = """
Definition one := xH.
Definition idp (x : positive) := x.
(* compare_cont: x is xH at level 0, and y is the variable q, which the
   first GRABREC tests and the SWITCH on y reads. *)
Lemma s0 (q : positive) : Pos.compare_cont Eq xH q = Pos.compare_cont Eq one q.
Proof. vm_cast_no_check (@eq_refl _ (Pos.compare_cont Eq xH q)). Qed.
(* eqb: level 0 matches; at level 1 both are variables. *)
Lemma s1 (p q : positive) : Pos.eqb (xI p) (xI q) = Pos.eqb (xI p) (xI (idp q)).
Proof. vm_cast_no_check (@eq_refl _ (Pos.eqb (xI p) (xI q))). Qed.
(* Z.ltb: level 1 of the magnitudes, x is xH and y is q. *)
Lemma s2 (q : positive) : Z.ltb (Zpos (xI xH)) (Zpos (xI q)) = Z.ltb (Zpos (xI one)) (Zpos (xI q)).
Proof. vm_cast_no_check (@eq_refl _ (Z.ltb (Zpos (xI xH)) (Zpos (xI q)))). Qed.
(* r is the result of the equal path, a free variable: the routine reads it
   there, and refuses; the bytecode returns it. *)
Lemma s3 (c : comparison) : Pos.compare_cont c (xI xH) (xI xH) = c.
Proof. vm_cast_no_check (@eq_refl _ c). Qed.
(* Z.eqb, through Pos.eqb on the magnitudes: level 1, x is xH and y is q. *)
Lemma s4 (q : positive) : Z.eqb (Zpos (xI xH)) (Zpos (xI q)) = Z.eqb (Zpos (xI one)) (Zpos (xI q)).
Proof. vm_cast_no_check (@eq_refl _ (Z.eqb (Zpos (xI xH)) (Zpos (xI q)))). Qed.
(* Z.leb, as s2. *)
Lemma s5 (q : positive) : Z.leb (Zpos (xI xH)) (Zpos (xI q)) = Z.leb (Zpos (xI one)) (Zpos (xI q)).
Proof. vm_cast_no_check (@eq_refl _ (Z.leb (Zpos (xI xH)) (Zpos (xI q)))). Qed.
"""
# The values a routine would give had it not inspected the variable. coqc
# must refuse each cast, since the term is stuck.
FAILS = """
Fail Definition f0 (q : positive) := (@eq_refl comparison Lt <: Pos.compare_cont Eq xH q = Lt).
Fail Definition f1 (p q : positive) := (@eq_refl bool true <: Pos.eqb (xI p) (xI q) = true).
Fail Definition f2 (p q : positive) := (@eq_refl bool false <: Pos.eqb (xI p) (xI q) = false).
Fail Definition f3 (q : positive) := (@eq_refl bool true <: Z.ltb (Zpos (xI xH)) (Zpos (xI q)) = true).
Fail Definition f4 (q : positive) := (@eq_refl comparison Gt <: Pos.compare_cont Eq (xO xH) q = Gt).
"""
open(d + "/Stuck.v", "w").write(HEADER + STUCK + FAILS)

with open(d + "/counts", "w") as f:
    for k, v in sorted(counts.items()):
        f.write("%s=%d\n" % (k, v))
PY
. "$d/counts"

LIBS="Hit HitE Wide WideE Stuck"
for lib in $LIBS; do
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

expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

ROUTINES="Pos.compare_cont Pos.eqb Z.compare Z.leb Z.ltb Z.eqb"
key() { echo "$1_$(echo "$2" | tr . _)"; }

# field LOG LINE FIELD: the value of FIELD on the line LINE, as printed.
field() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) { print kv[2]; exit } } }' "$d/$1"
}

for lib in $LIBS; do chk "$lib.log" -norec "$lib"; done
# The same with the literals as chains, as on a build where packing is
# compiled out: what the routines inspect, and so their calls, hits and
# refusals, do not depend on it.
for lib in $LIBS; do ROCQ_VM_BINNUM=-packlit chk "$lib-chain.log" -norec "$lib"; done

# The state of packing, which is compiled out on a 32-bit build and with
# OCaml 5 or later (kernel/byterun/rocq_binnum.h). The expected state is
# read from the toolchain, so that a wrongly compiled-out build still fails
# (as in misc/rocqchk_binnum_literal.sh).
packing=$(field Wide.log packed packing)
literals=$(field Wide.log packed packing-literals)
config=$( { ocamlfind ocamlc -config || ocamlc -config; } 2>/dev/null || true)
word=$(printf '%s\n' "$config" | awk '$1 == "word_size:" { print $2 }')
major=$(printf '%s\n' "$config" | awk '$1 == "version:" { split($2, v, "."); print v[1] }')
if [ -z "$word" ] || [ -z "$major" ]; then want=$packing
elif [ "$word" = 64 ] && [ "$major" -lt 5 ]; then want=on
else want=off; fi
expect "the packing of results" "$packing" = "$want"
expect "the packing of literals" "$literals" = "$want"

# (a) Every lemma is a hit, at its call site (Hit) or at the routine's
# entry (HitE), and runs nothing else of the family; with the literals as
# they come and as chains.
for sfx in "" -chain; do
  for r in $ROUTINES; do
    k=$(key HIT "$r")
    expect "(a) Hit$sfx $r site-calls" "$(stat "Hit$sfx.log" "$r" site-calls)" -eq "${!k:-0}"
    expect "(a) Hit$sfx $r site-refusals" "$(stat "Hit$sfx.log" "$r" site-refusals)" -eq 0
    expect "(a) Hit$sfx $r entry-calls" "$(stat "Hit$sfx.log" "$r" entry-calls)" -eq 0
    expect "(a) HitE$sfx $r entry-calls" "$(stat "HitE$sfx.log" "$r" entry-calls)" -eq "${!k:-0}"
    expect "(a) HitE$sfx $r entry-refusals" "$(stat "HitE$sfx.log" "$r" entry-refusals)" -eq 0
    expect "(a) HitE$sfx $r site-calls" "$(stat "HitE$sfx.log" "$r" site-calls)" -eq 0
  done
done
# The same lemmas with no routine: the bytecode alone checks them.
for lib in Hit HitE; do
  ROCQ_VM_BINNUM=0 chk "$lib-off.log" -norec "$lib"
done

# (b) The words read, exactly. With the literals as chains, on every build;
# with the literals as they come, the packed counts where packing is
# compiled in, and the chain counts where it is not.
wide() {
  local site=$1 entry=$2 prefix=$3 r k kw
  for r in $ROUTINES; do
    k=$(key WIDE "$r"); kw=$(key "$prefix" "$r")
    expect "(b) $site $r site-calls" "$(stat "$site" "$r" site-calls)" -eq "${!k:-0}"
    expect "(b) $site $r refusals" "$(stat "$site" "$r" refusals)" -eq 0
    expect "(b) $site $r site-words" "$(stat "$site" "$r" site-words)" -eq "${!kw:-0}"
    expect "(b) $entry $r entry-calls" "$(stat "$entry" "$r" entry-calls)" -eq "${!k:-0}"
    expect "(b) $entry $r entry-words" "$(stat "$entry" "$r" entry-words)" -eq "${!kw:-0}"
  done
}
wide Wide-chain.log WideE-chain.log WIDEC
if [ "$want" = on ]; then wide Wide.log WideE.log WIDEP
else wide Wide.log WideE.log WIDEC; fi

# (c) The stuck lemmas refuse, with these exact counts, with the literals as
# they come and as chains. Each lemma's cast makes the conversion evaluate
# its left side X three times and its right side X' once (the type of
# eq_refl is X = X, the statement X = X'), except s3, whose eq_refl is at
# the right side c: X once. In an evaluation:
#  - s0: compare_cont refuses at the call site (it reads x = xH and the
#    variable q), and GRABREC then finds q an accumulator, so the fixpoint
#    does not unfold and no entry runs: 4 site;
#  - s1: eqb refuses at the call site (level 1: p), GRABREC passes on xI q,
#    the entry refuses again, and the recursive call stops at GRABREC on q:
#    4 site, 4 entry;
#  - s2: Z.ltb refuses at its call site and at entry, Z.compare at its call
#    site in Z.ltb's body and at entry; Z.compare's body applies Pos.compare
#    (compare_cont Eq, a partial application, so no call site), whose entry
#    refuses (level 1: q), and the recursive call stops at GRABREC on q:
#    Z.ltb and Z.compare 4 site and 4 entry each, compare_cont 4 entry;
#  - s3: compare_cont refuses at the call site (the equal path reads r = c),
#    then at the entry of each of the two levels: 1 site, 2 entry;
#  - s4: Z.eqb refuses at its call site and at entry; its body calls Pos.eqb
#    on the magnitudes at a call site, which refuses (level 1: q), then at
#    the entry after GRABREC on xI q, and the recursive call stops at
#    GRABREC on q: Z.eqb 4 and 4, Pos.eqb 4 and 4 more;
#  - s5: as s2, with Z.leb: Z.leb 4 and 4, Z.compare and compare_cont 4
#    more each.
# The stuck fixpoints that the conversion meets are the same closure on
# both sides, so Vconv.conv_fix does not run their bodies. coqc refuses the
# Fail casts of Stuck.v, or its compilation above would have failed.
expect_stuck() {
  local log
  for log in Stuck.log Stuck-chain.log; do
    expect "(c) $log $1 site-calls" "$(stat "$log" "$1" site-calls)" -eq "$2"
    expect "(c) $log $1 site-refusals" "$(stat "$log" "$1" site-refusals)" -eq "$2"
    expect "(c) $log $1 entry-calls" "$(stat "$log" "$1" entry-calls)" -eq "$3"
    expect "(c) $log $1 entry-refusals" "$(stat "$log" "$1" entry-refusals)" -eq "$3"
  done
}
expect_stuck Pos.compare_cont 5 10
expect_stuck Pos.eqb 8 8
expect_stuck Z.ltb 4 4
expect_stuck Z.leb 4 4
expect_stuck Z.eqb 4 4
expect_stuck Z.compare 8 8

exit 0
