#!/usr/bin/env bash
# Every chain in the VM value of a structured constant (Const_val) is packed
# when the VM turns the constant into its value (Vmvalues.val_of_str_const,
# through rocq_binnum_pack_literal): a block of tag 246 and size 2, whose
# field 0 is the number of the chain and field 1 the chain itself (kernel/byterun/
# rocq_binnum.h). A routine reads field 0; SWITCH, PROJ and whd_val read
# field 1, so a literal never pays an expansion. See
# misc/rocqchk_binnum*.sh for the routines and for packed results.
#
# Each lemma states [e = c] where c was computed by cbv, which does not use
# the VM, and is proved by vm_compute (or by a VM cast), so that rocqchk
# recomputes e with its own bytecode. ROCQ_VM_BINNUM_STATS=1 prints the
# literals packed and their nodes, the expansions of packed blocks by
# SWITCH, whd_val and PROJ with the nodes they build, and, for each routine,
# its arguments that were a packed block or a chain over a packed tail:
#  (a) literal chains of 1, 60, 61, 62 and 200 nodes, of positive, Z (both
#      signs), N and nat, matched by bytecode: every expansion builds no
#      node, because the block keeps the chain;
#  (b) the same literals as the arguments of the routines: each reads them
#      as packed blocks or as chains over a packed tail (a chain of more
#      than 61 nodes keeps its outermost nodes and packs the rest);
#  (c) one literal shared by 40 code sites is packed once; literals inside a
#      pair, a list and an option; chains that end in 0%uint63 and in tt; a
#      user inductive of the shape of positive;
#  (d) a one-field primitive record, which PROJ reads with no SWITCH before
#      it: the true statement against cbv, the false one refused by coqc,
#      and a forged .vo of the false one refused by rocqchk;
#  (e) a primitive array literal: a get of a packed element, and a set
#      followed by a get;
#  (f) all of these with a minor heap of 4096 words, with the statistics
#      off, with ROCQ_VM_BINNUM=-packlit (no literal is packed), with
#      ROCQ_VM_BINNUM=-pack (no packed value at all) and with
#      ROCQ_VM_BINNUM=0;
#  (g) literals whose field 0 is a primitive float, with an immediate, a
#      block and a packed chain after it, and a cast between two of them
#      that differ in the block, refused; the probes of the review of
#      slice 5 (RevF2 crashed coqc and rocqchk, RevFlt4 proved False), and
#      a forged library of RevFlt4's false cast, refused by rocqchk; in
#      every mode, and whether packing is compiled in or not.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

python3 - "$d" <<'PY'
import random, sys

d = sys.argv[1]
rng = random.Random(20261029)

# A chain of k nodes is a positive of k + 1 bits; the packer packs a chain
# of 1 to 61 nodes, and otherwise the longest of its suffixes that it can.
LENGTHS = [1, 60, 61, 62, 200]

def pos(n):
    t = "xH"
    for c in bin(n)[3:]:
        t = "(%s %s)" % ("xI" if c == "1" else "xO", t)
    return t

def num(k):
    """A positive whose chain has k nodes."""
    return (1 << k) | rng.randrange(1 << k)

def nat(k):
    return "%d%%nat" % k

HEADER = """Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef Corelib.Init.Nat.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
Fixpoint walk (p : positive) : positive :=
  match p with xI q => xI (walk q) | xO q => xO (walk q) | xH => xH end.
Fixpoint depth (p : positive) : nat :=
  match p with xI q => S (depth q) | xO q => S (depth q) | xH => O end.
Definition zwalk (x : Z) : Z :=
  match x with Z0 => Z0 | Zpos p => Zpos (walk p) | Zneg p => Zneg (walk p) end.
Definition nwalk (x : N) : N :=
  match x with N0 => N0 | Npos p => Npos (walk p) end.
Fixpoint natwalk (n : nat) : nat :=
  match n with O => O | S m => S (natwalk m) end.
"""

def lemma(name, lhs):
    return ("Lemma %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))

# (a) Literal chains matched by bytecode. No routine runs here, so every
# packed block is a literal and every expansion keeps its chain.
out = [HEADER]
for k in LENGTHS:
    v = num(k)
    c = pos(v)
    out.append(lemma("wa%d" % k, "walk %s" % c))
    out.append(lemma("de%d" % k, "depth %s" % c))
    out.append(lemma("zp%d" % k, "zwalk (Zpos %s)" % c))
    out.append(lemma("zn%d" % k, "zwalk (Zneg %s)" % c))
    out.append(lemma("nn%d" % k, "nwalk (Npos %s)" % c))
    out.append(lemma("na%d" % k, "natwalk %s" % nat(k)))
out.append(lemma("z0", "zwalk Z0"))
out.append(lemma("n0", "nwalk N0"))
out.append(lemma("na0", "natwalk 0%nat"))
out.append(lemma("wxh", "walk xH"))
open(d + "/Lit.v", "w").write("".join(out))

# (b) The same literals as routine arguments.
out = [HEADER]
for k in LENGTHS:
    a, b = num(k), num(k)
    A, B = pos(a), pos(b)
    for lhs in ("Pos.add %s %s" % (A, B), "Pos.add_carry %s %s" % (A, B),
                "Pos.succ %s" % A, "Pos.pred_double %s" % A, "Pos.div2 %s" % A,
                "Pos.mul %s %s" % (A, B), "Pos.compare %s %s" % (A, B),
                "Pos.eqb %s %s" % (A, A), "Pos.eqb %s %s" % (A, B),
                "Pos.of_succ_nat %s" % nat(k),
                "Z.add (Zpos %s) (Zneg %s)" % (A, B),
                "Z.add (Zpos %s) (Zpos %s)" % (A, B),
                "Z.mul (Zneg %s) (Zpos %s)" % (A, B),
                "Z.compare (Zpos %s) (Zpos %s)" % (A, B),
                "Z.eqb (Zneg %s) (Zneg %s)" % (A, A),
                "Z.leb (Zpos %s) (Zpos %s)" % (A, B),
                "Z.ltb (Zneg %s) (Zpos %s)" % (A, B),
                "Z.double (Zpos %s)" % A, "Z.succ_double (Zneg %s)" % A,
                "Z.pred_double (Zpos %s)" % A, "Z.div2 (Zpos %s)" % A,
                "Z.div2 (Zneg %s)" % A, "Z.pos_sub %s %s" % (A, B),
                "Z.of_nat %s" % nat(k), "Nat.eqb %s %s" % (nat(k), nat(k)),
                "Nat.leb %s %s" % (nat(k), nat(k + 1)),
                "Nat.leb %s %s" % (nat(k + 1), nat(k)),
                "Z.pos_div_eucl %s (Zpos %s)" % (A, B)):
        out.append(lemma("g%d" % len(out), lhs))
# The smallest numbers: a packed Z of 2 or 3 is Zpos xH or Zneg xH, whose
# rest is the node xH (and not a number of 0).
for lhs in ("Z.div2 (Zpos xH)", "Z.div2 (Zneg xH)", "Z.double (Zpos xH)",
            "Z.succ_double (Zpos xH)", "Z.succ_double (Zneg xH)",
            "Z.pred_double (Zpos xH)", "Z.pred_double (Zneg xH)",
            "Z.add (Zpos xH) (Zneg xH)", "Z.add (Zpos xH) (Zpos xH)",
            "Z.mul (Zneg xH) (Zpos (xO xH))", "Z.mul (Zpos (xO xH)) (Zneg xH)",
            "Z.compare (Zpos xH) (Zneg xH)", "Z.eqb (Zpos xH) (Zpos xH)",
            "Z.pos_sub xH xH", "Z.pos_div_eucl xH (Zpos xH)",
            "Pos.div2 (xO xH)", "Pos.succ xH", "Pos.pred_double (xO xH)",
            "Pos.mul (xO xH) (xI xH)", "Pos.add xH xH", "Nat.eqb 1%nat 1%nat",
            "Nat.leb 1%nat 2%nat", "Z.of_nat 1%nat", "Pos.of_succ_nat 1%nat"):
    out.append(lemma("s%d" % len(out), lhs))
open(d + "/Arg.v", "w").write("".join(out))

# (c) One literal at 40 code sites, literals in a pair, a list and an
# option, chains that end in 0%uint63 and in tt, and a user inductive of
# the shape of positive.
out = [HEADER, """Require Import Corelib.Numbers.Cyclic.Int63.PrimInt63.
Inductive mypos := M1 (p : mypos) | M0 (p : mypos) | MH.
Fixpoint mwalk (p : mypos) : mypos :=
  match p with M1 q => M1 (mwalk q) | M0 q => M0 (mwalk q) | MH => MH end.
Inductive vint := V1 (i : int) | V0 (v : vint).
Fixpoint vget (v : vint) : int := match v with V1 i => i | V0 w => vget w end.
Inductive uend := U1 (u : unit) | U0 (v : uend).
Fixpoint uget (v : uend) : unit := match v with U1 u => u | U0 w => uget w end.
Definition fst_z (p : prod Z Z) : Z := match p with pair a _ => a end.
Fixpoint nth_z (l : list Z) (n : nat) : Z :=
  match l, n with nil, _ => Z0 | cons a _, O => a | cons _ l, S n => nth_z l n end.
Definition opt_z (o : option Z) : Z := match o with Some a => a | None => Z0 end.
"""]
shared = pos(num(40))
for i in range(40):
    out.append(lemma("sh%d" % i, "walk %s" % shared))
my = "MH"
for c in bin(num(30))[3:]:
    my = "(%s %s)" % ("M1" if c == "1" else "M0", my)
out.append(lemma("my", "mwalk %s" % my))
out.append(lemma("vi", "vget (V0 (V0 (V1 0%uint63)))"))
out.append(lemma("vi2", "vget (V0 (V1 7%uint63))"))
out.append(lemma("uu", "uget (U0 (U0 (U1 tt)))"))
a, b = pos(num(20)), pos(num(21))
out.append(lemma("pr", "fst_z (pair (Zpos %s) (Zneg %s))" % (a, b)))
out.append(lemma("li", "nth_z (cons (Zpos %s) (cons (Zneg %s) nil)) 1%%nat" % (a, b)))
out.append(lemma("op", "opt_z (Some (Zneg %s))" % a))
out.append(lemma("op2", "opt_z (@None Z)"))
out.append(lemma("zz", "Z.add (fst_z (pair (Zpos %s) Z0)) (Zpos %s)" % (a, b)))
open(d + "/Nest.v", "w").write("".join(out))

# (d) A one-field primitive record. Without the expansion in PROJ,
# w {| w := K T0 |} reads field 0 of the packed block, which is Val_long 7,
# that is T7.
REC = """Set Primitive Projections.
Inductive T := T0 | T1 | T2 | T3 | T4 | T5 | T6 | T7 | K (t : T).
Record W := { w : T }.
Record W2 := { w2 : W }.
"""
out = [HEADER, REC]
out.append(lemma("r0", "w {| w := K T0 |}"))
out.append(lemma("r1", "w {| w := K (K T0) |}"))
out.append(lemma("r2", "w {| w := K (K (K T1)) |}"))
out.append(lemma("r3", "w {| w := T7 |}"))
out.append(lemma("r4", "w (w2 {| w2 := {| w := K T0 |} |})"))
out.append("Fail Definition bad0 := (@eq_refl T T7 <: w {| w := K T0 |} = T7).\n")
out.append("Fail Definition bad1 := (@eq_refl T T3 <: w {| w := K (K T0) |} = T3).\n")
open(d + "/Rec.v", "w").write("".join(out))

# The forged case: ProjL states [w r = T7], which holds of the first ProjF
# and not of the second.
open(d + "/ProjF1.v", "w").write(REC + "Definition r : W := {| w := T7 |}.\n")
open(d + "/ProjF2.v", "w").write(REC + "Definition r : W := {| w := K T0 |}.\n")
open(d + "/ProjL.v", "w").write("""Require Import ProjF.
Lemma forged : w r = T7.
Proof. vm_cast_no_check (@eq_refl T T7). Qed.
""")

# (e) A primitive array literal.
out = [HEADER, """Require Import Corelib.Numbers.Cyclic.Int63.PrimInt63 Corelib.Array.PrimArray.
Open Scope uint63_scope.
"""]
e0, e1, e2 = pos(num(5)), pos(num(40)), pos(num(70))
arr = "[| %s; %s; %s | xH |]" % (e0, e1, e2)
out.append("Definition arr : array positive := %s.\n" % arr)
out.append(lemma("a0", "PrimArray.get arr 0"))
out.append(lemma("a1", "PrimArray.get arr 1"))
out.append(lemma("a2", "PrimArray.get arr 2"))
out.append(lemma("a3", "PrimArray.get arr 9"))
out.append(lemma("a4", "PrimArray.get (PrimArray.set arr 0 %s) 0" % pos(num(30))))
out.append(lemma("a5", "PrimArray.get (PrimArray.set arr 0 %s) 1" % pos(num(30))))
out.append(lemma("a6", "walk (PrimArray.get arr 1)"))
out.append(lemma("a7", "Pos.add (PrimArray.get arr 0) (PrimArray.get arr 1)"))
out.append(lemma("a8", "PrimArray.default arr"))
out.append(lemma("a9", "PrimArray.get (PrimArray.copy arr) 1"))
open(d + "/Arr.v", "w").write("".join(out))

# (g) Literals whose field 0 is a primitive float. On an OCaml build with
# flat float arrays, an array made by Array.init whose first element is a
# float is a flat float array, which stores every other element as a
# double: the walk of the packer must not put fields in one.
FLT = """From Corelib Require Import PrimFloat.
Inductive R3 := mk3 : float -> bool -> positive -> R3.
Inductive R4 := mk4 : float -> bool -> prod bool bool -> positive -> R4.
Definition f3 (x : R3) := match x with mk3 f _ _ => f end.
Definition b3 (x : R3) := match x with mk3 _ b _ => b end.
Definition p3 (x : R3) := match x with mk3 _ _ p => p end.
Definition f4 (x : R4) := match x with mk4 f _ _ _ => f end.
Definition b4 (x : R4) := match x with mk4 _ b _ _ => b end.
Definition q4 (x : R4) := match x with mk4 _ _ q _ => q end.
Definition p4 (x : R4) := match x with mk4 _ _ _ p => p end.
"""
out = [HEADER, FLT]
P, Q = pos(num(30)), pos(num(40))
for g in ("f3", "b3", "p3"):
    out.append(lemma("l%d" % len(out), "%s (mk3 1.5%%float true %s)" % (g, P)))
out.append(lemma("l%d" % len(out), "walk (p3 (mk3 2.5%%float false %s))" % P))
out.append(lemma("l%d" % len(out), "Pos.add (p3 (mk3 1.5%%float true %s)) %s" % (P, Q)))
for g in ("f4", "b4", "q4", "p4"):
    out.append(lemma("l%d" % len(out), "%s (mk4 1.5%%float true (pair true false) %s)" % (g, P)))
out.append("Definition r4a := mk4 1.5%%float true (pair true true) %s.\n" % P)
out.append("Definition r4b := mk4 1.5%%float true (pair true false) %s.\n" % P)
out.append(lemma("q4a", "q4 r4a"))
out.append("Fail Definition bad4 := (@eq_refl _ (q4 r4a) <: q4 r4a = q4 r4b).\n")
open(d + "/Flt.v", "w").write("".join(out))

# The two probes of the review of slice 5: RevF2 crashed the checker, and
# RevFlt4 proved False, which coqc must refuse.
open(d + "/RevF2.v", "w").write("""From Corelib Require Import PrimFloat.
Inductive R := mk : float -> bool -> nat -> R.
Definition r := mk 1.5%float true 2.
Definition get_b (x : R) := match x with mk _ b _ => b end.
Lemma lb : get_b r = true. Proof. vm_compute. reflexivity. Qed.
""")
FLT4 = """From Corelib Require Import PrimFloat.
Inductive R := mk : float -> (bool * bool) -> nat -> R.
Definition r1 := mk 1.5%%float (true, true) 2.
Definition r2 := mk 1.5%%float (true, %s) 2.
Definition get_b (x : R) := match x with mk _ b _ => b end.
"""
open(d + "/RevFlt4.v", "w").write(FLT4 % "false" + """
Definition bad : get_b r1 = get_b r2 := (@eq_refl _ (get_b r1) <: get_b r1 = get_b r2).
Lemma boom : False.
Proof. pose proof (f_equal snd bad) as H. cbv in H. discriminate H. Qed.
""")
# The same as a forged library: FltL holds of the first FltF (r2 = r1) and
# not of the second.
open(d + "/FltF1.v", "w").write(FLT4 % "true")
open(d + "/FltF2.v", "w").write(FLT4 % "false")
open(d + "/FltL.v", "w").write("""Require Import FltF.
Definition bad : get_b r1 = get_b r2 := (@eq_refl _ (get_b r1) <: get_b r1 = get_b r2).
""")
PY

LIBS="Lit Arg Nest Rec Arr Flt RevF2"
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

# line LOG LINE FIELD: FIELD of the line LINE, summed over every process.
line() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) s += kv[2] } }
    END { print s + 0 }' "$d/$1"
}

# field LOG LINE FIELD: the value of FIELD on the line LINE, as printed.
field() {
  awk -v l="$2:" -v f="$3" '$2 == l {
      for (i = 3; i <= NF; i++) { split($i, kv, "="); if (kv[1] == f) { print kv[2]; exit } } }' "$d/$1"
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

# forge F L: compiles L against F1.v as F, then F2.v as F, and patches the
# digest of F that L.vo records to the new one (the summary and library
# segments and their hashes), so that rocqchk checks L against an F that it
# was not compiled against.
forge() {
  local f=$1 l=$2
  cp "$d/${f}1.v" "$d/$f.v"
  rocq c -native-compiler no -R "$d" "" "$d/$f.v"
  rocq c -native-compiler no -R "$d" "" "$d/$l.v"
  cp "$d/$f.vo" "$d/${f}1.vo"
  cp "$d/${f}2.v" "$d/$f.v"
  rocq c -native-compiler no -R "$d" "" "$d/$f.v"
  python3 - "$d" "$f" "$l" <<'PY'
import hashlib, sys

d, f, l = sys.argv[1:4]

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

old = library_digest(open("%s/%s1.vo" % (d, f), "rb").read())
new = library_digest(open("%s/%s.vo" % (d, f), "rb").read())
data = bytearray(open("%s/%s.vo" % (d, l), "rb").read())
for name, pos, length, hash_at in segments(bytes(data)):
    if name not in ("summary", "library"):
        continue
    seg = bytes(data[pos:pos + length])
    if seg.count(old) == 0:
        raise SystemExit("the %s segment does not record the digest of %s" % (name, f))
    seg = seg.replace(old, new)
    digest = hashlib.md5(seg).digest()
    data[pos:pos + length] = seg
    data[pos + length:pos + length + 16] = digest
    data[hash_at:hash_at + 16] = digest
open("%s/%s.vo" % (d, l), "wb").write(bytes(data))
PY
}

# refused WHAT L MODE: rocqchk, in ROCQ_VM_BINNUM mode MODE ("on" for
# unset), refuses L with a type error.
refused() {
  local what=$1 l=$2 m=$3 v
  if [ "$m" = on ]; then v=; else v=$m; fi
  if env ${v:+ROCQ_VM_BINNUM=$v} rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$l" \
      > "$d/$l-forged-$m.log" 2>&1; then
    cat "$d/$l-forged-$m.log" >&2
    fail "$what rocqchk accepted the forged $l ($m)"
  fi
  grep -q "Type error" "$d/$l-forged-$m.log" \
    || { cat "$d/$l-forged-$m.log" >&2; fail "$what rocqchk refused the forged $l for another reason ($m)"; }
}

MODES="on -pack -packlit 0"

for lib in $LIBS; do chk "$lib.log" -norec "$lib"; done
for lib in $LIBS; do
  expect "$lib refusals" "$(total "$lib.log" refusals)" -eq 0
done

# (g) Literals whose field 0 is a primitive float, and the two probes of
# the review. The walk of the packer runs whether packing is compiled in or
# not, and in every mode, so this runs everywhere: coqc compiles Flt.v and
# RevF2.v and refuses RevFlt4.v (which proves False if a field is
# rewritten), and rocqchk checks Flt and RevF2 and refuses the forged FltL,
# in every mode.
for m in $MODES; do
  if [ "$m" = on ]; then v=; else v=$m; fi
  for lib in Flt RevF2; do
    env ${v:+ROCQ_VM_BINNUM=$v} rocq c -native-compiler no -R "$d" "" "$d/$lib.v" \
      > "$d/$lib-coqc-$m.log" 2>&1 || { cat "$d/$lib-coqc-$m.log" >&2; fail "(g) coqc $lib.v ($m) failed"; }
    env ${v:+ROCQ_VM_BINNUM=$v} rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" \
      > "$d/$lib-chk-$m.log" 2>&1 || { cat "$d/$lib-chk-$m.log" >&2; fail "(g) rocqchk $lib ($m) failed"; }
  done
  if env ${v:+ROCQ_VM_BINNUM=$v} rocq c -native-compiler no -R "$d" "" "$d/RevFlt4.v" \
      > "$d/RevFlt4-coqc-$m.log" 2>&1; then
    cat "$d/RevFlt4-coqc-$m.log" >&2
    fail "(g) coqc accepted RevFlt4.v ($m)"
  fi
  grep -q 'has type' "$d/RevFlt4-coqc-$m.log" \
    || { cat "$d/RevFlt4-coqc-$m.log" >&2; fail "(g) coqc refused RevFlt4.v for another reason ($m)"; }
done
forge FltF FltL
for m in $MODES; do refused "(g)" FltL "$m"; done
cp "$d/FltF1.v" "$d/FltF.v"
rocq c -native-compiler no -R "$d" "" "$d/FltF.v"
rocq c -native-compiler no -R "$d" "" "$d/FltL.v"
chk "FltL-good.log" -norec FltL

# The state of packing, which is compiled out on a 32-bit build and with
# OCaml 5 or later (kernel/byterun/rocq_binnum.h). The expected state is
# read from the toolchain, so that a wrongly compiled-out build still fails.
packing=$(field Lit.log packed packing)
literals=$(field Lit.log packed packing-literals)
config=$( { ocamlfind ocamlc -config || ocamlc -config; } 2>/dev/null || true)
word=$(printf '%s\n' "$config" | awk '$1 == "word_size:" { print $2 }')
major=$(printf '%s\n' "$config" | awk '$1 == "version:" { split($2, v, "."); print v[1] }')
if [ -z "$word" ] || [ -z "$major" ]; then want=$packing
elif [ "$word" = 64 ] && [ "$major" -lt 5 ]; then want=on
else want=off; fi
expect "the packing of results" "$packing" = "$want"
expect "the packing of literals" "$literals" = "$want"

if [ "$want" = off ]; then
  # Nothing is packed: the lemmas above still hold, and every count is 0.
  for lib in $LIBS; do
    expect "$lib literals" "$(line "$lib.log" packed literals)" -eq 0
    expect "$lib switch expansions" "$(line "$lib.log" packed switch-expansions)" -eq 0
    expect "$lib proj expansions" "$(line "$lib.log" packed proj-expansions)" -eq 0
    expect "$lib packed arguments" "$(total "$lib.log" args-packed)" -eq 0
  done
  exit 0
fi

# (a) Literals are matched through their kept chains: every expansion
# builds no node at all, and no routine runs.
expect "(a) literals" "$(line Lit.log packed literals)" -gt 0
expect "(a) literal nodes" "$(line Lit.log packed literal-nodes)" -gt 0
expect "(a) switch expansions" "$(line Lit.log packed switch-expansions)" -gt 0
expect "(a) switch nodes" "$(line Lit.log packed switch-nodes)" -eq 0
expect "(a) whd nodes" "$(line Lit.log packed whd-nodes)" -eq 0
expect "(a) calls" "$(total Lit.log calls)" -eq 0

# (b) Each routine read literals as packed blocks, or as chains over a
# packed tail for the chains of more than 61 nodes.
for r in Pos.add Pos.add_carry Pos.succ Pos.pred_double Pos.div2 Pos.mul \
         Pos.compare_cont Pos.eqb Pos.of_succ_nat Z.add Z.mul Z.compare Z.eqb \
         Z.leb Z.ltb Z.double Z.succ_double Z.pred_double Z.div2 Z.pos_sub \
         Z.of_nat Z.pos_div_eucl Nat.eqb Nat.leb; do
  expect "(b) $r hits" "$(stat Arg.log "$r" hits)" -gt 0
  expect "(b) $r packed arguments" \
    "$(( $(stat Arg.log "$r" args-packed) + $(stat Arg.log "$r" args-tail) ))" -gt 0
done
expect "(b) chains over a packed tail" "$(total Arg.log args-tail)" -gt 0

# (c) The 40 code sites share one slot (Vmsymtable.slot_for_str_cst), so
# the literal is packed once, not 40 times.
expect "(c) literals" "$(line Nest.log packed literals)" -gt 0
expect "(c) literals of 40 sites" "$(line Nest.log packed literals)" -lt 20
expect "(c) switch nodes" "$(line Nest.log packed switch-nodes)" -eq 0

# (d) PROJ read packed literals, through their kept chains.
expect "(d) proj expansions" "$(line Rec.log packed proj-expansions)" -gt 0
expect "(d) proj nodes" "$(line Rec.log packed proj-nodes)" -eq 0

# (d) The forged library: ProjL is checked against the ProjF that makes it
# false. Only the VM conversion of [w r] against T7 tells the two apart, so
# rocqchk must refuse it. A PROJ that read field 0 of the packed block would
# accept it.
forge ProjF ProjL
for m in $MODES; do refused "(d)" ProjL "$m"; done
cp "$d/ProjF1.v" "$d/ProjF.v"
rocq c -native-compiler no -R "$d" "" "$d/ProjF.v"
rocq c -native-compiler no -R "$d" "" "$d/ProjL.v"
chk "ProjL-good.log" -norec ProjL

# (e) The elements of an array literal are packed, and get and set read
# them.
expect "(e) literals" "$(line Arr.log packed literals)" -gt 0
expect "(e) packed or tail arguments" \
  "$(( $(total Arr.log args-packed) + $(total Arr.log args-tail) ))" -gt 0

# (g) The positive fields of the float literals are packed.
expect "(g) Flt literals" "$(line Flt.log packed literals)" -gt 0

# (f) A minor heap of 4096 words; the statistics off; the packing of
# literals off; no packing at all.
for lib in $LIBS; do
  OCAMLRUNPARAM=s=4096 chk "$lib-small.log" -norec "$lib"
  expect "(f) $lib small heap refusals" "$(total "$lib-small.log" refusals)" -eq 0
  rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" > "$d/$lib-nostats.log" 2>&1 \
    || { cat "$d/$lib-nostats.log" >&2; fail "rocqchk -norec $lib without statistics failed"; }
  ! grep -q "^binnum\[" "$d/$lib-nostats.log" || fail "(f) $lib printed statistics"
  ROCQ_VM_BINNUM=-packlit chk "$lib-nolit.log" -norec "$lib"
  expect "(f) $lib -packlit literals" "$(line "$lib-nolit.log" packed literals)" -eq 0
  expect "(f) $lib -packlit proj expansions" "$(line "$lib-nolit.log" packed proj-expansions)" -eq 0
  expect "(f) $lib -packlit refusals" "$(total "$lib-nolit.log" refusals)" -eq 0
  ROCQ_VM_BINNUM=-pack chk "$lib-nopack.log" -norec "$lib"
  expect "(f) $lib -pack literals" "$(line "$lib-nopack.log" packed literals)" -eq 0
  expect "(f) $lib -pack packed arguments" "$(total "$lib-nopack.log" args-packed)" -eq 0
  expect "(f) $lib -pack refusals" "$(total "$lib-nopack.log" refusals)" -eq 0
  ROCQ_VM_BINNUM=0 chk "$lib-off.log" -norec "$lib"
  expect "(f) $lib off calls" "$(total "$lib-off.log" calls)" -eq 0
done

exit 0
