#!/usr/bin/env bash
# rocqchk runs the arithmetic of Corelib's binary numbers (Pos.succ, add,
# add_carry, pred_double, mul, div2, of_succ_nat; Z.double, succ_double,
# pred_double, pos_sub, add, mul, compare, leb, ltb, eqb, div2, of_nat,
# pos_div_eucl; Nat.eqb, leb) as C routines, through the BINNUM instruction
# (kernel/vmbinnum.ml, kernel/byterun/rocq_binnum.c), when it recognizes their
# bodies and the bodies of the constants they call. See also
# misc/rocqchk_binnum.sh, for the comparisons of the first slice.
#
# Each lemma states [f a b = c] where c was computed by cbv, which does not
# use the VM, and is proved by vm_compute, so that rocqchk recomputes [f a b]
# with its own bytecode. coqc's own vm_compute runs Corelib's stored code,
# which has no BINNUM. The counters that ROCQ_VM_BINNUM_STATS=1 prints at the
# exit of every process show which code ran:
#  (a) the Corelib functions, with random and edge inputs (numbers of more
#      than 64 and 128 bits, zero and negative Z, equal operands, divisors 1
#      and larger than the dividend): one call per lemma, every call a hit;
#  (b) ROCQ_VM_BINNUM=0: nothing is bound and no routine runs;
#      ROCQ_VM_BINNUM=-Pos.succ turns off only that routine;
#  (c) copies over Corelib's types (as Stdlib's), over user inductives of the
#      same shapes, and through aliases, bind, and their results are right;
#  (d) copies with one branch changed, a copy that calls one of these, a
#      copy whose callee is opaque, a copy whose callee is another function
#      of the expected callee's block (Pos.add_carry for Pos.add), and copies
#      with one variable changed in a let value or a let body, do not bind,
#      for the reason given, and their own results still check;
#  (e) inputs with a free variable: the routine reads what the bytecode
#      reads, refuses where it finds the variable, and shares what it does
#      not read; one probe for each refusal guard of each routine (depth 1,
#      and depth 70 for the numbers read into limbs); refusals where the
#      bytecode still computes a constructor; a refused call of pos_div_eucl
#      falls back to the bytecode, whose callees hit; a partial application
#      hits; exact counts, at function entry and at call sites;
#  (f) the -j 2 run of (a): each worker prints its own counters;
#  (g) large numbers with a 4096-word minor heap, so that the allocation of
#      the results runs the GC many times, also for chains built over a
#      young subterm of an argument;
#  (h) the packing of literals on: the same calls and refusals. The words
#      of (a) to (g) are those of chain literals, so those checks run with
#      ROCQ_VM_BINNUM=-packlit.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQ_VM_BINNUM ROCQ_VM_BINNUM_STATS OCAMLRUNPARAM

d=$(mktemp -d)

python3 - "$d" <<'PY'
import random, sys

d = sys.argv[1]
rng = random.Random(20261025)

def bits(k):
    """A random number of exactly k bits."""
    return 1 if k == 1 else rng.randrange(1 << (k - 1), 1 << k)

def rpos(lo=1, hi=200):
    return bits(rng.randint(lo, hi))

def chain(n, i, o, h):
    """The positive n, most significant bit inside: (i (o h)) is 5."""
    t = h
    for c in bin(n)[3:]:
        t = "(%s %s)" % (i if c == "1" else o, t)
    return t

def pos(n): return chain(n, "xI", "xO", "xH")
def upos(n): return chain(n, "pI", "pO", "pH")
def z(n): return "Z0" if n == 0 else "(Zpos %s)" % pos(n) if n > 0 else "(Zneg %s)" % pos(-n)
def uz(n): return "uZ0" if n == 0 else "(uZpos %s)" % upos(n) if n > 0 else "(uZneg %s)" % upos(-n)
def nat(n): return "(%d)%%nat" % n
def unat(n):
    t = "nO"
    for _ in range(n): t = "(nS %s)" % t
    return t

HEADER = """Require Import Corelib.BinNums.PosDef Corelib.BinNums.IntDef.
Abbreviation cbv_val t := ltac:(let v := eval cbv in t in exact v) (only parsing).
"""

def lemma(name, lhs):
    return ("Lemma %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, lhs, lhs))

# Inputs.
POSE = [1, 2, 3, 4, 5, 6, 7, 8]
for k in (31, 32, 33, 63, 64, 65, 128, 129, 200):
    POSE += [(1 << k) - 1, 1 << k, (1 << k) + 1, bits(k)]
ZE = [0, 1, -1, 2, -2, 3, -3]
for k in (32, 64, 65, 128, 129):
    for n in ((1 << k) - 1, 1 << k, (1 << k) + 1, bits(k)):
        ZE += [n, -n]
NATE = [0, 1, 2, 3, 31, 32, 63, 64, 65, 127, 128, 129, 255, 256, 1000]

def pos_pairs(nrandom):
    p = [(1, 1), (1, 2), (2, 1), (3, 3), (1, 7), (7, 1)]
    for k in (32, 64, 65, 128, 200):
        a, b = bits(k), bits(k)
        p += [(a, b), ((1 << k) - 1, 1), (1, (1 << k) - 1), ((1 << k) - 1, (1 << k) - 1),
              (a, 3), (3, a), (a, 1 << 40), (1 << 40, a), (a, a)]
    for _ in range(nrandom):
        p.append((rpos(), rpos()))
    return p

def z_pairs(nrandom):
    small = [0, 1, -1, 5, -5, (1 << 64) + 3, -((1 << 64) + 3), bits(130), -bits(130)]
    p = [(a, b) for a in small for b in small]
    for _ in range(nrandom):
        a = rng.choice([0, 1, -1]) * rpos(1, 150)
        b = rng.choice([a, -a, rng.choice([0, 1, -1]) * rpos(1, 150)])
        p.append((a, b))
    return p

def div_pairs(nrandom):
    p = []
    for a in (1, 2, 3, 7, bits(64), bits(65), bits(200)):
        p.append((a, 1))
    for b in (2, 3, 1 << 31, (1 << 32) - 1, 1 << 32, (1 << 32) + 1, bits(64), bits(65), bits(128), bits(200)):
        p += [(max(1, b - 1), b), (b, b), (b * 5, b), (b * bits(70) + bits(20) % b or 1, b), (bits(250), b)]
    for _ in range(nrandom):
        p.append((rpos(1, 260), rpos(1, 130)))
    return p

def nat_pairs(nrandom):
    p = [(0, 0), (0, 5), (5, 0), (5, 5), (5, 6), (6, 5), (100, 100), (1000, 999), (999, 1000)]
    for _ in range(nrandom):
        a = rng.randint(0, 1500)
        p.append((a, rng.choice([a, a + 1, a - 1 if a else 0, rng.randint(0, 1500)])))
    return p

counts = {}
def count(key, n=1):
    counts[key] = counts.get(key, 0) + n

# (a) The Corelib functions. Every lemma calls its function once.
out = [HEADER, "Local Open Scope positive_scope.\n"]
n = [0]
def add(routine, lhs):
    out.append(lemma("l%d" % n[0], lhs))
    n[0] += 1
    count("N_" + routine.replace(".", "_"))

for x in POSE + [rpos() for _ in range(30)]:
    add("Pos.succ", "Pos.succ %s" % pos(x))
    add("Pos.pred_double", "Pos.pred_double %s" % pos(x))
    add("Pos.div2", "Pos.div2 %s" % pos(x))
for a, b in pos_pairs(30):
    add("Pos.add", "Pos.add %s %s" % (pos(a), pos(b)))
    add("Pos.add_carry", "Pos.add_carry %s %s" % (pos(a), pos(b)))
for a, b in pos_pairs(20) + [(1 << 70, bits(90)), (bits(90), 1 << 70), ((1 << 64) - 1, (1 << 64) - 1)]:
    add("Pos.mul", "Pos.mul %s %s" % (pos(a), pos(b)))
for k in NATE + [rng.randint(0, 2000) for _ in range(15)]:
    add("Pos.of_succ_nat", "Pos.of_succ_nat %s" % nat(k))
    add("Z.of_nat", "Z.of_nat %s" % nat(k))
for x in ZE + [rng.choice([1, -1]) * rpos() for _ in range(20)]:
    add("Z.double", "Z.double %s" % z(x))
    add("Z.succ_double", "Z.succ_double %s" % z(x))
    add("Z.pred_double", "Z.pred_double %s" % z(x))
    add("Z.div2", "Z.div2 %s" % z(x))
for a, b in pos_pairs(20) + [(x, x) for x in POSE[:12]]:
    add("Z.pos_sub", "Z.pos_sub %s %s" % (pos(a), pos(b)))
for a, b in z_pairs(30):
    for f in ("add", "mul", "compare", "leb", "ltb", "eqb"):
        add("Z." + f, "Z.%s %s %s" % (f, z(a), z(b)))
for a, b in div_pairs(30):
    add("Z.pos_div_eucl", "Z.pos_div_eucl %s %s" % (pos(a), z(b)))
for a, b in nat_pairs(30):
    add("Nat.eqb", "Nat.eqb %s %s" % (nat(a), nat(b)))
    add("Nat.leb", "Nat.leb %s %s" % (nat(a), nat(b)))
open(d + "/Diff.v", "w").write("".join(out))

# Copies of the bodies, with the names of their types, constructors and
# callees as parameters.
SUCC_T = """
Fixpoint succ (x:@pos@) : @pos@ :=
  match x with
    | @xI@ p => @xO@ (succ p)
    | @xO@ p => @xI@ p
    | @xH@ => @xO@ @xH@
  end.
"""

ADD_T = """
Fixpoint add (x y:@pos@) : @pos@ :=
  match x, y with
    | @xI@ p, @xI@ q => @xO@ (add_carry p q)
    | @xI@ p, @xO@ q => @xI@ (add p q)
    | @xI@ p, @xH@ => @xO@ (@succ@ p)
    | @xO@ p, @xI@ q => @xI@ (add p q)
    | @xO@ p, @xO@ q => @xO@ (add p q)
    | @xO@ p, @xH@ => @xI@ p
    | @xH@, @xI@ q => @xO@ (@succ@ q)
    | @xH@, @xO@ q => @xI@ q
    | @xH@, @xH@ => @xO@ @xH@
  end
with add_carry (x y:@pos@) : @pos@ :=
  match x, y with
    | @xI@ p, @xI@ q => @xI@ (add_carry p q)
    | @xI@ p, @xO@ q => @xO@ (add_carry p q)
    | @xI@ p, @xH@ => @xI@ (@succ@ p)
    | @xO@ p, @xI@ q => @xO@ (add_carry p q)
    | @xO@ p, @xO@ q => @xI@ (add p q)
    | @xO@ p, @xH@ => @xO@ (@succ@ p)
    | @xH@, @xI@ q => @xI@ (@succ@ q)
    | @xH@, @xO@ q => @xO@ (@succ@ q)
    | @xH@, @xH@ => @xI@ @xH@
  end.
"""

REST_T = """
Fixpoint pred_double (x:@pos@) : @pos@ :=
  match x with
    | @xI@ p => @xI@ (@xO@ p)
    | @xO@ p => @xI@ (pred_double p)
    | @xH@ => @xH@
  end.

Fixpoint mul (x y:@pos@) : @pos@ :=
  match x with
    | @xI@ p => add y (@xO@ (mul p y))
    | @xO@ p => @xO@ (mul p y)
    | @xH@ => y
  end.

Definition div2 (p:@pos@) : @pos@ :=
  match p with
    | @xH@ => @xH@
    | @xO@ p => p
    | @xI@ p => p
  end.

Definition div2_up (p:@pos@) : @pos@ :=
 match p with
   | @xH@ => @xH@
   | @xO@ p => p
   | @xI@ p => @succ@ p
 end.

Fixpoint of_succ_nat (n:@nat@) : @pos@ :=
  match n with
    | @O@ => @xH@
    | @S@ x => @succ@ (of_succ_nat x)
  end.

Fixpoint compare_cont (r:@cmp@) (x y:@pos@) {struct y} : @cmp@ :=
  match x, y with
    | @xI@ p, @xI@ q => compare_cont r p q
    | @xI@ p, @xO@ q => compare_cont @Gt@ p q
    | @xI@ p, @xH@ => @Gt@
    | @xO@ p, @xI@ q => compare_cont @Lt@ p q
    | @xO@ p, @xO@ q => compare_cont r p q
    | @xO@ p, @xH@ => @Gt@
    | @xH@, @xI@ q => @Lt@
    | @xH@, @xO@ q => @Lt@
    | @xH@, @xH@ => r
  end.

Definition compare := compare_cont @Eq@.

Fixpoint eqb (p q:@pos@) {struct q} : @bool@ :=
  match p, q with
    | @xI@ p, @xI@ q => eqb p q
    | @xO@ p, @xO@ q => eqb p q
    | @xH@, @xH@ => @true@
    | _, _ => @false@
  end.
"""

POS_TEMPLATE = SUCC_T + ADD_T + REST_T

Z_TEMPLATE = """
Definition double (x:@Z@) : @Z@ :=
  match x with
    | @Z0@ => @Z0@
    | @Zpos@ p => @Zpos@ (@xO@ p)
    | @Zneg@ p => @Zneg@ (@xO@ p)
  end.

Definition succ_double (x:@Z@) : @Z@ :=
  match x with
    | @Z0@ => @Zpos@ @xH@
    | @Zpos@ p => @Zpos@ (@xI@ p)
    | @Zneg@ p => @Zneg@ (@P@pred_double p)
  end.

Definition pred_double (x:@Z@) : @Z@ :=
  match x with
    | @Z0@ => @Zneg@ @xH@
    | @Zneg@ p => @Zneg@ (@xI@ p)
    | @Zpos@ p => @Zpos@ (@P@pred_double p)
  end.

Fixpoint pos_sub (x y:@pos@) {struct y} : @Z@ :=
  match x, y with
    | @xI@ p, @xI@ q => double (pos_sub p q)
    | @xI@ p, @xO@ q => succ_double (pos_sub p q)
    | @xI@ p, @xH@ => @Zpos@ (@xO@ p)
    | @xO@ p, @xI@ q => pred_double (pos_sub p q)
    | @xO@ p, @xO@ q => double (pos_sub p q)
    | @xO@ p, @xH@ => @Zpos@ (@P@pred_double p)
    | @xH@, @xI@ q => @Zneg@ (@xO@ q)
    | @xH@, @xO@ q => @Zneg@ (@P@pred_double q)
    | @xH@, @xH@ => @Z0@
  end.

Definition add (x y:@Z@) : @Z@ :=
  match x, y with
    | @Z0@, y => y
    | x, @Z0@ => x
    | @Zpos@ x', @Zpos@ y' => @Zpos@ (@P@add x' y')
    | @Zpos@ x', @Zneg@ y' => pos_sub x' y'
    | @Zneg@ x', @Zpos@ y' => pos_sub y' x'
    | @Zneg@ x', @Zneg@ y' => @Zneg@ (@P@add x' y')
  end.

Definition opp (x:@Z@) : @Z@ :=
  match x with
    | @Z0@ => @Z0@
    | @Zpos@ x => @Zneg@ x
    | @Zneg@ x => @Zpos@ x
  end.

Definition sub (m n:@Z@) : @Z@ := add m (opp n).

Definition mul (x y:@Z@) : @Z@ :=
  match x, y with
    | @Z0@, _ => @Z0@
    | _, @Z0@ => @Z0@
    | @Zpos@ x', @Zpos@ y' => @Zpos@ (@P@mul x' y')
    | @Zpos@ x', @Zneg@ y' => @Zneg@ (@P@mul x' y')
    | @Zneg@ x', @Zpos@ y' => @Zneg@ (@P@mul x' y')
    | @Zneg@ x', @Zneg@ y' => @Zpos@ (@P@mul x' y')
  end.

Definition compare (x y:@Z@) : @cmp@ :=
  match x, y with
    | @Z0@, @Z0@ => @Eq@
    | @Z0@, @Zpos@ y' => @Lt@
    | @Z0@, @Zneg@ y' => @Gt@
    | @Zpos@ x', @Z0@ => @Gt@
    | @Zpos@ x', @Zpos@ y' => @P@compare x' y'
    | @Zpos@ x', @Zneg@ y' => @Gt@
    | @Zneg@ x', @Z0@ => @Lt@
    | @Zneg@ x', @Zpos@ y' => @Lt@
    | @Zneg@ x', @Zneg@ y' => @CompOpp@ (@P@compare x' y')
  end.

Definition leb (x y:@Z@) : @bool@ :=
  match compare x y with
    | @Gt@ => @false@
    | _ => @true@
  end.

Definition ltb (x y:@Z@) : @bool@ :=
  match compare x y with
    | @Lt@ => @true@
    | _ => @false@
  end.

Definition eqb (x y:@Z@) : @bool@ :=
  match x, y with
    | @Z0@, @Z0@ => @true@
    | @Zpos@ p, @Zpos@ q => @P@eqb p q
    | @Zneg@ p, @Zneg@ q => @P@eqb p q
    | _, _ => @false@
  end.

Definition div2 (z:@Z@) : @Z@ :=
 match z with
   | @Z0@ => @Z0@
   | @Zpos@ @xH@ => @Z0@
   | @Zpos@ p => @Zpos@ (@P@div2 p)
   | @Zneg@ p => @Zneg@ (@P@div2_up p)
 end.

Definition of_nat (n:@nat@) : @Z@ :=
  match n with
   | @O@ => @Z0@
   | @S@ n => @Zpos@ (@P@of_succ_nat n)
  end.

Fixpoint pos_div_eucl (a:@pos@) (b:@Z@) : @prod@ @Z@ @Z@ :=
  match a with
    | @xH@ => if leb (@Zpos@ (@xO@ @xH@)) b then @pair@ @Z0@ (@Zpos@ @xH@) else @pair@ (@Zpos@ @xH@) @Z0@
    | @xO@ a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := mul (@Zpos@ (@xO@ @xH@)) r in
      if ltb r' b then @pair@ (mul (@Zpos@ (@xO@ @xH@)) q) r'
      else @pair@ (add (mul (@Zpos@ (@xO@ @xH@)) q) (@Zpos@ @xH@)) (sub r' b)
    | @xI@ a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := add (mul (@Zpos@ (@xO@ @xH@)) r) (@Zpos@ @xH@) in
      if ltb r' b then @pair@ (mul (@Zpos@ (@xO@ @xH@)) q) r'
      else @pair@ (add (mul (@Zpos@ (@xO@ @xH@)) q) (@Zpos@ @xH@)) (sub r' b)
  end.
"""

NAT_TEMPLATE = """
Fixpoint eqb (n m : @nat@) : @bool@ :=
  match n, m with
    | @O@, @O@ => @true@
    | @O@, @S@ _ => @false@
    | @S@ _, @O@ => @false@
    | @S@ n', @S@ m' => eqb n' m'
  end.

Fixpoint leb (n m : @nat@) : @bool@ :=
  match n, m with
    | @O@, _ => @true@
    | _, @O@ => @false@
    | @S@ n', @S@ m' => leb n' m'
  end.
"""

CORE = {"pos": "positive", "xI": "xI", "xO": "xO", "xH": "xH", "cmp": "comparison",
        "Eq": "Eq", "Lt": "Lt", "Gt": "Gt", "bool": "bool", "true": "true", "false": "false",
        "Z": "Z", "Z0": "Z0", "Zpos": "Zpos", "Zneg": "Zneg", "nat": "nat", "O": "O", "S": "S",
        "prod": "prod", "pair": "pair", "CompOpp": "CompOpp", "succ": "succ"}
USER = {"pos": "upos", "xI": "pI", "xO": "pO", "xH": "pH", "cmp": "ucmp",
        "Eq": "cEq", "Lt": "cLt", "Gt": "cGt", "bool": "ubool", "true": "btrue", "false": "bfalse",
        "Z": "uZ", "Z0": "uZ0", "Zpos": "uZpos", "Zneg": "uZneg", "nat": "unat", "O": "nO", "S": "nS",
        "prod": "uprod", "pair": "upair", "CompOpp": "uCompOpp", "succ": "succ"}

def inst(template, names, **extra):
    for k, v in dict(names, **extra).items():
        template = template.replace("@%s@" % k, v)
    assert "@" not in template, template
    return template

# (c) Copies: SPos, SZ, SN over Corelib's types, SZ calling Corelib's Pos
# functions, as Stdlib's BinInt.Z does; UP, UZ, UN over user inductives; and
# copies of Pos.add and Pos.of_succ_nat that call Pos.succ through aliases.
out = [HEADER, """
Inductive upos : Set := pI : upos -> upos | pO : upos -> upos | pH : upos.
Inductive ucmp : Set := cEq | cLt | cGt.
Inductive ubool : Set := btrue | bfalse.
Inductive uZ : Set := uZ0 : uZ | uZpos : upos -> uZ | uZneg : upos -> uZ.
Inductive unat : Set := nO : unat | nS : unat -> unat.
Inductive uprod (A B : Type) : Type := upair : A -> B -> uprod A B.
Arguments upair {A B} _ _.
Definition uCompOpp (r:ucmp) : ucmp := match r with cEq => cEq | cLt => cGt | cGt => cLt end.
""",
       "Module SPos.\n", inst(POS_TEMPLATE, CORE), "End SPos.\n",
       "Module SZ.\n", inst(Z_TEMPLATE, CORE, P="Pos."), "End SZ.\n",
       "Module SN.\n", inst(NAT_TEMPLATE, CORE), "End SN.\n",
       "Module UP.\n", inst(POS_TEMPLATE, USER), "End UP.\n",
       "Module UZ.\n", inst(Z_TEMPLATE, USER, P="UP."), "End UZ.\n",
       "Module UN.\n", inst(NAT_TEMPLATE, USER), "End UN.\n",
       """
Definition asucc := Pos.succ.
Definition asucc2 := asucc.
Definition zadd_alias := Z.add.
Module AP.
""", inst(SUCC_T + ADD_T, CORE, succ="asucc"),
       inst("""
Fixpoint of_succ_nat (n:@nat@) : @pos@ :=
  match n with
    | @O@ => @xH@
    | @S@ x => @succ@ (of_succ_nat x)
  end.
""", CORE, succ="asucc2"), "End AP.\n"]

def copies(kind, p, zf, nf, routine, fn, args, nrand):
    """Lemmas on random inputs for the copies of [fn] over Corelib's types (S)
    and user types (U)."""
    for i in range(nrand):
        a = args()
        for mod, conv in (("S", (pos, z, nat)), ("U", (upos, uz, unat))):
            pc, zc, nc = conv
            vals = [{"p": pc, "z": zc, "n": nc}[t](v) for t, v in a]
            m = {"pos": mod + "P", "z": mod + "Z", "nat": mod + "N"}[kind]
            m = m.replace("SP", "SPos")
            out.append(lemma("c%d" % len(out), "%s.%s %s" % (m, fn, " ".join(vals))))
            count("NC_" + routine.replace(".", "_"))

R = lambda: ("p", rpos(1, 120))
RZ = lambda: ("z", rng.choice([0, 1, -1]) * rpos(1, 120))
RN = lambda: ("n", rng.randint(0, 300))
for fn, routine, gen in (
        ("succ", "Pos.succ", lambda: [R()]),
        ("add", "Pos.add", lambda: [R(), R()]),
        ("add_carry", "Pos.add_carry", lambda: [R(), R()]),
        ("pred_double", "Pos.pred_double", lambda: [R()]),
        ("mul", "Pos.mul", lambda: [R(), R()]),
        ("div2", "Pos.div2", lambda: [R()]),
        ("of_succ_nat", "Pos.of_succ_nat", lambda: [RN()]),
        ("compare_cont", "Pos.compare_cont",
         lambda: [("c", rng.choice(["Eq", "Lt", "Gt"])), R(), R()]),
        ("eqb", "Pos.eqb", lambda: (lambda a: [a, rng.choice([a, R()])])(R()))):
    if fn == "compare_cont":
        for i in range(8):
            a = gen()
            for mod, pc, cmap in (("SPos", pos, {"Eq": "Eq", "Lt": "Lt", "Gt": "Gt"}),
                                  ("UP", upos, {"Eq": "cEq", "Lt": "cLt", "Gt": "cGt"})):
                out.append(lemma("c%d" % len(out), "%s.compare_cont %s %s %s"
                                 % (mod, cmap[a[0][1]], pc(a[1][1]), pc(a[2][1]))))
                count("NC_Pos_compare_cont")
        continue
    copies("pos", None, None, None, routine, fn, gen, 8)
for fn in ("double", "succ_double", "pred_double", "div2"):
    copies("z", None, None, None, "Z." + fn, fn, lambda: [RZ()], 8)
for fn in ("add", "mul", "compare", "leb", "ltb", "eqb"):
    copies("z", None, None, None, "Z." + fn, fn,
           lambda: (lambda a: [a, rng.choice([a, ("z", -a[1]), RZ()])])(RZ()), 8)
copies("z", None, None, None, "Z.pos_sub", "pos_sub", lambda: [R(), R()], 8)
copies("z", None, None, None, "Z.of_nat", "of_nat", lambda: [RN()], 8)
copies("z", None, None, None, "Z.pos_div_eucl", "pos_div_eucl",
       lambda: [R(), ("z", rpos(1, 70))], 8)
for fn in ("eqb", "leb"):
    copies("nat", None, None, None, "Nat." + fn, fn,
           lambda: (lambda a: [a, rng.choice([a, RN()])])(RN()), 8)
for i in range(6):
    a, b = rpos(1, 100), rpos(1, 100)
    out.append(lemma("al%d" % i, "AP.add %s %s" % (pos(a), pos(b))))
    count("NC_Pos_add")
    out.append(lemma("alc%d" % i, "AP.add_carry %s %s" % (pos(a), pos(b))))
    count("NC_Pos_add_carry")
    out.append(lemma("ao%d" % i, "AP.of_succ_nat %s" % nat(rng.randint(0, 300))))
    count("NC_Pos_of_succ_nat")
    out.append(lemma("az%d" % i, "zadd_alias %s %s" % (z(a), z(-b))))
    count("NC_Z_add")
open(d + "/Copy.v", "w").write("".join(out))

# (d) Near misses.
out = [HEADER, "Local Open Scope positive_scope.\n", """
(* Pos.succ with one branch changed. *)
Fixpoint succ_bad (x:positive) : positive :=
  match x with
    | p~1 => (succ_bad p)~0
    | p~0 => p~0
    | 1 => 1~0
  end.

(* Z.add with the arguments of one call swapped. *)
Definition zadd_swap (x y:Z) : Z :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (Pos.add x' y')
    | Zpos x', Zneg y' => Z.pos_sub y' x'
    | Zneg x', Zpos y' => Z.pos_sub y' x'
    | Zneg x', Zneg y' => Zneg (Pos.add x' y')
  end.

(* Pos.add with one branch changed, and Z.add calling it. *)
""", inst(ADD_T, CORE, succ="Pos.succ")
       .replace("Fixpoint add ", "Fixpoint add_bad ").replace("add_carry", "add_carry_bad")
       .replace("(add p q)", "(add_bad p q)")
       .replace("| xH, xH => xO xH", "| xH, xH => xI xH"), """
Definition zadd_cbad (x y:Z) : Z :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (add_bad x' y')
    | Zpos x', Zneg y' => Z.pos_sub x' y'
    | Zneg x', Zpos y' => Z.pos_sub y' x'
    | Zneg x', Zneg y' => Zneg (add_bad x' y')
  end.

(* Z.pos_div_eucl with one constructor changed. *)
Fixpoint pde_bad (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if Z.leb (Zpos 2) b then (Z0, Zpos 1) else (Zpos 1, Zpos 1)
    | xO a' =>
      let (q, r) := pde_bad a' b in
      let r' := Z.mul (Zpos 2) r in
      if Z.ltb r' b then (Z.mul (Zpos 2) q, r') else (Z.add (Z.mul (Zpos 2) q) (Zpos 1), Z.sub r' b)
    | xI a' =>
      let (q, r) := pde_bad a' b in
      let r' := Z.add (Z.mul (Zpos 2) r) (Zpos 1) in
      if Z.ltb r' b then (Z.mul (Zpos 2) q, r') else (Z.add (Z.mul (Zpos 2) q) (Zpos 1), Z.sub r' b)
  end.

(* Nat.leb with one branch changed. *)
Fixpoint leb_bad (n m : nat) : bool :=
  match n, m with
    | O, _ => false
    | _, O => false
    | S n', S m' => leb_bad n' m'
  end.

(* Pos.add calling an opaque successor. *)
Definition osucc : positive -> positive.
Proof. exact Pos.succ. Qed.
Module OP.
""", inst(ADD_T, CORE, succ="osucc"), """End OP.

(* Where each differs from the function it copies. The values of the
   functions are checked by the kernel's own conversion, not by the VM. *)
Lemma succ_differs : succ_bad 2 = cbv_val (succ_bad 2).
Proof. vm_compute. reflexivity. Qed.
Lemma succ_ref : succ_bad 2 = 2 /\\ Pos.succ 2 = 3.
Proof. split; reflexivity. Qed.
Lemma swap_differs : zadd_swap (Zpos 3) (Zneg 1) = cbv_val (zadd_swap (Zpos 3) (Zneg 1)).
Proof. vm_compute. reflexivity. Qed.
Lemma swap_ref : zadd_swap (Zpos 3) (Zneg 1) = Zneg 2 /\\ Z.add (Zpos 3) (Zneg 1) = Zpos 2.
Proof. split; reflexivity. Qed.
Lemma cbad_differs : zadd_cbad (Zpos 1) (Zpos 1) = cbv_val (zadd_cbad (Zpos 1) (Zpos 1)).
Proof. vm_compute. reflexivity. Qed.
Lemma cbad_ref : zadd_cbad (Zpos 1) (Zpos 1) = Zpos 3 /\\ Z.add (Zpos 1) (Zpos 1) = Zpos 2.
Proof. split; reflexivity. Qed.
Lemma pde_differs : pde_bad 1 (Zpos 1) = cbv_val (pde_bad 1 (Zpos 1)).
Proof. vm_compute. reflexivity. Qed.
Lemma pde_ref : pde_bad 1 (Zpos 1) = (Zpos 1, Zpos 1) /\\ Z.pos_div_eucl 1 (Zpos 1) = (Zpos 1, Z0).
Proof. split; reflexivity. Qed.
Lemma leb_differs : leb_bad 0 0 = cbv_val (leb_bad 0 0).
Proof. vm_compute. reflexivity. Qed.
Lemma leb_ref : leb_bad 0 0 = false /\\ Nat.leb 0 0 = true.
Proof. split; reflexivity. Qed.
Lemma op_add : OP.add 2 2 = cbv_val (OP.add 2 2).
Proof. vm_compute. reflexivity. Qed.

(* Pos.mul calling Pos.add_carry (function 1 of the block that Pos.add's body
   is) where the reference calls Pos.add (function 0). *)
Fixpoint mul_c (x y:positive) : positive :=
  match x with
    | p~1 => Pos.add_carry y (mul_c p y)~0
    | p~0 => (mul_c p y)~0
    | 1 => y
  end.

(* Z.pos_div_eucl with one let value changed: r' := 2 q in the xO branch. *)
Fixpoint pde_lv (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if Z.leb (Zpos 2) b then (Z0, Zpos 1) else (Zpos 1, Z0)
    | xO a' =>
      let (q, r) := pde_lv a' b in
      let r' := Z.mul (Zpos 2) q in
      if Z.ltb r' b then (Z.mul (Zpos 2) q, r') else (Z.add (Z.mul (Zpos 2) q) (Zpos 1), Z.sub r' b)
    | xI a' =>
      let (q, r) := pde_lv a' b in
      let r' := Z.add (Z.mul (Zpos 2) r) (Zpos 1) in
      if Z.ltb r' b then (Z.mul (Zpos 2) q, r') else (Z.add (Z.mul (Zpos 2) q) (Zpos 1), Z.sub r' b)
  end.

(* Z.pos_div_eucl with one let body changed: Z.sub b r' in the xO branch. *)
Fixpoint pde_lb (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if Z.leb (Zpos 2) b then (Z0, Zpos 1) else (Zpos 1, Z0)
    | xO a' =>
      let (q, r) := pde_lb a' b in
      let r' := Z.mul (Zpos 2) r in
      if Z.ltb r' b then (Z.mul (Zpos 2) q, r') else (Z.add (Z.mul (Zpos 2) q) (Zpos 1), Z.sub b r')
    | xI a' =>
      let (q, r) := pde_lb a' b in
      let r' := Z.add (Z.mul (Zpos 2) r) (Zpos 1) in
      if Z.ltb r' b then (Z.mul (Zpos 2) q, r') else (Z.add (Z.mul (Zpos 2) q) (Zpos 1), Z.sub r' b)
  end.

Lemma mul_c_differs : mul_c 3 1 = cbv_val (mul_c 3 1).
Proof. vm_compute. reflexivity. Qed.
Lemma mul_c_ref : mul_c 3 1 = xO (xO xH) /\\ Pos.mul 3 1 = xI xH.
Proof. split; reflexivity. Qed.
Lemma pde_lv_differs : pde_lv (xO xH) (Zpos (xI xH)) = cbv_val (pde_lv (xO xH) (Zpos (xI xH))).
Proof. vm_compute. reflexivity. Qed.
Lemma pde_lv_ref : pde_lv (xO xH) (Zpos (xI xH)) = (Z0, Z0) /\\
  Z.pos_div_eucl (xO xH) (Zpos (xI xH)) = (Z0, Zpos (xO xH)).
Proof. split; reflexivity. Qed.
Lemma pde_lb_differs : pde_lb (xO (xI xH)) (Zpos (xO (xO xH))) =
  cbv_val (pde_lb (xO (xI xH)) (Zpos (xO (xO xH)))).
Proof. vm_compute. reflexivity. Qed.
Lemma pde_lb_ref : pde_lb (xO (xI xH)) (Zpos (xO (xO xH))) = (Zpos xH, Zneg (xO xH)) /\\
  Z.pos_div_eucl (xO (xI xH)) (Zpos (xO (xO xH))) = (Zpos xH, Zpos (xO xH)).
Proof. split; reflexivity. Qed.
"""]
for i in range(10):
    a, b = rpos(1, 90), rpos(1, 90)
    out.append(lemma("bs%d" % i, "succ_bad %s" % pos(a)))
    out.append(lemma("bw%d" % i, "zadd_swap %s %s" % (z(a), z(-b))))
    out.append(lemma("bc%d" % i, "zadd_cbad %s %s" % (z(a), z(b))))
    out.append(lemma("bp%d" % i, "pde_bad %s %s" % (pos(a), z(b))))
    out.append(lemma("bl%d" % i, "leb_bad %s %s" % (nat(rng.randint(0, 50)), nat(rng.randint(0, 50)))))
open(d + "/Bad.v", "w").write("".join(out))

# (e) Free variables: one lemma per library, either [l = l] or [l = c] with c
# computed by cbv.
def refl(name, binder, lhs):
    return ("Lemma %s %s : %s = %s.\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, binder, lhs, lhs))
def free_cbv(name, binder, lhs):
    return ("Lemma %s %s : %s = cbv_val (%s).\nProof. vm_compute. reflexivity. Qed.\n"
            % (name, binder, lhs, lhs))
P, ZB, NB = "(p : positive)", "(y : Z)", "(n : nat)"
E = {
    "E1": free_cbv("e", P, "Pos.succ (xO p)"),
    "E2": refl("e", P, "Pos.succ (xI p)"),
    "E3": free_cbv("e", P, "Pos.add (xO p) xH"),
    "E4": refl("e", P, "Pos.add (xI p) xH"),
    "E5": free_cbv("e", P, "Pos.mul (xO (xO xH)) p"),
    "E6": free_cbv("e", ZB, "Z.add Z0 y"),
    "E7": free_cbv("e", P, "Z.compare (Zpos p) Z0"),
    "E8": free_cbv("e", P, "Z.double (Zpos p)"),
    "E9": refl("e", P, "Z.div2 (Zneg (xI p))"),
    "E10": refl("e", NB, "Nat.eqb (S (S n)) 3"),
    "E11": free_cbv("e", NB, "Nat.leb 0 n"),
    "E12": lemma("e", "Z.pos_div_eucl %s %s" % (pos(5), z(-3))),
}
# One library per refusal guard of the routines: a variable where the
# routine's guard is the only check before a field read (B1 of the slice-2
# review). [l = l], except Q1 and Q2, whose right sides are constructors
# that the bytecode computes after the routine refuses.
def xo(k, inner):
    for _ in range(k): inner = "(xO %s)" % inner
    return inner
PROBES = [
    ("P01", P, "Pos.pred_double (xO p)"),
    ("P02", P, "Pos.add (xO p) (xI xH)"),
    ("P03", P, "Pos.mul (xI xH) p"),
    ("P04", P, "Pos.mul (xI p) (xI xH)"),
    ("P05", P, "Pos.div2 p"),
    ("P06", NB, "Pos.of_succ_nat (S n)"),
    ("P07", ZB, "Z.double y"),
    ("P08", ZB, "Z.succ_double y"),
    ("P09", ZB, "Z.pred_double y"),
    ("P10", P, "Z.pos_sub (xO p) xH"),
    ("P11", ZB, "Z.add y (Zpos xH)"),
    ("P12", ZB, "Z.add (Zpos xH) y"),
    ("P13", P, "Z.add (Zpos (xO p)) (Zneg xH)"),
    ("P14", ZB, "Z.mul y (Zpos (xI xH))"),
    ("P15", ZB, "Z.mul (Zpos (xI xH)) y"),
    ("P16", P, "Z.mul (Zpos (xI xH)) (Zpos p)"),
    ("P17", ZB, "Z.compare y Z0"),
    ("P18", ZB, "Z.compare Z0 y"),
    ("P19", ZB, "Z.leb y Z0"),
    ("P20", ZB, "Z.ltb Z0 y"),
    ("P21", ZB, "Z.eqb y Z0"),
    ("P22", ZB, "Z.eqb Z0 y"),
    ("P23", ZB, "Z.div2 y"),
    ("P24", P, "Z.div2 (Zpos p)"),
    ("P25", NB, "Z.of_nat (S n)"),
    ("P26", P, "Z.pos_div_eucl (xO p) (Zpos (xI xH))"),
    ("P27", P, "Z.pos_div_eucl (xI (xO xH)) (Zpos (xO p))"),
    ("P28", NB, "Nat.eqb (S O) (S n)"),
    ("P29", NB, "Nat.leb (S n) (S (S O))"),
    ("P30", NB, "Nat.leb (S (S O)) (S n)"),
    ("P31", P, "Z.pos_sub %s xH" % xo(70, "p")),
    ("P32", P, "Pos.mul (xI xH) %s" % xo(70, "p")),
    ("P33", P, "Pos.add_carry (xO p) (xI xH)"),
]
for lib, binder, lhs in PROBES:
    E[lib] = refl("e", binder, lhs)
E["Q1"] = free_cbv("e", P, "Z.pos_sub (xI p) xH")
E["Q2"] = free_cbv("e", P, "Z.compare (Zpos (xI p)) (Zpos xH)")
for lib, text in E.items():
    open(d + "/%s.v" % lib, "w").write(HEADER + text)
open(d + "/Partial.v", "w").write(HEADER + """
Fixpoint map {A B} (f : A -> B) (l : list A) : list B :=
  match l with nil => nil | cons x l => cons (f x) (map f l) end.
""" + lemma("partial", "map (Z.add %s) (cons %s (cons %s (cons Z0 nil)))" % (z(3), z(1), z(-5))))

# (g) Large numbers.
out = [HEADER]
a, b = bits(1500), bits(1500)
big = [
    ("Pos.mul", "Pos.mul %s %s" % (pos(a), pos(b))),
    ("Pos.add", "Pos.add %s %s" % (pos(bits(3000)), pos(bits(3000)))),
    ("Pos.add_carry", "Pos.add_carry %s %s" % (pos((1 << 3000) - 1), pos(1))),
    ("Pos.succ", "Pos.succ %s" % pos((1 << 3000) - 1)),
    ("Pos.pred_double", "Pos.pred_double %s" % pos(1 << 3000)),
    ("Z.mul", "Z.mul %s %s" % (z(-a), z(b))),
    ("Z.add", "Z.add %s %s" % (z(-bits(3000)), z(bits(2999)))),
    ("Z.pos_sub", "Z.pos_sub %s %s" % (pos(bits(3000)), pos(bits(3000)))),
    ("Z.pos_div_eucl", "Z.pos_div_eucl %s %s" % (pos(bits(2000)), z(bits(1000)))),
    ("Z.pos_div_eucl", "Z.pos_div_eucl %s %s" % (pos(bits(2000)), z(bits(31)))),
    ("Pos.of_succ_nat", "Pos.of_succ_nat %s" % nat(3000)),
]
for i, (routine, lhs) in enumerate(big):
    out.append(lemma("g%d" % i, lhs))
    count("NG_" + routine.replace(".", "_"))
open(d + "/Big.v", "w").write("".join(out))

# (g) Chains over a shared base that the VM has just allocated (the fresh
# result of Pos.mul _ 1 or Z.mul _ 1, which copies its argument, and so is
# young), for k = 1000, 2000 and 3000 (the review of slice 2, N2):
#  - Pos.succ (Pos.mul X 1), X = S 2^(k+1) + 2^k - 1: k + 1 fresh nodes over
#    the subterm S~0 of the young copy;
#  - Pos.mul 2^k (Pos.mul S 1): k fresh xO over the young copy;
#  - Z.mul (Zpos 2^k) (Z.mul (Zneg S) (Zpos 1)): the same, wrapped in Zneg;
#  - Z.succ_double (Zneg (Pos.mul (S 2^k) 1)): k fresh xI over a subterm.
# Each outer call hits once, and each inner Pos.mul or Z.mul once.
out = [HEADER]
for k in (1000, 2000, 3000):
    s = rng.randrange(1 << 299, 1 << 300)
    x = (s << (k + 1)) + (1 << k) - 1
    for routine, lhs in (
            ("Pos.succ", "Pos.succ (Pos.mul %s xH)" % pos(x)),
            ("Pos.mul", "Pos.mul %s (Pos.mul %s xH)" % (pos(1 << k), pos(s))),
            ("Z.mul", "Z.mul (Zpos %s) (Z.mul (Zneg %s) (Zpos xH))" % (pos(1 << k), pos(s))),
            ("Z.succ_double", "Z.succ_double (Zneg (Pos.mul %s xH))" % pos(s << k))):
        out.append(lemma("s%d" % len(out), lhs))
        count("NS_" + routine.replace(".", "_"))
count("NS_Pos_mul", 9)
count("NS_Z_mul", 3)
open(d + "/BigShare.v", "w").write("".join(out))

with open(d + "/counts", "w") as f:
    for k, v in sorted(counts.items()):
        f.write("%s=%d\n" % (k, v))
PY
. "$d/counts"

ELIBS="E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 Partial Q1 Q2
  P01 P02 P03 P04 P05 P06 P07 P08 P09 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20
  P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33"
for lib in Diff Copy Bad $ELIBS Big BigShare; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# chk LOG ARGS...: rocqchk with the counters on; its output goes to LOG.
# The words counted below are those of chain literals: ROCQ_VM_BINNUM
# defaults to -packlit here, since a packed literal is one word (see (h)).
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

expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

bound() { grep -q "^binnum\[[0-9]*\] bind $2: $3\$" "$d/$1"; }
# missed LOG NAME REFERENCE REASON
missed() { grep -q "^binnum\[[0-9]*\] near-miss $2: $3: $4\$" "$d/$1"; }
# first_diff LOG NAME REFERENCE: with ROCQ_VM_BINNUM_STATS=2, the path to the
# first node where NAME differs from REFERENCE.
first_diff() {
  awk -v n="near-miss $2: $3: " 'hit { sub(/^binnum\[[0-9]*\]   at /, ""); print; exit }
    index($0, n) { hit = 1 }' "$d/$1"
}

ROUTINES="Pos.succ Pos.add Pos.add_carry Pos.pred_double Pos.mul Pos.div2 Pos.of_succ_nat
  Z.double Z.succ_double Z.pred_double Z.pos_sub Z.add Z.mul Z.compare Z.leb Z.ltb Z.eqb
  Z.div2 Z.of_nat Z.pos_div_eucl Nat.eqb Nat.leb"
key() { echo "$1_$(echo "$2" | tr . _)"; }
count_of() { local k; k=$(key "$1" "$2"); echo "${!k:-0}"; }

# (a) Every routine hits once per lemma, and refuses nothing.
chk a.log -norec Diff
for r in $ROUTINES; do
  expect "(a) $r hits" "$(stat a.log "$r" hits)" -eq "$(count_of N "$r")"
  expect "(a) $r refusals" "$(stat a.log "$r" refusals)" -eq 0
done
for c in "PosDef.Pos.succ: Pos.succ" "PosDef.Pos.add: Pos.add,Pos.add_carry" \
         "PosDef.Pos.add_carry: Pos.add,Pos.add_carry" "PosDef.Pos.pred_double: Pos.pred_double" \
         "PosDef.Pos.mul: Pos.mul" "PosDef.Pos.div2: Pos.div2" \
         "PosDef.Pos.of_succ_nat: Pos.of_succ_nat" \
         "IntDef.Z.double: Z.double" "IntDef.Z.succ_double: Z.succ_double" \
         "IntDef.Z.pred_double: Z.pred_double" "IntDef.Z.pos_sub: Z.pos_sub" \
         "IntDef.Z.add: Z.add" "IntDef.Z.mul: Z.mul" "IntDef.Z.compare: Z.compare" \
         "IntDef.Z.leb: Z.leb" "IntDef.Z.ltb: Z.ltb" "IntDef.Z.eqb: Z.eqb" \
         "IntDef.Z.div2: Z.div2" "IntDef.Z.of_nat: Z.of_nat" \
         "IntDef.Z.pos_div_eucl: Z.pos_div_eucl"; do
  bound a.log "Corelib.BinNums.${c%%: *}" "${c#*: }" || fail "(a) Corelib.BinNums.$c is not bound"
done
bound a.log Corelib.Init.Nat.eqb Nat.eqb || fail "(a) Corelib.Init.Nat.eqb is not bound"
bound a.log Corelib.Init.Nat.leb Nat.leb || fail "(a) Corelib.Init.Nat.leb is not bound"
binds_a=$(recog a.log binds)

# (b) Recognition off: nothing is bound and no routine runs. One routine off.
ROCQ_VM_BINNUM=0 chk b.log -norec Diff
expect "(b) binds" "$(recog b.log binds)" -eq 0
for r in $ROUTINES; do
  expect "(b) $r calls" "$(stat b.log "$r" calls)" -eq 0
done
ROCQ_VM_BINNUM=-Pos.succ chk b2.log -norec Diff
expect "(b) -Pos.succ: Pos.succ calls" "$(stat b2.log Pos.succ calls)" -eq 0
expect "(b) -Pos.succ: Pos.of_succ_nat hits" "$(stat b2.log Pos.of_succ_nat hits)" -eq "$N_Pos_of_succ_nat"
expect "(b) -Pos.succ: Z.add hits" "$(stat b2.log Z.add hits)" -eq "$N_Z_add"
# The copies, the near misses, the refusals and the large numbers also check
# with recognition off.
for lib in Copy Bad $ELIBS Big BigShare; do
  ROCQ_VM_BINNUM=0 chk "b-$lib.log" -norec "$lib"
  expect "(b) $lib binds" "$(recog "b-$lib.log" binds)" -eq 0
done

# (c) The copies bind, through their callees and aliases, and their results
# are right.
chk c.log -norec Copy
for m in SPos UP; do
  for c in "succ: Pos.succ" "add: Pos.add,Pos.add_carry" "add_carry: Pos.add,Pos.add_carry" \
           "pred_double: Pos.pred_double" "mul: Pos.mul" "div2: Pos.div2" \
           "of_succ_nat: Pos.of_succ_nat" "compare_cont: Pos.compare_cont" "eqb: Pos.eqb"; do
    bound c.log "Copy.$m.${c%%: *}" "${c#*: }" || fail "(c) Copy.$m.$c is not bound"
  done
done
for m in SZ UZ; do
  for f in double succ_double pred_double pos_sub add mul compare leb ltb eqb div2 of_nat pos_div_eucl; do
    bound c.log "Copy.$m.$f" "Z.$f" || fail "(c) Copy.$m.$f is not bound"
  done
done
for m in SN UN; do
  for f in eqb leb; do
    bound c.log "Copy.$m.$f" "Nat.$f" || fail "(c) Copy.$m.$f is not bound"
  done
done
bound c.log Copy.AP.add Pos.add,Pos.add_carry || fail "(c) Copy.AP.add (through an alias) is not bound"
bound c.log Copy.AP.of_succ_nat Pos.of_succ_nat \
  || fail "(c) Copy.AP.of_succ_nat (through two aliases) is not bound"
for r in $ROUTINES Pos.compare_cont Pos.eqb; do
  expect "(c) $r hits" "$(stat c.log "$r" hits)" -eq "$(count_of NC "$r")"
  expect "(c) $r refusals" "$(stat c.log "$r" refusals)" -eq 0
done

# (d) The near misses do not bind, each for its reason.
STATS=2 chk d.log -norec Bad
missed d.log Bad.succ_bad Pos.succ constructor || fail "(d) Bad.succ_bad is not a near miss for its constructor"
missed d.log Bad.zadd_swap Z.add "de Bruijn index" || fail "(d) Bad.zadd_swap is not a near miss for a variable"
missed d.log Bad.add_bad Pos.add constructor || fail "(d) Bad.add_bad is not a near miss for its constructor"
missed d.log Bad.zadd_cbad Z.add constructor || fail "(d) Bad.zadd_cbad is not a near miss through its callee"
missed d.log Bad.pde_bad Z.pos_div_eucl node || fail "(d) Bad.pde_bad is not a near miss for its constructor"
missed d.log Bad.leb_bad Nat.leb constructor || fail "(d) Bad.leb_bad is not a near miss for its constructor"
missed d.log Bad.OP.add Pos.add "callee is not a transparent definition" \
  || fail "(d) Bad.OP.add is not a near miss for its opaque callee"
for f in succ_bad zadd_swap add_bad add_carry_bad zadd_cbad pde_bad leb_bad OP.add OP.add_carry \
         mul_c pde_lv pde_lb; do
  ! grep -q "^binnum\[[0-9]*\] bind Bad\.$f: " "$d/d.log" || fail "(d) Bad.$f is bound"
done
case "$(first_diff d.log Bad.zadd_cbad Z.add)" in
  *"callee Pos.add >"*) ;;
  *) fail "(d) the first difference of Bad.zadd_cbad is not in its callee Pos.add" ;;
esac
# The callee of mul_c is function 1 of Pos.add's block, where the reference
# expects function 0; pde_lv and pde_lb differ from the reference in one
# variable, in a let value and in a let body.
missed d.log Bad.mul_c Pos.mul "fixpoint index" || fail "(d) Bad.mul_c is not a near miss for its callee's index"
missed d.log Bad.pde_lv Z.pos_div_eucl "de Bruijn index" || fail "(d) Bad.pde_lv is not a near miss for a variable"
missed d.log Bad.pde_lb Z.pos_div_eucl "de Bruijn index" || fail "(d) Bad.pde_lb is not a near miss for a variable"
top="fixpoint body 1 > lambda body > lambda body"
expect "(d) first difference of mul_c" "'$(first_diff d.log Bad.mul_c Pos.mul)'" = \
  "'$top > branch 1 > function > callee Pos.add'"
expect "(d) first difference of pde_lv" "'$(first_diff d.log Bad.pde_lv Z.pos_div_eucl)'" = \
  "'$top > branch 2 > branch 1 > let value > argument 2'"
expect "(d) first difference of pde_lb" "'$(first_diff d.log Bad.pde_lb Z.pos_div_eucl)'" = \
  "'$top > branch 2 > branch 1 > let body > branch 2 > argument 4 > argument 1'"

# (e) Refusals and reads. A lemma [l = l] makes rocqchk evaluate l twice ("per
# side"), a lemma [l = c] once. Each evaluation of l starts at a call site:
# BINNUMCALL runs the routine there. When it refuses, the call runs, and the
# routine runs again at the function's entry (BINNUM), unless GRABREC finds
# the recursive argument stuck first. A stuck fixpoint is read back by
# running its body on fresh variables (mk_fix_body, kernel/vmvalues.ml): its
# routine refuses that call at the entry, at the first variables it reads.
# Words: one per node read; Pos.add and Pos.add_carry read a node of each
# number per step, read_pos reads a number to its end (or to its first
# variable), z_node and nat_node one node.
#
# The counts asserted are those of the routine under test. The read-back of
# a stuck term also runs the branches of the matches it holds on fresh
# variables, and so calls other routines (Pos.succ in the read-back of
# Pos.add's block, for example); those counts follow from vconv's walk, not
# from the routine, and are not asserted.
#
# ecount LOG ROUTINE EHITS EREFUSALS EWORDS SHITS SREFUSALS SWORDS: the counts
# of ROUTINE at the entry, then at call sites.
ecount() {
  local ec er sc sr
  ec=$(stat "$1" "$2" entry-calls); er=$(stat "$1" "$2" entry-refusals)
  sc=$(stat "$1" "$2" site-calls); sr=$(stat "$1" "$2" site-refusals)
  expect "(e) $1 $2 entry hits" "$((ec - er))" -eq "$3"
  expect "(e) $1 $2 entry refusals" "$er" -eq "$4"
  expect "(e) $1 $2 entry words" "$(stat "$1" "$2" entry-words)" -eq "$5"
  expect "(e) $1 $2 site hits" "$((sc - sr))" -eq "$6"
  expect "(e) $1 $2 site refusals" "$sr" -eq "$7"
  expect "(e) $1 $2 site words" "$(stat "$1" "$2" site-words)" -eq "$8"
}
for lib in $ELIBS; do chk "$lib.log" -norec "$lib"; done
# Pos.succ (xO p) = xI p: hit at the call site, reads the xO, shares p.
ecount E1.log Pos.succ 0 0 0 1 0 1
# Pos.succ (xI p): per side, refused at p (2 words) at the call site and at
# the entry; the bytecode's succ p is stuck (GRABREC), and its read-back
# refused (1 word).
ecount E2.log Pos.succ 0 4 6 0 2 4
# Pos.add (xO p) 1 = xI p: hit at the call site, reads the two nodes, shares p.
ecount E3.log Pos.add 0 0 0 1 0 2
# Pos.add (xI p) 1: per side, the carry goes into p, refused there (3 words),
# at the call site and at the entry. The bytecode's xO (Pos.succ p) calls
# Pos.succ at a call site (refused, 1 word), whose GRABREC is stuck, and the
# read-back of that stuck Pos.succ is refused at the entry (1 word).
ecount E4.log Pos.add 0 2 6 0 2 6
ecount E4.log Pos.succ 0 2 2 0 2 2
# Pos.mul 4 p = xO (xO p): hit at the call site, reads 4, which is a power of
# two, shares p.
ecount E5.log Pos.mul 0 0 0 1 0 3
# Z.add Z0 y = y: hit at the call site, reads Z0 only.
ecount E6.log Z.add 0 0 0 1 0 1
# Z.compare (Zpos p) Z0 = Gt: hit at the call site, reads the two nodes.
ecount E7.log Z.compare 0 0 0 1 0 2
# Z.double (Zpos p) = Zpos (xO p): hit at the call site, shares p.
ecount E8.log Z.double 0 0 0 1 0 1
# Z.div2 (Zneg (xI p)) = Zneg (Pos.succ p): per side, refused at p (3 words),
# at the call site and at the entry; div2_up's call of Pos.succ p is refused
# at its call site, stuck in GRABREC, and refused in its read-back.
ecount E9.log Z.div2 0 2 6 0 2 6
ecount E9.log Pos.succ 0 2 2 0 2 2
# Nat.eqb (S (S n)) 3: per side, refused after 5 words at the call site and
# at the entry; then Nat.eqb (S n) 2 (a recursive call, so at the entry)
# after 3; Nat.eqb n 1 is stuck, and its read-back refused (1 word).
ecount E10.log Nat.eqb 0 6 18 0 2 10
# Nat.leb 0 n = true: hit at the call site, reads the 0 only.
ecount E11.log Nat.leb 0 0 0 1 0 1
# Z.pos_div_eucl 5 (Zneg 3) is refused (b <= 0) at the call site (4 words),
# then at the entries of a = 5 (4 words), 2 (3) and 1 (2); the bytecode then
# calls Z.leb 2 b (2 words), and, on the way up, Z.mul 2 r (2 words for
# r = 0, 4 for r = 3), Z.ltb r' b (2), Z.mul 2 q (4), Z.add (2 q) 1 (4),
# Z.sub r' b, through Z.add r' 3 (1 word for r' = 0, 7 for r' = 7), and
# Z.add (2 r) 1 (4), all at call sites of the body.
ecount E12.log Z.pos_div_eucl 0 3 9 0 1 4
ecount E12.log Z.leb 0 0 0 1 0 2
ecount E12.log Z.ltb 0 0 0 2 0 4
ecount E12.log Z.mul 0 0 0 4 0 14
ecount E12.log Z.add 0 0 0 5 0 20
# map (Z.add 3) [1; -5; 0]: Z.add 3 is a closure until map gives it its last
# argument (APPLY1, then the entry): 3 hits at the entry, 5 + 7 + 2 words.
ecount Partial.log Z.add 3 0 14 0 0 0
# Refusals where the bytecode still computes a constructor (l = c, c by cbv):
# Z.pos_sub (xI p) 1 = Zpos (xO p): read_pos reads xI and p (2 words) and
# refuses, at the call site and at the entry; the bytecode answers at the
# step (xI p, 1).
ecount Q1.log Z.pos_sub 0 1 2 0 1 2
# Z.compare (Zpos (xI p)) (Zpos 1) = Gt: the two Z nodes, then the comparison
# reads xI against xH (2) and the rest p of x (1): refused after 5 words, at
# the call site and at the entry; the bytecode calls Pos.compare, whose code
# applies compare_cont Eq to x' and y' (APPLY to its entry): refused after r,
# the step and p (4 words); the bytecode answers Gt at the step (xI p, 1).
ecount Q2.log Z.compare 0 1 5 0 1 5
ecount Q2.log Pos.compare_cont 0 1 4 0 0 0
# One probe per guard (B1 of the slice-2 review). Each is [l = l]: per side,
# the call site reads up to the variable and refuses; the call then runs and
# its entry refuses again after the same reads; then, for a fixpoint, the
# recursive call on the variable is stuck at GRABREC, and the read-back of
# that stuck fixpoint is refused at its first read (+1 entry refusal).
# Pos.pred_double (xO p): 2 words (xO, p); the recursion pred_double p is
# stuck: entry 2 x (2 + 1), site 2 x 2.
ecount P01.log Pos.pred_double 0 4 6 0 2 4
# Pos.add (xO p) 3: 4 words (xO, xI; p, xH); add p 1 is stuck; the read-back
# of the block reads both arguments (2 words): entry 2 x (4 + 2).
ecount P02.log Pos.add 0 4 12 0 2 8
# Pos.mul 3 p: read_pos x = 3 (2 words), not a power of two, then p (1):
# refused at 3 words; the bytecode's mul 1 p hits at the entry (reads 1, a
# power of two, 1 word): entry 2 x (3 refused + 1 hit).
ecount P03.log Pos.mul 2 2 8 0 2 6
# Pos.mul (xI p) 3: read_pos x reads xI and p (2 words); mul p 3 is stuck:
# entry 2 x (2 + 1).
ecount P04.log Pos.mul 0 4 6 0 2 4
# Pos.div2 p: 1 word, at the call site and at the entry (not a fixpoint).
ecount P05.log Pos.div2 0 2 2 0 2 2
# Pos.of_succ_nat (S n): 2 words (S, n); of_succ_nat n is stuck.
ecount P06.log Pos.of_succ_nat 0 4 6 0 2 4
# Z.double y, Z.succ_double y, Z.pred_double y: 1 word each.
ecount P07.log Z.double 0 2 2 0 2 2
ecount P08.log Z.succ_double 0 2 2 0 2 2
ecount P09.log Z.pred_double 0 2 2 0 2 2
# Z.pos_sub (xO p) 1: read_pos x reads xO and p (2 words); the bytecode's
# step (xO p, 1) makes no recursive call.
ecount P10.log Z.pos_sub 0 2 4 0 2 4
# Z.add y (Zpos 1): the node of y (1 word). Z.add (Zpos 1) y: both nodes (2).
ecount P11.log Z.add 0 2 2 0 2 2
ecount P12.log Z.add 0 2 4 0 2 4
# Z.add (Zpos (xO p)) (Zneg 1): two nodes, then pos_sub reads xO and p.
ecount P13.log Z.add 0 2 8 0 2 8
# Z.mul y (Zpos 3): 1 word. Z.mul (Zpos 3) y: 2. Z.mul (Zpos 3) (Zpos p): two
# nodes, 3 (2 words, not a power of two), then p (1): 5.
ecount P14.log Z.mul 0 2 2 0 2 2
ecount P15.log Z.mul 0 2 4 0 2 4
ecount P16.log Z.mul 0 2 10 0 2 10
# Z.compare y Z0: 1 word; Z.compare Z0 y: 2; Z.leb y Z0: 1; Z.ltb Z0 y: 2.
ecount P17.log Z.compare 0 2 2 0 2 2
ecount P18.log Z.compare 0 2 4 0 2 4
ecount P19.log Z.leb 0 2 2 0 2 2
ecount P20.log Z.ltb 0 2 4 0 2 4
# Z.eqb y Z0: 1 word; Z.eqb Z0 y: 2.
ecount P21.log Z.eqb 0 2 2 0 2 2
ecount P22.log Z.eqb 0 2 4 0 2 4
# Z.div2 y: 1 word; Z.div2 (Zpos p): the Zpos and p (2).
ecount P23.log Z.div2 0 2 2 0 2 2
ecount P24.log Z.div2 0 2 4 0 2 4
# Z.of_nat (S n): S and n (2 words).
ecount P25.log Z.of_nat 0 2 4 0 2 4
# Z.pos_div_eucl (xO p) (Zpos 3): read_pos a reads xO and p (2 words); the
# recursion on p is stuck: entry 2 x (2 + 1).
ecount P26.log Z.pos_div_eucl 0 4 6 0 2 4
# Z.pos_div_eucl 5 (Zpos (xO p)): a (3 words), the Zpos (1), xO and p (2):
# 6 words; the recursion runs on a = 2 (2 + 1 + 2 words) and a = 1
# (1 + 1 + 2), each refused at its entry: entry 2 x (6 + 5 + 4).
ecount P27.log Z.pos_div_eucl 0 6 30 0 2 12
# Nat.eqb 1 (S n): S, S, O, n (4 words); the recursive call Nat.eqb O n
# (O is not stuck) is refused at its entry after O and n (2).
ecount P28.log Nat.eqb 0 4 12 0 2 8
# Nat.leb (S n) 2: S, S, n (3 words); leb n 1 is stuck.
ecount P29.log Nat.leb 0 4 8 0 2 6
# Nat.leb 2 (S n): S, S, S, n (4 words); Nat.leb 1 n is refused at its entry
# after S and n (2); the stuck match on n runs its branch S m' on a fresh
# variable, whose Nat.leb O m' hits at the entry (1 word): entry
# 2 x (4 + 2 refused + 1 hit).
ecount P30.log Nat.leb 2 4 14 0 2 8
# Z.pos_sub (xO^70 p) 1: read_pos reads 70 nodes in its word, then in limbs,
# and p: 71 words; no recursive call at the step (xO _, 1).
ecount P31.log Z.pos_sub 0 2 142 0 2 142
# Pos.mul 3 (xO^70 p): 3 (2 words), then y to p (71): 73; the bytecode's
# mul 1 y hits at the entry (1 word): entry 2 x (73 + 1).
ecount P32.log Pos.mul 2 2 148 0 2 146
# Pos.add_carry (xO p) 3: 4 words; add_carry p 1 is stuck; the read-back of
# the block reads both arguments of add_carry (2): entry 2 x (4 + 2).
ecount P33.log Pos.add_carry 0 4 12 0 2 8

# (f) -j 2: the workers print their own counters.
chk f.log -j 2 -norec Diff
for r in $ROUTINES; do
  expect "(f) $r hits" "$(stat f.log "$r" hits)" -eq "$(count_of N "$r")"
done
expect "(f) binds" "$(recog f.log binds)" -eq "$binds_a"
pids=$(awk '$2 == "routine" { print $1 }' "$d/f.log" | sort -u | wc -l)
expect "(f) processes that print counters" "$pids" -ge 3
chk f2.log -j 2 -norec Copy
for r in $ROUTINES Pos.compare_cont Pos.eqb; do
  expect "(f) Copy $r hits" "$(stat f2.log "$r" hits)" -eq "$(count_of NC "$r")"
done

# (g) Large numbers, with a minor heap of 4096 words.
OCAMLRUNPARAM=s=4096 chk g.log -norec Big
for r in Pos.mul Pos.add Pos.add_carry Pos.succ Pos.pred_double Z.mul Z.add Z.pos_sub \
         Z.pos_div_eucl Pos.of_succ_nat; do
  expect "(g) $r hits" "$(stat g.log "$r" hits)" -eq "$(count_of NG "$r")"
  expect "(g) $r refusals" "$(stat g.log "$r" refusals)" -eq 0
done
# Chains over young shared bases, with a minor heap of 4096 words.
OCAMLRUNPARAM=s=4096 chk gs.log -norec BigShare
for r in Pos.succ Pos.mul Z.mul Z.succ_double; do
  expect "(g) shared $r hits" "$(stat gs.log "$r" hits)" -eq "$(count_of NS "$r")"
  expect "(g) shared $r refusals" "$(stat gs.log "$r" refusals)" -eq 0
done

# (h) The packing of literals on, as by default (rocqchk_binnum_literal.sh
# tests it): a literal is then read as one packed word, which changes the
# words above, but no routine makes or refuses another call.
for lib in Diff Copy Bad $ELIBS Big BigShare; do
  chk "h-$lib.log" -norec "$lib"
  ROCQ_VM_BINNUM_STATS=1 rocqchk -silent -bytecode-compiler yes -R "$d" "" -norec "$lib" \
    > "$d/h-$lib-lit.log" 2>&1 || { cat "$d/h-$lib-lit.log" >&2; fail "(h) rocqchk -norec $lib failed"; }
  for f in entry-calls entry-refusals site-calls site-refusals; do
    [ "$(per_routine "h-$lib.log" $f)" = "$(per_routine "h-$lib-lit.log" $f)" ] \
      || fail "(h) $lib: the $f of the routines change with the packing of literals"
  done
done

exit 0
