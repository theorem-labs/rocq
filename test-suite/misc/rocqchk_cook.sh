#!/usr/bin/env bash
# rocqchk -j N defers the check of each opaque body. The body is fetched
# from its library's table, discharged (by CheckLibrary.indirect_accessor) and
# substituted (subst_mps_list) inside that deferred check, so in the
# process that checks it, and not in the main process before it is
# deferred. The count that -d checker-workers prints, "N cooked in the
# main process", is taken in the cook itself, so it says where the cook
# ran, not which branch of the code called it: a change that moved the
# cook of an ordinary body back into the main process would make it
# nonzero here. A constant of a sealed module whose signature declares it
# without a body is the exception: the main process records what its body
# uses (Mod_checking.register_opacified_constant), so it cooks that body
# itself, and still defers its check. At -j 1 the check runs at once, as
# before.
#
#  (a) Cook.v: sections with variables and a let, polymorphic lemmas with
#      private universes, a polymorphic section, a functor, its
#      applications, and Include. The -o output and the verdict are the
#      same at -j 1, 2 and 16; the main process cooks no body; every check
#      runs once;
#  (b) CookB.v: opaque bodies that point into Cook.vo's table, through a
#      functor of Cook applied here and through Include: the same;
#  (c) Sealed.v: a module sealed by a signature that declares Parameters,
#      which the module proves with Qed. Those bodies are cooked in the main
#      process (2), and the -o summary lists the axiom that the proof of one
#      of them uses, and not the Parameters themselves, at every -j;
#  (d) SecFail: an ill-typed opaque proof inside a section (the opaques
#      segment of another build of the file): coqchk fails at every -j with
#      the type error of -j 1, which -j N wraps in "while checking the
#      opaque proof of SecFail.s2";
#  (e) Many.v, 300 opaque proofs in a section and a functor: with
#      -worker-budget 0, every worker stops after one check, and the rest is
#      handed back and cooked by the worker that runs it; with the request
#      at each worker's entry (ROCQCHK_WORKER_RELEASE_AT=entry), workers
#      release their tails; in both, every check runs exactly once, and the
#      output is the one of -j 1.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT

d=$(mktemp -d)
mkdir "$d/good" "$d/bad" "$d/spliced"

cat > "$d/Cook.v" <<'EOF'
Section S.
  Variable A : Type.
  Variable a : A.
  Variable n : nat.
  Let k := S n.
  Lemma sec_a : a = a. Proof using a. reflexivity. Qed.
  Lemma sec_k : k = S n. Proof using n. reflexivity. Qed.
  Lemma sec_both : (a, n) = (a, n). Proof using a n. reflexivity. Qed.
  Lemma sec_none : 0 = 0. Proof using. reflexivity. Qed.
End S.

(* Private universes: the body uses a universe that the statement does
   not, so it is in the table, and the check adds it with push_subgraph. *)
Polymorphic Lemma pp@{u} (X : Type@{u}) : X -> X.
Proof. intro x. exact x. Qed.
Polymorphic Lemma ppriv@{u} (X : Type@{u}) : X -> X.
Proof. pose (T := Type). intro x. exact x. Qed.

Set Universe Polymorphism.
Section P.
  Universe w.
  Variable B : Type@{w}.
  Lemma psec (b : B) : b = b. Proof. pose (T := Type). reflexivity. Qed.
  Lemma psec2 (b : B) : (b, b) = (b, b). Proof. pose (T := Type -> Type). reflexivity. Qed.
End P.
Unset Universe Polymorphism.

Module Type T.
  Parameter m : nat.
  Axiom ax : m = m.
End T.

Module F (X : T).
  Lemma fl : X.m = X.m. Proof. reflexivity. Qed.
  Lemma fl2 : X.m + 0 = X.m + 0. Proof. reflexivity. Qed.
End F.

Module M.
  Definition m := 3.
  Lemma ax : m = m. Proof. reflexivity. Qed.
End M.

Module FM := F M.

Module G (X : T) (Y : T).
  Include F X.
  Lemma gl : Y.m = Y.m. Proof. reflexivity. Qed.
End G.

Module GM := G M M.

Lemma use_fm : M.m = M.m. Proof. exact FM.fl. Qed.
EOF

cat > "$d/CookB.v" <<'EOF'
Require Import Cook.

Module N.
  Definition m := 5.
  Lemma ax : m = m. Proof. reflexivity. Qed.
End N.

(* The opaque bodies of FN and H are Cook.F's, in Cook.vo's table. *)
Module FN := Cook.F N.
Module H.
  Include Cook.F Cook.M.
  Lemma h_own : Cook.M.m = Cook.M.m. Proof. reflexivity. Qed.
End H.
Module GN := Cook.G N Cook.M.

Lemma b_own : N.m = N.m. Proof. exact FN.fl. Qed.
EOF

cat > "$d/Sealed.v" <<'EOF'
Axiom ax_used : True.

Module Type S.
  Parameter p : True.
  Parameter q : nat -> nat.
  Axiom r : forall n, q n = q n.
End S.

(* p and r are declared without a body and proved with Qed: their bodies
   take the eager path. q is a transparent definition. extra is not in S. *)
Module M : S.
  Lemma p : True. Proof. exact ax_used. Qed.
  Definition q (n : nat) := n.
  Lemma r : forall n, q n = q n. Proof. reflexivity. Qed.
  Lemma extra : True. Proof. exact I. Qed.
End M.

Lemma use_p : True. Proof. exact M.p. Qed.
EOF

python3 - "$d" <<'PY'
import sys
d = sys.argv[1]
out = []
out.append("Section S.\n  Variable v : nat.\n")
for i in range(150):
    out.append("  Lemma s%d : v + %d = v + %d. Proof using v. reflexivity. Qed.\n" % (i, i, i))
out.append("End S.\n")
out.append("Module Type T. Parameter m : nat. End T.\n")
out.append("Module F (X : T).\n")
for i in range(75):
    out.append("  Lemma f%d : X.m + %d = X.m + %d. Proof. reflexivity. Qed.\n" % (i, i, i))
out.append("End F.\n")
out.append("Module A. Definition m := 1. End A.\nModule B. Definition m := 2. End B.\n")
out.append("Module FA := F A.\nModule FB := F B.\n")
for i in range(75):
    out.append("Lemma t%d : %d = %d. Proof. reflexivity. Qed.\n" % (i, i, i))
open(d + "/Many.v", "w").write("".join(out))

def secfail(bad):
    s = ["Section S.\n  Variable v : nat.\n",
         "  Lemma s1 : v = v. Proof using v. reflexivity. Qed.\n"]
    if bad:
        # Ill-typed once this opaques segment is put under the good library
        # segment: there s2 has type v + 0 = v + 0.
        s.append("  Lemma s2 : nat. Proof using v. exact v. Qed.\n")
    else:
        s.append("  Lemma s2 : v + 0 = v + 0. Proof using v. reflexivity. Qed.\n")
    s.append("  Lemma s3 : S v = S v. Proof using v. reflexivity. Qed.\nEnd S.\n")
    s.append("Lemma t1 : 0 = 0. Proof. reflexivity. Qed.\n")
    return "".join(s)

open(d + "/good/SecFail.v", "w").write(secfail(False))
open(d + "/bad/SecFail.v", "w").write(secfail(True))
PY

for lib in Cook CookB Sealed Many; do
  rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
done
rocq c -native-compiler no -R "$d/good" "" "$d/good/SecFail.v"
rocq c -native-compiler no -R "$d/bad" "" "$d/bad/SecFail.v"

# The library segment of the good SecFail.vo with the opaques segment of the
# bad one. Same splice as misc/rocqchk_parallel.sh.
python3 - "$d" <<'PY'
import sys, hashlib, struct
d = sys.argv[1]
MAGIC = 0x436F7121  # "Coq!"; all ints big-endian, layout per lib/objFile.ml
def parse(p):
    b = open(p, "rb").read()
    magic, ver = struct.unpack_from(">II", b, 0)
    assert magic == MAGIC, "bad magic"
    (sp,) = struct.unpack_from(">Q", b, 8)
    off = sp
    (n,) = struct.unpack_from(">I", b, off); off += 4
    segs = {}
    for _ in range(n):
        (nl,) = struct.unpack_from(">I", b, off); off += 4
        name = b[off:off+nl].decode(); off += nl
        pos, ln = struct.unpack_from(">QQ", b, off); off += 16
        h = b[off:off+16]; off += 16
        data = b[pos:pos+ln]
        assert hashlib.md5(data).digest() == h, name + ": bad segment MD5"
        segs[name] = data
    return ver, segs
def write(p, ver, by):
    out = bytearray()
    out += struct.pack(">II", MAGIC, ver)
    out += struct.pack(">Q", 0)
    summ = []
    for name in sorted(by):
        data = by[name]; pos = len(out); out += data
        h = hashlib.md5(data).digest(); out += h
        summ.append((name, pos, len(data), h))
    sp = len(out)
    out += struct.pack(">I", len(summ))
    for name, pos, ln, h in summ:
        nb = name.encode()
        out += struct.pack(">I", len(nb)); out += nb
        out += struct.pack(">QQ", pos, ln); out += h
    struct.pack_into(">Q", out, 8, sp)
    open(p, "wb").write(out)
vg, sg = parse(d + "/good/SecFail.vo")
vb, sb = parse(d + "/bad/SecFail.vo")
assert vg == vb, "vo_version mismatch"
assert sg["opaques"] != sb["opaques"], "opaques should differ"
spliced = dict(sg)
spliced["opaques"] = sb["opaques"]
write(d + "/spliced/SecFail.vo", vg, spliced)
PY

fail() { >&2 echo "FAILURE: $*"; exit 1; }

expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

# out NAME ARGS...: rocqchk as a user runs it, with -o: its standard output
# and error together, pids replaced, in $d/NAME.out. Exit code in $R.
R=0
out() {
  local name=$1; shift
  R=0
  rocqchk -o "$@" > "$d/$name.raw" 2>&1 || R=$?
  sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/$name.raw" > "$d/$name.out"
}

# dbg NAME ARGS...: rocqchk with the scheduling debug stream, for the counts.
dbg() {
  local name=$1; shift
  R=0
  rocqchk -silent -d checker-workers "$@" > "$d/$name.log" 2>&1 || R=$?
}

# done_field NAME FIELD: a number of the final "done:" line, which can be
# wrapped over several lines.
done_field() {
  tr -s ' \n\t' ' ' < "$d/$1.log" |
    grep -o 'done: [0-9]* workers forked, [0-9]* stopped early, [0-9]* released a tail, [0-9]* checks run of [0-9]* deferred, [0-9]* cooked in the main process' |
    tail -n 1 |
    awk -v f="$2" '{
      if (f == "forked") print $2; if (f == "stopped") print $5; if (f == "released") print $8;
      if (f == "run") print $12; if (f == "deferred") print $16; if (f == "cooked") print $18 }'
}

same() {
  diff -u "$d/$1.out" "$d/$2.out" > "$d/$2.diff" \
    || { cat "$d/$2.diff" >&2; fail "$3: the output differs from -j 1"; }
}

# (a), (b), (c): the output of -j 2 and -j 16 is the one of -j 1; the counts.
for lib in Cook CookB Sealed; do
  out "$lib-j1" -j 1 -R "$d" "" -norec "$lib"
  expect "($lib) -j 1 exit code" "$R" -eq 0
  [ -s "$d/$lib-j1.out" ] || fail "($lib) the output of -j 1 is empty"
  for j in 2 16; do
    out "$lib-j$j" -j $j -R "$d" "" -norec "$lib"
    expect "($lib) -j $j exit code" "$R" -eq 0
    same "$lib-j1" "$lib-j$j" "($lib) -j $j"
    dbg "$lib-d$j" -j $j -R "$d" "" -norec "$lib"
    expect "($lib) -j $j exit code with -d" "$R" -eq 0
    expect "($lib) -j $j checks run" "$(done_field "$lib-d$j" run)" -eq "$(done_field "$lib-d$j" deferred)"
    expect "($lib) -j $j checks deferred" "$(done_field "$lib-d$j" deferred)" -gt 0
    if [ "$lib" = Sealed ]; then
      expect "($lib) -j $j bodies cooked in the main process" "$(done_field "$lib-d$j" cooked)" -eq 2
    else
      expect "($lib) -j $j bodies cooked in the main process" "$(done_field "$lib-d$j" cooked)" -eq 0
    fi
  done
done

# (c) The summary: the Parameter p is implemented by a body that uses
# ax_used, so the axiom listed is ax_used, and neither M.p nor M.r is. The
# axioms part of the summary runs from "* Axioms:" to the next "* " line.
awk '/^\* Axioms:/ { f = 1; next } /^\* / { f = 0 } f' "$d/Sealed-j1.out" > "$d/axioms"
[ "$(tr -d ' ' < "$d/axioms" | grep -v '^$')" = "Sealed.ax_used" ] \
  || { cat "$d/Sealed-j1.out" >&2; fail "(c) the axioms listed are not exactly Sealed.ax_used"; }

# (d) An ill-typed opaque proof inside a section. The first error printed
# is the one of the proof: at -j 1 the type error, with workers the same
# text and a line naming the proof. The main process's second error, which
# names the failing worker's batch, depends on the schedule and is not
# compared (as in misc/rocqchk_release.sh (e)).
errblock() {
  awk '/^Fatal Error/ { n++ } n == 1' "$d/$1.out"
}
out SecFail-j1 -j 1 -R "$d/spliced" "" -norec SecFail
expect "(d) -j 1 exit code" "$R" -ne 0
errblock SecFail-j1 > "$d/err1"
grep -q "Type error" "$d/err1" || { cat "$d/SecFail-j1.out" >&2; fail "(d) no type error at -j 1"; }
for j in 2 16; do
  out "SecFail-j$j" -j $j -R "$d/spliced" "" -norec SecFail
  expect "(d) -j $j exit code" "$R" -ne 0
  errblock "SecFail-j$j" > "$d/err$j"
  grep -qx " *while checking the opaque proof of SecFail.s2\." "$d/err$j" \
    || { cat "$d/SecFail-j$j.out" >&2; fail "(d) -j $j did not name SecFail.s2"; }
  grep -v "while checking the opaque proof of" "$d/err$j" > "$d/err$j.1"
  diff -u "$d/err1" "$d/err$j.1" > "$d/err$j.diff" \
    || { cat "$d/err$j.diff" >&2; fail "(d) the error text of -j $j differs from -j 1"; }
done

# (e) Checks handed back, by budget stops and by releases.
out Many-j1 -j 1 -R "$d" "" -norec Many
expect "(e) -j 1 exit code" "$R" -eq 0
out Many-b0 -j 4 -worker-budget 0 -R "$d" "" -norec Many
expect "(e) -worker-budget 0 exit code" "$R" -eq 0
same Many-j1 Many-b0 "(e) -worker-budget 0"
dbg Many-db0 -j 4 -worker-budget 0 -R "$d" "" -norec Many
expect "(e) -worker-budget 0 exit code with -d" "$R" -eq 0
expect "(e) -worker-budget 0 workers stopped early" "$(done_field Many-db0 stopped)" -gt 0
expect "(e) -worker-budget 0 checks deferred" "$(done_field Many-db0 deferred)" -ge 300
expect "(e) -worker-budget 0 checks run" "$(done_field Many-db0 run)" -eq "$(done_field Many-db0 deferred)"
expect "(e) -worker-budget 0 bodies cooked in the main process" "$(done_field Many-db0 cooked)" -eq 0
ROCQCHK_WORKER_RELEASE_AT=entry out Many-rel -j 4 -R "$d" "" -norec Many
expect "(e) release at entry exit code" "$R" -eq 0
same Many-j1 Many-rel "(e) release at entry"
ROCQCHK_WORKER_RELEASE_AT=entry dbg Many-drel -j 4 -R "$d" "" -norec Many
expect "(e) release at entry exit code with -d" "$R" -eq 0
expect "(e) release at entry: tails released" "$(done_field Many-drel released)" -gt 0
expect "(e) release at entry: checks run" "$(done_field Many-drel run)" -eq "$(done_field Many-drel deferred)"

exit 0
