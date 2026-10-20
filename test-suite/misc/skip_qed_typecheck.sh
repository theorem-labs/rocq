#!/usr/bin/env bash
# -skip-qed-typecheck makes coqc skip the kernel's typechecking of opaque
# proofs at Qed. This checks that:
#  - an ill-typed proof (vm_cast_no_check with a wrong value) is rejected by
#    coqc without the option, accepted with it, then rejected by rocqchk, and
#    Print Assumptions reports it;
#  - the option reaches async proof workers;
#  - the library segment of each .vo, hence the digest a dependent records,
#    and rocqchk's context summary are the same with and without the option.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
line="has an opaque proof not checked by the kernel."

# 1. Rejection
mkdir "$d/bad"
cat > "$d/bad/Bad.v" <<'EOF'
Definition f (n : nat) : bool := Nat.eqb n 3.
Lemma bad : f 3 = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
EOF
if rocq c -q -R "$d/bad" "" "$d/bad/Bad.v" 2> "$d/err"; then
  >&2 echo "FAILURE: coqc accepted the ill-typed proof without the option"; exit 1
fi
rocq c -q -skip-qed-typecheck -R "$d/bad" "" "$d/bad/Bad.v"
if rocqchk -silent -R "$d/bad" "" Bad 2> "$d/err"; then
  >&2 echo "FAILURE: rocqchk accepted the ill-typed proof"; exit 1
fi
grep -q "Type error" "$d/err" || { >&2 echo "FAILURE: rocqchk rejected, but not as a type error"; cat "$d/err" >&2; exit 1; }
cat > "$d/bad/Use.v" <<'EOF'
Require Bad.
Print Assumptions Bad.bad.
EOF
rocq c -q -R "$d/bad" "" "$d/bad/Use.v" > "$d/out"
grep -qxF "Bad.bad $line" "$d/out" || { >&2 echo "FAILURE: Print Assumptions does not report Bad.bad"; cat "$d/out" >&2; exit 1; }

# 2. Async proof workers
mkdir "$d/async"
cp "$d/bad/Bad.v" "$d/async/Bad.v"
if rocq c -q -async-proofs on -R "$d/async" "" "$d/async/Bad.v" 2> "$d/err"; then
  >&2 echo "FAILURE: coqc -async-proofs on accepted the ill-typed proof without the option"; exit 1
fi
rocq c -q -async-proofs on -skip-qed-typecheck -R "$d/async" "" "$d/async/Bad.v"
cp "$d/bad/Use.v" "$d/async/Use.v"
rocq c -q -R "$d/async" "" "$d/async/Use.v" > "$d/out"
grep -qxF "Bad.bad $line" "$d/out" || { >&2 echo "FAILURE: an async worker did not record Bad.bad as unchecked"; cat "$d/out" >&2; exit 1; }

# 3. Identity of what dependents and rocqchk see, for several roots A and a
# dependent B. Besides plain proofs, the bodies of univ and counter add a
# monomorphic universe constraint and allocate fresh universe levels; both
# reach the universes of A and B, so they must not depend on the option.
# Both builds of a fixture use the same directory, since a .vo records its
# source path.
fixture() { # NAME A.v B.v
  mkdir "$d/$1" "$d/$1/src" "$d/$1/on" "$d/$1/off"
  printf '%s\n' "$2" > "$d/$1/src/A.v"
  printf '%s\n' "$3" > "$d/$1/src/B.v"
}
fixture basic 'Lemma a : forall n, n + 0 = n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.
Lemma a2 : 5 * 5 = 25.
Proof. abstract reflexivity. Qed.
Definition t := a 3.' 'Require Import A.
Lemma b : 3 + 0 = 3.
Proof. exact t. Qed.'
fixture univ 'Definition T1 := Type.
Definition T2 := Type.
Lemma l : True. Proof. pose (x := T1 : T2). exact I. Qed.' 'Require Import A.
Definition b := (T1 : T2).
Lemma bl : True. Proof. exact l. Qed.'
fixture counter 'Lemma l : True. Proof. pose (y := Type). pose (z := Type). exact I. Qed.
Definition T3 := Type.' 'Require Import A.
Definition b3 : Type := T3.
Lemma bl : True. Proof. exact l. Qed.'
fixture counter_unused 'Lemma l : True. Proof. pose (y := Type). pose (z := Type). exact I. Qed.
Definition T3 := Type.' 'Require Import A.
Lemma bl : True. Proof. exact l. Qed.'
for fx in basic univ counter counter_unused; do
  s="$d/$fx/src"
  for mode in on off; do
    opt=; [ $mode = on ] && opt=-skip-qed-typecheck
    rm -f "$s"/*.vo*
    for f in A B; do rocq c -q $opt -R "$s" "" "$s/$f.v"; done
    rocqchk -silent -o -R "$s" "" A B > "$d/$fx/chk-$mode" 2>&1
    grep -q "CONTEXT SUMMARY" "$d/$fx/chk-$mode" || { >&2 echo "FAILURE: $fx: no rocqchk context summary"; cat "$d/$fx/chk-$mode" >&2; exit 1; }
    cp "$s/A.vo" "$s/B.vo" "$d/$fx/$mode/"
  done
  cmp "$d/$fx/chk-on" "$d/$fx/chk-off" || { >&2 echo "FAILURE: $fx: rocqchk context summaries differ"; diff "$d/$fx/chk-on" "$d/$fx/chk-off" >&2; exit 1; }
done

python3 - "$d" <<'PY'
import sys, struct
d = sys.argv[1]
def segs(p):
    # layout per lib/objFile.ml; all ints big-endian
    b = open(p, "rb").read()
    (sp,) = struct.unpack_from(">Q", b, 8)
    off = sp
    (n,) = struct.unpack_from(">I", b, off); off += 4
    out = {}
    for _ in range(n):
        (nl,) = struct.unpack_from(">I", b, off); off += 4
        name = b[off:off+nl].decode(); off += nl
        pos, ln = struct.unpack_from(">QQ", b, off); off += 32
        out[name] = b[pos:pos+ln]
    return out
# The vmlibrary segment is not compared: its marshal sharing varies between
# ordinary runs.
for fx in ["basic", "univ", "counter", "counter_unused"]:
    for f in ["A", "B"]:
        on = segs(f"{d}/{fx}/on/{f}.vo")
        off = segs(f"{d}/{fx}/off/{f}.vo")
        # The library segment's MD5 is the digest a dependent records.
        for seg in ["library", "summary"]:
            if on[seg] != off[seg]:
                sys.exit(f"FAILURE: {fx}: {seg} segment of {f}.vo differs")
    if segs(f"{d}/{fx}/on/A.vo")["opaques"] == segs(f"{d}/{fx}/off/A.vo")["opaques"]:
        sys.exit(f"FAILURE: {fx}: opaques segment of A.vo does not record the option")
PY
exit 0
