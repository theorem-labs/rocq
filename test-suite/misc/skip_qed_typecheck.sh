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

# 3. Identity of what dependents and rocqchk see
# Both builds use the same directory, since a .vo records its source path.
mkdir "$d/src" "$d/on" "$d/off"
cat > "$d/src/A.v" <<'EOF'
Lemma a : forall n, n + 0 = n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.
Lemma a' : 5 * 5 = 25.
Proof. abstract reflexivity. Qed.
Definition t := a 3.
EOF
cat > "$d/src/B.v" <<'EOF'
Require Import A.
Lemma b : 3 + 0 = 3.
Proof. exact t. Qed.
EOF
for mode in on off; do
  opt=; [ $mode = on ] && opt=-skip-qed-typecheck
  rm -f "$d"/src/*.vo*
  for f in A B; do rocq c -q $opt -R "$d/src" "" "$d/src/$f.v"; done
  rocqchk -silent -o -R "$d/src" "" A B > "$d/chk-$mode"
  cp "$d/src/A.vo" "$d/src/B.vo" "$d/$mode/"
done
cmp "$d/chk-on" "$d/chk-off" || { >&2 echo "FAILURE: rocqchk context summaries differ"; diff "$d/chk-on" "$d/chk-off" >&2; exit 1; }

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
        pos, ln = struct.unpack_from(">QQ", b, off); off += 16
        h = b[off:off+16]; off += 16
        out[name] = (b[pos:pos+ln], h)
    return out
for f in ["A", "B"]:
    on = segs(f"{d}/on/{f}.vo")
    off = segs(f"{d}/off/{f}.vo")
    # The library segment's MD5 is the digest a dependent records.
    if on["library"] != off["library"]:
        sys.exit(f"FAILURE: library segment of {f}.vo differs")
    if on["summary"] != off["summary"]:
        sys.exit(f"FAILURE: summary segment of {f}.vo differs (dependency digests)")
    if on["opaques"] == off["opaques"]:
        sys.exit(f"FAILURE: opaques segment of {f}.vo does not record the option")
PY
exit 0
