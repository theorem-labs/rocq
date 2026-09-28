#!/usr/bin/env bash
# rocqchk -j N checks opaque proofs in forked worker processes. It must accept
# the same libraries as rocqchk -j 1, and reject a library as soon as one of
# its opaque proofs is ill-typed, whichever process checks it.
#
# The ill-typed proof is made by splicing: two compilations that differ only
# in one lemma have opaque tables with the same layout, so the library segment
# of the first one (where the lemma has type U) together with the opaques
# segment of the second one (where its proof has type U -> U) makes a well
# formed .vo whose proof of that lemma does not have the type it claims.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
mkdir "$d/good" "$d/bad"

# Many opaque proofs, so that there is work for several workers.
gen() {
  echo 'Inductive T : Prop := I.'
  echo 'Definition U := T.'
  for i in $(seq 1 400); do
    if [ "$i" = 1 ] && [ "$1" = bad ]; then
      echo "Lemma l$i : forall x : U, U. Proof. exact (fun x => x). Qed."
    else
      echo "Lemma l$i : U. Proof. exact I. Qed."
    fi
    echo "Definition d$i := l$i."
  done
}
gen good > "$d/good/Lib.v"
gen bad > "$d/bad/Lib.v"
rocq c -native-compiler no -R "$d/good" "" "$d/good/Lib.v"
rocq c -native-compiler no -R "$d/bad" "" "$d/bad/Lib.v"

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
    out += struct.pack(">Q", 0)              # summary position placeholder
    summ = []
    for name in sorted(by):                  # CString.Map.iter order
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
vg, sg = parse(d + "/good/Lib.vo")
vb, sb = parse(d + "/bad/Lib.vo")
assert vg == vb, "vo_version mismatch"
assert sg["opaques"] != sb["opaques"], "opaques should differ"
spliced = dict(sg)
spliced["opaques"] = sb["opaques"]
write(d + "/Lib.vo", vg, spliced)
PY

for j in 1 2 4; do
  if ! rocqchk -j $j -R "$d/good" "" -norec Lib > "$d/good$j.log" 2>&1; then
    >&2 echo "FAILURE: rocqchk -j $j rejected a correct library"
    cat "$d/good$j.log" >&2
    exit 1
  fi
  grep -q "Modules were successfully checked" "$d/good$j.log"
done

# The first opaque proof is the ill-typed one, and it always goes to the first
# worker: the error is reported by that worker, then by the main process, which
# exits with the same code as with -j 1.
for j in 1 2 4; do
  R=0
  rocqchk -j $j -R "$d" "" -norec Lib > "$d/bad$j.log" 2>&1 || R=$?
  if [ $R = 0 ]; then
    >&2 echo "FAILURE: rocqchk -j $j accepted an ill-typed opaque proof"
    cat "$d/bad$j.log" >&2
    exit 1
  fi
  if [ $j = 1 ]; then R1=$R; fi
  if [ $R != $R1 ] ||
     grep -q "Modules were successfully checked" "$d/bad$j.log" ||
     ! grep -q "Type error" "$d/bad$j.log" ||
     { [ $j != 1 ] &&
       ! { grep -q "while checking the opaque proof of Lib.l1\.$" "$d/bad$j.log" &&
           grep -q "Worker process [0-9]* exited with code $R" "$d/bad$j.log"; }; }; then
    >&2 echo "FAILURE: rocqchk -j $j rejected the ill-typed proof, but not as expected"
    cat "$d/bad$j.log" >&2
    exit 1
  fi
done

# Profiling is sequential only.
rocqchk -j 2 -profile "$d/prof.json" -R "$d/good" "" -norec Lib > "$d/prof.log" 2>&1
grep -q "Option -j is ignored when profiling" "$d/prof.log" ||
  { >&2 echo "FAILURE: no warning about -j and -profile"; cat "$d/prof.log" >&2; exit 1; }

exit 0
