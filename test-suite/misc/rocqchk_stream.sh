#!/usr/bin/env bash
# With workers, when every library to check is named with -norec, rocqchk
# checks each library as soon as the libraries it depends on are read,
# without waiting until it has read them all. That must not change what it
# prints or how it ends. Each case runs that way and the way that reads
# every library first, which -admit of a library already admitted forces
# without changing which libraries are checked, and compares the two.
#
# rocqchk reads the -norec libraries from the last named to the first, so
# the library named last is read, and checked, first.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
mkdir "$d/src" "$d/good" "$d/bad"

gen() {
  echo 'Inductive T : Prop := I.'
  echo 'Definition U := T.'
  for i in $(seq 1 200); do
    if [ "$i" = 1 ] && [ "$1" = bad ]; then
      echo "Lemma l$i : forall x : U, U. Proof. exact (fun x => x). Qed."
    else
      echo "Lemma l$i : U. Proof. exact I. Qed."
    fi
    echo "Definition d$i := l$i."
  done
}

for n in A B C Magic; do gen good > "$d/src/$n.v"; done
gen good > "$d/good/Bad.v"
gen bad > "$d/bad/Bad.v"
for n in A B C Magic; do rocq c -native-compiler no -R "$d/src" "" "$d/src/$n.v"; done
rocq c -native-compiler no -R "$d/good" "" "$d/good/Bad.v"
rocq c -native-compiler no -R "$d/bad" "" "$d/bad/Bad.v"

# Bad.vo: the library segment of the good compilation with the opaques
# segment of the bad one, so its proof of l1 does not have the type it
# claims (see rocqchk_parallel.sh). Magic.vo: a wrong magic number, which
# rocqchk refuses when it reads the file.
python3 - "$d" <<'PY'
import hashlib, struct, sys
d = sys.argv[1]
MAGIC = 0x436F7121
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
vg, sg = parse(d + "/good/Bad.vo")
vb, sb = parse(d + "/bad/Bad.vo")
assert vg == vb and sg["opaques"] != sb["opaques"]
spliced = dict(sg)
spliced["opaques"] = sb["opaques"]
write(d + "/src/Bad.vo", vg, spliced)
with open(d + "/src/Magic.vo", "r+b") as f:
    f.write(b"Bad!")
PY

# A library that every case reads and admits anyway.
leaf=Corelib.Init.Notations

fail=0
# compare <case> <how> <rocqchk arguments...>: <how> is "all" (standard
# output and standard error, each whole, and the exit code) or "error" (the
# error lines, the proof they name and the exit code: with workers, which
# batch is named, the process ids, and how far the walk printed before the
# error depend on timing either way).
compare() {
  local case="$1" how="$2"; shift 2
  local r1=0 r2=0
  rocqchk -j 4 "$@" > "$d/stream.out" 2> "$d/stream.err" || r1=$?
  rocqchk -j 4 "$@" -admit "$leaf" > "$d/first.out" 2> "$d/first.err" || r2=$?
  cat "$d/stream.out" "$d/stream.err" > "$d/stream.log"
  if [ "$how" = error ]; then
    for f in stream first; do
      { grep -E 'Fatal Error|Error:|Type error|while checking the opaque proof|bad magic' \
          "$d/$f.out" "$d/$f.err" | sed -e "s#^$d/$f\.##" \
          -e 's/Worker process [0-9]*/Worker process PID/' | sort -u; } > "$d/$f.cmp"
    done
  else
    for f in stream first; do
      { echo "-- standard output"; cat "$d/$f.out"
        echo "-- standard error"; cat "$d/$f.err"; } > "$d/$f.cmp"
    done
  fi
  if [ "$r1" != "$r2" ] || ! cmp -s "$d/stream.cmp" "$d/first.cmp"; then
    echo "$case: differs (exit codes $r1 and $r2)"
    diff -u "$d/first.cmp" "$d/stream.cmp" | head -40 || true
    fail=1
  else
    echo "$case: same (exit code $r1)"
  fi
  # A case is only a test if it ends the way it should.
  case "$case" in
    correct*) [ "$r1" = 0 ] || { echo "$case: expected exit code 0"; fail=1; } ;;
    *) [ "$r1" != 0 ] || { echo "$case: expected a failure"; fail=1; } ;;
  esac
}

compare "correct libraries" all -R "$d/src" "" -norec A -norec B -norec C
# Bad is read and checked first, while Magic, read last, fails: stock fails
# on Magic before it checks anything.
compare "ill-typed proof, then a file that cannot be read" all \
  -R "$d/src" "" -norec Magic -norec A -norec B -norec Bad
# The run that reads every library first checks nothing before Magic fails,
# so the two being the same already shows the intern's error comes first;
# the ill-typed proof must not be reported.
if grep -q -e 'Type error' -e 'while checking the opaque proof' "$d/stream.log"; then
  echo "the ill-typed proof was reported before the file that cannot be read"
  tail -n 20 "$d/stream.log"; fail=1
fi
compare "ill-typed proof" error -R "$d/src" "" -norec A -norec B -norec Bad
grep -q 'while checking the opaque proof of Bad.l1\.' "$d/stream.log" ||
  { echo "expected the proof of Bad.l1 to be reported"; fail=1; }
# Without a directory for the files that hold a worker's output, workers
# print at once: rocqchk then reads every library first, and reports the
# failing worker as it does then.
TMPDIR="$d/none" compare "ill-typed proof, no files for workers' output" error \
  -R "$d/src" "" -norec A -norec B -norec Bad
grep -q 'Worker process' "$d/stream.log" ||
  { echo "expected the failing worker to be reported"; fail=1; }

exit $fail
