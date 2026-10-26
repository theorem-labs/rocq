#!/usr/bin/env bash
# The main process never reads the opaque proofs of a library when a
# worker will. When it interns one it reads the bytes of the "opaques"
# segment and the digest stored after it once, without parsing them, and
# keeps their MD5. The table is read on first use, in the process that
# needs it: a worker, or the main process when it could not fork. That
# process reads the same range again and compares its MD5 with the one
# the main process recorded, then reads the table with stock's own code.
# At -j 1 no other process can read it, so the table is parsed where
# stock parses it, when the library is interned.
#
# Stock parses every interned library's table when it interns it, so a
# malformed table fails coqchk even when nothing reads it. One deferred
# task reads each table the same way, so the verdicts stay stock's.
#
#  (a) the verdict, the exit code and the -o output of -j 2, 4 and 16 are
#      the ones of -j 1, and the main process parses no table at all;
#  (b) every table is read: tables read equals tables deferred, and the
#      workers parse between one and two times as many tables, where a
#      stride of the jobs would parse them once per check;
#  (c) a corrupted table in a checked library with no opaque constant of
#      its own: coqchk fails, at every -j, as stock does at intern time;
#  (d) the same in a dependency interned without validation, which stock
#      reads with Marshal.from_channel;
#  (e) the same in an admitted dependency;
#  (f) a crafted table whose marshalled data claims more than its segment
#      holds: the read goes on into the file, where stock's read from the
#      channel goes on, and the verdict is the same at every -j;
#  (g) an ill-typed opaque proof is rejected at every -j;
#  (h) -admit and -norec mixes, and a library read only as a dependency:
#      the output of -j 1;
#  (i) two workers that read one segment at the same time;
#  (j) the bytes of a table changed, after the main process read them, to
#      another table that is just as long and just as correct: the MD5
#      comparison fails and coqchk fails;
#  (l) only the opaques length in the table of segments is wrong (past the
#      end of the file, zero, negative), the payload and its digests
#      intact: stock never reads that length and accepts the file, and so
#      must this build, at -j 1, 2, 4 and 16, for a checked library, a
#      dependency read without validation, and an admitted dependency;
#  (m) the table is a valid marshalled value of the wrong type, and (n)
#      the digest stored after it differs: stock refuses both where it
#      validates and accepts both where it does not;
#  (o) every file above against stock, at every -j: the exit code and the
#      output, but for the line that names the batch of a failing worker;
#  (p) a value that runs past its segment on the path that does not
#      validate, which (f) covers only where it validates;
#  (q) a segment that starts in the last bytes of the file: an absent
#      marshal header and one cut short are reported as stock reports
#      them;
#  (r) a segment that does not start in the file at all;
#  (s) two libraries damaged in different ways: the refusal stock reports,
#      which is the table it could not read;
#  (t) a marshal header that claims more data than an int holds;
#  (u) damaged bytes in the table of a dependency that is not validated,
#      which stock never accepts;
#  (v) a declared length that covers a 2 GiB tail, under a 4 GiB
#      address-space limit;
#  (w) a damaged table together with something else that is wrong, found
#      in the same file, later in the walk, or in another library: the
#      error stock reports, which is the first table it could not read.
#
# (i) and (j) open their window with ROCQCHK_OPAQUE_AT=before:lib:dir,
# which stops a process before it reads the table of [lib] until the test
# lets it go, so that they need no timing.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_OPAQUE_AT

d=$(mktemp -d)
mkdir "$d/src" "$d/good"

fail() { >&2 echo "FAILURE: $*"; exit 1; }
expect() { [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"; }

# The libraries. Op has a handful of opaque proofs, Big enough of them for
# its jobs to fill several batches, NoOp none at all, and Use reads one of
# Dep's through a Definition, so that Dep's table is needed only if a check
# reaches it. M1 to M12 are twelve libraries of ten opaque proofs each, for
# the batches of (b).
{
  echo 'Inductive T : Prop := I.'
  echo 'Definition U := T.'
  for i in 1 2 3; do
    echo "Lemma l$i : U. Proof. exact I. Qed."
    echo "Definition d$i := l$i."
  done
} > "$d/src/Op.v"
{
  echo 'Inductive T : Prop := I.'
  for i in $(seq 1 100); do
    echo "Lemma b$i : T. Proof. exact I. Qed."
  done
} > "$d/src/Big.v"
{
  echo 'Inductive T : Prop := I.'
  echo 'Definition x := I.'
  echo 'Definition y := x.'
} > "$d/src/NoOp.v"
# Use reads Dep's opaque proof through a Definition, so Dep's table is
# needed only when a check reaches it.
{
  echo 'Inductive T : Prop := I.'
  echo 'Lemma dep : T. Proof. exact I. Qed.'
} > "$d/src/Dep.v"
{
  echo 'Require Import Dep.'
  echo 'Definition use := Dep.dep.'
  echo 'Lemma here : Dep.T. Proof. exact Dep.dep. Qed.'
} > "$d/src/Use.v"
# The ill-typed variant of Op: same table layout, l1 proved by a function.
sed 's/^Lemma l1 : U\. Proof\. exact I\. Qed\.$/Lemma l1 : forall x : U, U. Proof. exact (fun x => x). Qed./' \
  "$d/src/Op.v" > "$d/src/OpBad.v"

for i in $(seq 1 12); do
  {
    echo 'Inductive T : Prop := I.'
    for k in $(seq 1 10); do echo "Lemma m$k : T. Proof. exact I. Qed."; done
  } > "$d/src/M$i.v"
done
# Swap, and a second Swap whose proofs of s1 and s2 are exchanged: its
# table is just as long, and just as correct, but its bytes differ, for
# (j). (Two equal proofs would be shared in one table and not in the
# other, which would change its length.)
mkdir "$d/src/swapj"
swap() {
  echo 'Inductive T : Prop := I | J.'
  echo "Lemma s1 : T. Proof. exact $1. Qed."
  echo "Lemma s2 : T. Proof. exact $2. Qed."
}
swap I J > "$d/src/Swap.v"
swap J I > "$d/src/swapj/Swap.v"
# Wide has a table larger than a channel's buffer (64 KB), for (o): three
# proofs of 3000 nested lets each, with different binder names, so that
# nothing is shared between them.
{
  echo 'Inductive T : Prop := I.'
  for h in Ha Hb Hc; do
    echo "Lemma w$h : T. Proof. do 3000 (pose proof I as $h; clear $h); exact I. Qed."
  done
} > "$d/src/Wide.v"
# UseNoOp reads nothing of NoOp but a transparent definition, so NoOp's
# table is read only by its table task, for (m) and (n). UseOp depends on
# Op, for (w).
echo 'Require Import NoOp. Definition z := NoOp.x.' > "$d/src/UseNoOp.v"
echo 'Require Import Op. Definition z := Op.d2.' > "$d/src/UseOp.v"
for v in Op Big NoOp UseNoOp UseOp Dep Use Swap Wide $(seq -f 'M%.0f' 1 12); do
  rocq c -native-compiler no -R "$d/src" "" "$d/src/$v.v"
done
rocq c -native-compiler no -R "$d/src/swapj" "" "$d/src/swapj/Swap.v"
mkdir "$d/src/bad"
sed 's/^Definition d1 := l1\.$/Definition d1 := l1 I./' "$d/src/OpBad.v" > "$d/src/bad/Op.v"
rocq c -native-compiler no -R "$d/src/bad" "" "$d/src/bad/Op.v"
cp "$d/src"/*.vo "$d/good/"

# Reading and rewriting the segments of a .vo, as lib/objFile.ml lays them
# out. "corrupt" and "truncate" write a whole file whose stored hashes
# match its data, so the only thing wrong with it is the data of that
# segment; "replace" overwrites the bytes of one segment where they are,
# which a file being checked needs.
cat > "$d/vo.py" <<'PY'
import hashlib, os, struct, sys
MAGIC = 0x436F7121  # "Coq!"; all ints big-endian, layout per lib/objFile.ml

def parse(p):
    b = open(p, "rb").read()
    magic, ver = struct.unpack_from(">II", b, 0)
    assert magic == MAGIC, "bad magic"
    (sp,) = struct.unpack_from(">Q", b, 8)
    off = sp
    (n,) = struct.unpack_from(">I", b, off); off += 4
    segs, where = {}, {}
    for _ in range(n):
        (nl,) = struct.unpack_from(">I", b, off); off += 4
        name = b[off:off+nl].decode(); off += nl
        pos, ln = struct.unpack_from(">QQ", b, off); off += 16
        h = b[off:off+16]; off += 16
        data = b[pos:pos+ln]
        assert hashlib.md5(data).digest() == h, name + ": bad segment MD5"
        segs[name] = data
        where[name] = (pos, ln)
    return ver, segs, where

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

def summary_entry(data, name):
    # The offset of the (position, length) pair of one segment's summary.
    (off,) = struct.unpack_from(">Q", data, 8)
    (n,) = struct.unpack_from(">I", data, off); off += 4
    for _ in range(n):
        (nl,) = struct.unpack_from(">I", data, off); off += 4
        got = bytes(data[off:off+nl]).decode(); off += nl
        if got == name:
            return off
        off += 32
    raise RuntimeError("missing segment " + name)

cmd = sys.argv[1]
if cmd == "corrupt":
    # Data of that segment replaced by bytes that are not a marshalled
    # value, of the same length.
    p, name = sys.argv[2], sys.argv[3]
    ver, segs, _ = parse(p)
    segs[name] = b"\x7f" * len(segs[name])
    write(p, ver, segs)
elif cmd == "truncate":
    # The last [n] bytes of the data dropped: its marshal header then
    # claims more than the segment holds.
    p, name, n = sys.argv[2], sys.argv[3], int(sys.argv[4])
    ver, segs, _ = parse(p)
    assert len(segs[name]) > n, name + ": too short to truncate"
    segs[name] = segs[name][:-n]
    write(p, ver, segs)
elif cmd == "splice":
    # The library segment of the first file with the opaques segment of the
    # second: a well formed .vo whose proof of l1 does not have the type it
    # claims.
    good, bad, out = sys.argv[2], sys.argv[3], sys.argv[4]
    vg, sg, _ = parse(good)
    vb, sb, _ = parse(bad)
    assert vg == vb, "vo_version mismatch"
    assert sg["opaques"] != sb["opaques"], "opaques should differ"
    sg = dict(sg); sg["opaques"] = sb["opaques"]
    write(out, vg, sg)
elif cmd == "replace":
    # The data of a segment overwritten where it is by the data of the same
    # segment of another file, of the same length; the digest stored after
    # it is kept. The file still parses, validates and checks: only the MD5
    # of its bytes tells it changed.
    p, other, name = sys.argv[2], sys.argv[3], sys.argv[4]
    _, _, where = parse(p)
    _, so, _ = parse(other)
    pos, ln = where[name]
    assert len(so[name]) == ln, name + ": not the same length"
    with open(p, "r+b") as f:
        f.seek(pos); f.write(so[name]); f.flush(); os.fsync(f.fileno())
elif cmd == "size":
    _, _, where = parse(sys.argv[2])
    print(where[sys.argv[3]][1])
elif cmd in ("length", "position"):
    # Change only the length, or only the position, in one segment
    # summary. The payload, the other field, the stored segment digest
    # and the trailing digest stay byte-for-byte intact: stock's reader
    # ignores the length, and seeks to the position.
    p, name, v = sys.argv[2], sys.argv[3], int(sys.argv[4])
    data = bytearray(open(p, "rb").read())
    off = summary_entry(data, name)
    struct.pack_into(">q", data, off + (8 if cmd == "length" else 0), v)
    open(p, "wb").write(data)
elif cmd == "hugehdr":
    # The segment replaced by a marshal header of the long format, and
    # nothing else, whose data length no OCaml int holds. The stored
    # hashes are rewritten to match it, so the only thing wrong with the
    # file is what that header claims.
    p, name = sys.argv[2], sys.argv[3]
    ver, segs, _ = parse(p)
    segs[name] = (struct.pack(">II", 0x8495A6BF, 0)
                  + struct.pack(">QQQ", 0x7FFFFFFFFFFFFF00, 0x100, 0x100))
    write(p, ver, segs)
elif cmd == "poke":
    # Bytes of a segment's data changed at an offset, every stored hash
    # rewritten to match, so the file is well framed and only the
    # marshalled value is damaged.
    p, name, off, blob = sys.argv[2], sys.argv[3], int(sys.argv[4]), bytes.fromhex(sys.argv[5])
    ver, segs, _ = parse(p)
    data = bytearray(segs[name])
    data[off:off+len(blob)] = blob
    segs[name] = bytes(data)
    write(p, ver, segs)
elif cmd == "pad":
    # The file made longer by [n] zero bytes after everything it holds,
    # without writing them (a sparse tail).
    p, n = sys.argv[2], int(sys.argv[3])
    with open(p, "r+b") as f:
        f.seek(0, 2); f.truncate(f.tell() + n)
elif cmd == "wrongtype":
    # The opaques segment replaced by the data of another segment: a valid
    # marshalled value, of the wrong type. The stored hashes are rewritten
    # to match it.
    p, name, other = sys.argv[2], sys.argv[3], sys.argv[4]
    ver, segs, _ = parse(p)
    segs[name] = segs[other]
    write(p, ver, segs)
elif cmd == "digest":
    # The 16 bytes stored after a segment's data overwritten where they are:
    # the data and the table's hash of it stay intact, and only the digest
    # that stock compares after the parse of a validated library differs.
    p, name = sys.argv[2], sys.argv[3]
    _, _, where = parse(p)
    pos, ln = where[name]
    with open(p, "r+b") as f:
        f.seek(pos + ln); f.write(b"\x00" * 16)
elif cmd == "ocaml":
    # The OCaml version that the summary names, replaced by zeros of the
    # same length, the stored hashes rewritten to match.
    import re
    p = sys.argv[2]
    ver, segs, _ = parse(p)
    m = re.search(rb"[0-9]+\.[0-9]+\.[0-9]+", segs["summary"])
    assert m, "no OCaml version in the summary"
    s = segs["summary"]
    segs["summary"] = s[:m.start()] + b"0" * (m.end() - m.start()) + s[m.end():]
    write(p, ver, segs)
PY

vo() { python3 "$d/vo.py" "$@"; }

# run NAME ARGS...: coqchk as a user runs it, with -o, standard output and
# error together and pids replaced. Exit code in $R.
R=0
run() {
  local name=$1; shift
  R=0
  coqchk -o "$@" > "$d/$name.raw" 2>&1 || R=$?
  sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/$name.raw" > "$d/$name.out"
}

# dbg NAME ARGS...: the same with the scheduling debug stream, whose
# messages can be wrapped, so whitespace is collapsed into $d/NAME.flat.
dbg() {
  local name=$1; shift
  R=0
  coqchk -silent -d checker-workers "$@" > "$d/$name.log" 2>&1 || R=$?
  tr -s '[:space:]' ' ' < "$d/$name.log" > "$d/$name.flat"
}

same() {
  diff -u "$d/$1.out" "$d/$2.out" > "$d/$2.diff" \
    || { cat "$d/$2.diff" >&2; fail "$3: the output differs from $1"; }
}

# field FLAT REGEX: the capture of the last match of REGEX in FLAT.
field() { sed -n "s/.*$2.*/\1/p" "$1" | tail -1; }

LIB=(-R "$d/good" "")

# (a) Every -j gives the output of -j 1, and the main process parses no
# table once there are workers to do it.
for j in 1 2 4 16; do
  run "a$j" -j $j "${LIB[@]}" -norec Op -norec Big -norec NoOp -norec Use
  expect "(a) -j $j exit code" "$R" -eq 0
  [ "$j" = 1 ] || same a1 "a$j" "(a) -j $j"
done
for j in 2 4 16; do
  dbg "a$j" -j $j "${LIB[@]}" -norec Op -norec Big -norec NoOp -norec Use
  expect "(a) -j $j exit code with -d" "$R" -eq 0
  read=$(field "$d/a$j.flat" 'tables: \([0-9]*\) read of')
  deferred=$(field "$d/a$j.flat" 'tables: [0-9]* read of \([0-9]*\) deferred')
  main=$(field "$d/a$j.flat" 'deferred, \([0-9]*\) parsed in the main process')
  expect "(a) -j $j tables read" "$read" -eq "$deferred"
  expect "(a) -j $j tables deferred" "$deferred" -ge 5
  expect "(a) -j $j tables parsed in the main process" "$main" -eq 0
  expect "(a) -j $j bytes read in the main process" \
    "$(field "$d/a$j.flat" 'parsed in the main process, \([0-9]*\) bytes')" -eq 0
done

# (b) A batch holds whole libraries, so the table its checks read is
# parsed once for all of them. Twelve libraries of ten opaque proofs each
# make 120 checks: a stride of the queue would put checks of most of the
# twelve in every batch, and parse the tables again in each of them. Here
# the parses stay close to the number of tables; the ones above it are the
# tail of the queue, where a batch is shorter than a library's jobs.
MODS=()
for i in $(seq 1 12); do MODS+=(-norec "M$i"); done
dbg b -j 4 -worker-budget 60 "${LIB[@]}" "${MODS[@]}"
expect "(b) exit code" "$R" -eq 0
deferred=$(field "$d/b.flat" 'tables: [0-9]* read of \([0-9]*\) deferred')
expect "(b) tables deferred" "$deferred" -ge 12
expect "(b) checks run" "$(field "$d/b.flat" 'a tail, \([0-9]*\) checks run of')" -eq 120
# Every parse of a table is a worker's, and none is parsed by the main
# process: the two counts come from different lines.
total=$(grep -o 'parsed [0-9]* opaque table' "$d/b.flat" | awk '{ s += $2 } END { print s + 0 }')
expect "(b) tables parsed by workers" "$total" -ge "$deferred"
expect "(b) tables parsed by workers" "$total" -le "$(( 2 * deferred ))"
expect "(b) tables parsed in the main process" \
  "$(field "$d/b.flat" 'deferred, \([0-9]*\) parsed in the main process')" -eq 0

# (c) A corrupted table in a checked library that has no opaque constant.
# Stock fails on it when it interns it; here the worker that reads every
# table before the walk fails (validate_tables).
for case in NoOp:c Dep:d; do
  lib=${case%%:*}; tag=${case##*:}
  rm -rf "$d/$tag"; cp -a "$d/good" "$d/$tag"
  vo corrupt "$d/$tag/$lib.vo" opaques
  for j in 1 2 16; do
    case $tag in
      c) run "$tag$j" -j $j -R "$d/$tag" "" -norec NoOp -norec Op ;;
      d) run "$tag$j" -j $j -R "$d/$tag" "" -norec Use ;;
    esac
    expect "($tag) -j $j exit code" "$R" -eq 1
    grep -qi "corrupted\|Try to rebuild" "$d/$tag$j.out" \
      || { cat "$d/$tag$j.out" >&2; fail "($tag) -j $j did not report a corrupted file"; }
  done
done

# (e) The same in an admitted dependency. Stock reads its table with
# Marshal.from_channel and fails; so does the deferred task.
rm -rf "$d/e"; cp -a "$d/good" "$d/e"
vo corrupt "$d/e/Dep.vo" opaques
for j in 1 2 16; do
  run "e$j" -j $j -R "$d/e" "" -admit Dep -norec Use
  expect "(e) -j $j exit code" "$R" -eq 1
  grep -qi "corrupted\|Try to rebuild" "$d/e$j.out" \
    || { cat "$d/e$j.out" >&2; fail "(e) -j $j did not report a corrupted file"; }
done

# (f) A table whose marshalled data claims more than its segment holds.
# The read goes on into the file, as stock's read from the channel does,
# and the verdict is the same whichever process reads it.
rm -rf "$d/f"; cp -a "$d/good" "$d/f"
vo truncate "$d/f/Op.vo" opaques 8
for j in 1 2 16; do
  run "f$j" -j $j -R "$d/f" "" -norec Op
  expect "(f) -j $j exit code" "$R" -eq 1
  grep -qi "corrupted\|Try to rebuild" "$d/f$j.out" \
    || { cat "$d/f$j.out" >&2; fail "(f) -j $j did not report a corrupted file"; }
done

# (g) An ill-typed opaque proof, rejected at every -j.
rm -rf "$d/g"; cp -a "$d/good" "$d/g"
vo splice "$d/good/Op.vo" "$d/src/bad/Op.vo" "$d/g/Op.vo"
for j in 1 2 16; do
  run "g$j" -j $j -R "$d/g" "" -norec Op
  expect "(g) -j $j exit code" "$R" -eq 129
  grep -q "Type error" "$d/g$j.out" \
    || { cat "$d/g$j.out" >&2; fail "(g) -j $j did not report a type error"; }
done

# (h) -admit and -norec mixes, and a library read only as a dependency.
for mix in "-norec Use" "-admit Dep -norec Use" "-norec Use -norec Dep" \
           "-admit Dep -norec Use -norec Big -norec NoOp"; do
  tag=$(echo "$mix" | tr -cd 'A-Za-z')
  for j in 1 4; do
    # shellcheck disable=SC2086
    run "h$tag$j" -j $j "${LIB[@]}" $mix
    expect "(h) $mix -j $j exit code" "$R" -eq 0
  done
  same "h${tag}1" "h${tag}4" "(h) $mix"
done

# (l) Only the length in the table of segments is wrong: the payload, its
# position and both stored digests are intact. Stock's reader never reads
# that length -- it seeks to the segment and parses one value -- so it
# accepts these files, and so must this one, at every -j, however the
# library is read. ROCQCHK_STOCK names a stock coqchk to compare exit codes
# and -o output with; without one, the comparison is with this build's
# output on the intact file, which stock accepts.
STOCK=${ROCQCHK_STOCK:-}
lrun() {
  local bin=$1 name=$2; shift 2
  R=0
  "$bin" -silent -o "$@" > "$d/$name.out" 2>&1 || R=$?
}
for sel in checked dep admitted; do
  case $sel in
    checked) lib=NoOp; args=(-norec NoOp) ;;
    dep) lib=Dep; args=(-norec Use) ;;
    admitted) lib=Dep; args=(-admit Dep -norec Use) ;;
  esac
  for mut in pasteof zero negative; do
    t=$d/l-$sel-$mut
    rm -rf "$t"; cp -a "$d/good" "$t"
    lrun coqchk "l-$sel-$mut-intact" -j 1 -R "$t" "" "${args[@]}"
    expect "(l) $sel $mut: the intact file's exit code" "$R" -eq 0
    size=$(stat -c %s "$t/$lib.vo")
    case $mut in
      pasteof) n=$(( size + 128 )) ;;
      zero) n=0 ;;
      negative) n=-17 ;;
    esac
    vo length "$t/$lib.vo" opaques "$n"
    for j in 1 2 4 16; do
      name=l-$sel-$mut-j$j
      lrun coqchk "$name" -j $j -R "$t" "" "${args[@]}"
      if [ -n "$STOCK" ]; then
        rc=$R
        lrun "$STOCK" "$name-stock" -j $j -R "$t" "" "${args[@]}"
        expect "(l) $sel, length $n, -j $j: exit code (stock's is $R)" "$rc" -eq "$R"
        same "$name-stock" "$name" "(l) $sel, length $n, -j $j, against stock"
      else
        expect "(l) $sel, length $n, -j $j: exit code" "$R" -eq 0
        same "l-$sel-$mut-intact" "$name" "(l) $sel, length $n, -j $j"
      fi
    done
  done
done

# (m) and (n) tell the two ways stock reads a table apart: NoOp checked
# (-norec NoOp) is validated; NoOp read only as UseNoOp's dependency
# (-norec UseNoOp) is demarshalled without validation, and nothing reads
# its table but its table task. (m) The opaques segment is a valid
# marshalled value of the wrong type (the library segment's data): stock
# rejects it validated, and accepts it as a dependency. (n) The digest
# stored after the segment differs from the table's hash: stock rejects it
# validated, where it compares them, and accepts it as a dependency. With
# ROCQCHK_STOCK, every exit code and -o output is compared with stock's.
for mut in m n; do
  t=$d/$mut; rm -rf "$t"; cp -a "$d/good" "$t"
  case $mut in
    m) vo wrongtype "$t/NoOp.vo" opaques library ;;
    n) vo digest "$t/NoOp.vo" opaques ;;
  esac
  for sel in checked dep; do
    case $sel in
      checked) args=(-norec NoOp) ;;
      dep) args=(-norec UseNoOp) ;;
    esac
    for j in 1 2 4 16; do
      name=$mut-$sel-j$j
      lrun coqchk "$name" -j $j -R "$t" "" "${args[@]}"
      rc=$R
      case $sel in
        checked) expect "($mut) $sel -j $j: exit code" "$rc" -ne 0 ;;
        dep) expect "($mut) $sel -j $j: exit code" "$rc" -eq 0 ;;
      esac
      if [ -n "$STOCK" ]; then
        lrun "$STOCK" "$name-stock" -j $j -R "$t" "" "${args[@]}"
        expect "($mut) $sel -j $j: exit code (stock's is $R)" "$rc" -eq "$R"
        [ "$sel" = checked ] || same "$name-stock" "$name" "($mut) $sel -j $j, against stock"
      fi
    done
  done
done

# The window of (i), (j) and (k): a process stops at [point] of the read of
# [lib]'s table until $d/w/go is there. "start" runs coqchk behind it,
# "open" waits for [n] processes to be stopped, and "go" lets them all go;
# the exit code lands in $w/rc.
w=$d/w
window_start() {
  local name=$1 at=$2; shift 2
  rm -rf "$w"; mkdir -p "$w"
  ( rc=0
    ROCQCHK_OPAQUE_AT=$at coqchk -o "$@" > "$d/$name.raw" 2>&1 || rc=$?
    echo "$rc" > "$w/rc" ) &
  window_pid=$!
}
window_open() {
  local n=$1 name=$2 deadline
  deadline=$(( $(date +%s) + 60 ))
  while [ "$(find "$w" -name '*-*' | wc -l)" -lt "$n" ]; do
    [ "$(date +%s)" -lt "$deadline" ] \
      || { cat "$d/$name.raw" >&2; fail "($name) no process stopped at the window"; }
    sleep 0.05
  done
}
window_go() { touch "$w/go"; wait "$window_pid" || true; }

# out_of NAME: the output of a window run, pids replaced.
out_of() { sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/$1.raw" > "$d/$1.out"; }

# (i) Two workers read one segment at the same time. Big has enough proofs
# for its jobs to fill several batches, so several workers read its table.
window_start i "before:Big:$w" -j 4 -worker-budget 60 "${LIB[@]}" -norec Big
window_open 2 i
window_go
expect "(i) exit code" "$(cat "$w/rc")" -eq 0
run i1 -j 1 "${LIB[@]}" -norec Big
expect "(i) -j 1 exit code" "$R" -eq 0
out_of i
same i1 i "(i) two workers on one segment"

# (j) The bytes of a table changed after the main process read them. They
# are the table of the other Swap: as long, well formed, and correct, so
# only the MD5 the worker computes, which differs from the one the main
# process recorded, tells them apart, and coqchk fails.
rm -rf "$d/j"; cp -a "$d/good" "$d/j"
run j0 -j 2 -worker-budget 60 -R "$d/j" "" -norec Swap
expect "(j) exit code before the change" "$R" -eq 0
window_start j "before:Swap:$w" -j 2 -worker-budget 60 -R "$d/j" "" -norec Swap
window_open 1 j
vo replace "$d/j/Swap.vo" "$d/src/swapj/Swap.vo" opaques
window_go
expect "(j) exit code" "$(cat "$w/rc")" -eq 1
grep -q "changed while it was being checked" "$d/j.raw" \
  || { cat "$d/j.raw" >&2; fail "(j) the changed table was not reported"; }
# The changed file on its own: stock reads it once, and accepts it.
run j2 -j 2 -worker-budget 60 -R "$d/j" "" -norec Swap
expect "(j) exit code of the changed file" "$R" -eq 0

# (o) Every file above, against stock (ROCQCHK_STOCK), at every -j: the
# exit code must be stock's, and the output too wherever nothing failed,
# and always at -j 1, where this build parses the table where stock
# parses it. Without ROCQCHK_STOCK the reference is this build.
REF=${STOCK:-coqchk}

# srun NAME BIN ARGS...: a -silent -o run, pids replaced, exit code in $R.
srun() {
  local name=$1 bin=$2; shift 2
  R=0
  "$bin" -silent -o "$@" > "$d/$name.raw" 2>&1 || R=$?
  sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/$name.raw" > "$d/$name.out"
}

# noworker NAME: the output of NAME without the main process's "Worker
# process" error and the lines that continue it. It names the batch that
# the failing worker held, which depends on the schedule, as it does in
# stock.
noworker() {
  awk '/^Fatal Error: Worker process/ { skip = 1; next }
       skip && /^ / { next }
       { skip = 0; print }' "$d/$1.out" > "$d/$1.nw"
}

# ocmp TAG ARGS...: this build against the reference, at every -j: the
# exit code, and the output but for the batch line.
ocmp() {
  local tag=$1 j rc; shift
  for j in 1 2 4 16; do
    srun "o-$tag-j$j" coqchk -j "$j" "$@"
    rc=$R
    srun "o-$tag-j$j-ref" "$REF" -j "$j" "$@"
    expect "(o) $tag -j $j: exit code (the reference's is $R)" "$rc" -eq "$R"
    noworker "o-$tag-j$j"; noworker "o-$tag-j$j-ref"
    diff -u "$d/o-$tag-j$j-ref.nw" "$d/o-$tag-j$j.nw" > "$d/o-$tag-j$j.diff" \
      || { cat "$d/o-$tag-j$j.diff" >&2; fail "(o) $tag -j $j: the output differs from the reference's"; }
  done
}
ocmp intact -R "$d/good" "" -norec Op -norec NoOp -norec Use
ocmp admitted -R "$d/good" "" -admit Dep -norec Use
ocmp wide -R "$d/good" "" -norec Wide
ocmp corrupt-checked -R "$d/c" "" -norec NoOp -norec Op
ocmp corrupt-dep -R "$d/d" "" -norec Use
ocmp corrupt-admitted -R "$d/e" "" -admit Dep -norec Use
ocmp truncated -R "$d/f" "" -norec Op
ocmp illtyped -R "$d/g" "" -norec Op
ocmp wrongtype-checked -R "$d/m" "" -norec NoOp
ocmp wrongtype-dep -R "$d/m" "" -norec UseNoOp
ocmp digest-checked -R "$d/n" "" -norec NoOp
ocmp digest-dep -R "$d/n" "" -norec UseNoOp
for sel in checked dep admitted; do
  case $sel in
    checked) oargs=(-norec NoOp) ;;
    dep) oargs=(-norec Use) ;;
    admitted) oargs=(-admit Dep -norec Use) ;;
  esac
  for mut in pasteof zero negative; do
    ocmp "length-$sel-$mut" -R "$d/l-$sel-$mut" "" "${oargs[@]}"
  done
done

# (p) A marshalled value that runs past its segment on the path that does
# not validate: Dep's table, read with Marshal. (f) covers the path that
# validates, and (l) and (o) the reads that run past the segment and
# succeed.
#
# (p1) The header claims 8 bytes more than its segment holds, and the
# file has them: the reader takes the digest stored after the segment for
# payload and builds a value from bytes that mean nothing. What the
# runtime then does with that value is not defined, and it is not a
# property of the checker: on this base, with the same file and the same
# reads (identical openat/lseek/read, measured under strace on
# speed-r3a-2, 2026-10-25), the release's own coqchk dies by SIGSEGV
# while this build ends 0 under the default minor heap, and this build
# dies by SIGSEGV under OCAMLRUNPARAM=s=4k and s=16M. Both outcomes are
# printed, and neither is asserted. The same undefinedness beyond -j 1 is
# the known difference of ledger L8, confined to a table nothing reads.
#
# (p2) The header claims more than the whole file holds, which is
# defined: the demarshalling runs out of file and raises, wherever it
# runs. The exit code and the output must be the reference's, at -j 1 and
# beyond it.
rm -rf "$d/p"; cp -a "$d/good" "$d/p"
vo truncate "$d/p/Dep.vo" opaques 8
srun p-j1 coqchk -j 1 -R "$d/p" "" -norec Use
p1=$R
srun p-ref "$REF" -j 1 -R "$d/p" "" -norec Use
echo "(p1) undefined value: this build exits $p1 at -j 1, the reference $R"

# The length field of the marshal header (offset 4 of the segment's data),
# set to a megabyte, which the file does not hold; every stored hash is
# rewritten, so the only thing wrong with the file is what that header
# claims.
rm -rf "$d/p2"; cp -a "$d/good" "$d/p2"
vo poke "$d/p2/Dep.vo" opaques 4 00100000
for j in 1 2 4; do
  srun "p2-j$j" coqchk -j $j -R "$d/p2" "" -norec Use
  rc=$R
  srun "p2-j$j-ref" "$REF" -j $j -R "$d/p2" "" -norec Use
  expect "(p2) -j $j: exit code (the reference's is $R)" "$rc" -eq "$R"
  expect "(p2) -j $j: the file is refused" "$rc" -ne 0
  same "p2-j$j-ref" "p2-j$j" "(p2) -j $j"
done

# (q) The segment starts in the last bytes of the file, so a reader finds
# fewer there than one marshal header. Stock's demarshalling tells an
# absent header ("premature end of file") from one cut short
# ("input_value: truncated object"), and so must this build, which runs
# the same demarshalling on the same bytes.
for k in 0 1 7 19; do
  for sel in checked dep; do
    case $sel in
      checked) qlib=NoOp; qargs=(-norec NoOp); qtext="Corrupted file" ;;
      dep) qlib=Dep; qargs=(-norec Use)
        if [ "$k" -eq 0 ]; then qtext="premature end of file"
        else qtext="input_value: truncated object"; fi ;;
    esac
    t=$d/q-$sel-$k; rm -rf "$t"; cp -a "$d/good" "$t"
    vo position "$t/$qlib.vo" opaques "$(( $(stat -c %s "$t/$qlib.vo") - k ))"
    for j in 1 2 4 16; do
      srun "q-$sel-$k-j$j" coqchk -j "$j" -R "$t" "" "${qargs[@]}"
      rc=$R
      srun "q-$sel-$k-j$j-ref" "$REF" -j "$j" -R "$t" "" "${qargs[@]}"
      expect "(q) $sel, $k bytes left, -j $j: exit code (the reference's is $R)" \
        "$rc" -eq "$R"
      grep -q "$qtext" "$d/q-$sel-$k-j$j.out" \
        || { cat "$d/q-$sel-$k-j$j.out" >&2
             fail "(q) $sel, $k bytes left, -j $j: not \"$qtext\""; }
      same "q-$sel-$k-j$j-ref" "q-$sel-$k-j$j" "(q) $sel, $k bytes left, -j $j"
    done
  done
done

# (r) The segment does not start in the file at all. A read cannot seek
# there, so stock reads whatever its channel holds and refuses the file.
# This build hashes nothing of such a segment and parses it where stock
# parses it, when the library is interned, at every -j; in particular it
# does not report a file that never changed as one that changed.
for sel in checked dep; do
  case $sel in
    checked) rlib=NoOp; rargs=(-norec NoOp) ;;
    dep) rlib=Dep; rargs=(-norec Use) ;;
  esac
  t=$d/r-$sel; rm -rf "$t"; cp -a "$d/good" "$t"
  vo position "$t/$rlib.vo" opaques -1
  for j in 1 2 4 16; do
    srun "r-$sel-j$j" coqchk -j "$j" -R "$t" "" "${rargs[@]}"
    rc=$R
    srun "r-$sel-j$j-ref" "$REF" -j "$j" -R "$t" "" "${rargs[@]}"
    expect "(r) $sel, -j $j: exit code (the reference's is $R)" "$rc" -eq "$R"
    expect "(r) $sel, -j $j: the file is refused" "$rc" -ne 0
    same "r-$sel-j$j-ref" "r-$sel-j$j" "(r) $sel, -j $j"
    if grep -q "changed while it was being checked" "$d/r-$sel-j$j.out"; then
      cat "$d/r-$sel-j$j.out" >&2
      fail "(r) $sel, -j $j: a file that never changed was reported as changed"
    fi
  done
done

# (s) Two libraries, each damaged in its own way: Op carries a proof of
# the wrong type, and NoOp, which no check of Op reaches, carries a table
# that cannot be parsed. The walk reaches Op first (the libraries are
# checked in the order the interning left them, which is the reverse of
# the command line here). Stock interns both before it checks anything,
# so it refuses the file it cannot read, exit code 1, and never reaches
# the proof. At -j 1 this build does the same, because it too parses
# every table when it interns the library. With workers the proof can be
# checked, and fail, before the worker that reads the tables reaches that
# table; the main
# process then reads the tables in stock's order, and reports the table,
# with stock's words and exit code, and not the worker's error.
rm -rf "$d/s"; cp -a "$d/g" "$d/s"
vo corrupt "$d/s/NoOp.vo" opaques
for j in 1 2 4 16; do
  srun "s-j$j" coqchk -j "$j" -R "$d/s" "" -norec NoOp -norec Op
  rc=$R
  srun "s-j$j-ref" "$REF" -j "$j" -R "$d/s" "" -norec NoOp -norec Op
  expect "(s) -j $j: exit code (the reference's is $R)" "$rc" -eq "$R"
  expect "(s) -j $j: the file is refused" "$rc" -ne 0
  same "s-j$j-ref" "s-j$j" "(s) -j $j"
  grep -q "Corrupted file" "$d/s-j$j.out" \
    || { cat "$d/s-j$j.out" >&2
         fail "(s) -j $j: the unreadable table was not what refused the run"; }
done

# (t) A marshal header that claims more data than an [int] holds. Stock
# hands the number to its runtime, which fails to allocate; this build
# hands the same bytes to the same read instead of allocating from the
# number itself, and reports what it raises where stock does.
for sel in checked dep; do
  case $sel in
    checked) tlib=NoOp; targs=(-norec NoOp) ;;
    dep) tlib=Dep; targs=(-norec Use) ;;
  esac
  t=$d/t-$sel; rm -rf "$t"; cp -a "$d/good" "$t"
  vo hugehdr "$t/$tlib.vo" opaques
  for j in 1 2 16; do
    srun "t-$sel-j$j" coqchk -j "$j" -R "$t" "" "${targs[@]}"
    rc=$R
    srun "t-$sel-j$j-ref" "$REF" -j "$j" -R "$t" "" "${targs[@]}"
    expect "(t) $sel -j $j: exit code (the reference's is $R)" "$rc" -eq "$R"
    expect "(t) $sel -j $j: the file is refused" "$rc" -ne 0
    same "t-$sel-j$j-ref" "t-$sel-j$j" "(t) $sel -j $j"
  done
done

# (u) Eight damaged bytes in the marshalled table of a dependency that is
# not validated (the second review's D1). The file is well framed and
# every stored hash matches. Stock demarshals the table from the channel
# and never accepts it: it reports "input_value: ill-formed message" or
# another marshal error, or dies, from one run to the next. So must this
# build, which demarshals it the same way: a reader that rebuilt the value
# from a string instead accepted this file every time.
for sel in dep admitted; do
  case $sel in
    dep) uargs=(-norec Use) ;;
    admitted) uargs=(-admit Dep -norec Use) ;;
  esac
  t=$d/u-$sel; rm -rf "$t"; cp -a "$d/good" "$t"
  vo poke "$t/Dep.vo" opaques 24 deadbeefdeadbeef
  for j in 1 2 4 16; do
    srun "u-$sel-j$j" coqchk -j "$j" -R "$t" "" "${uargs[@]}"
    expect "(u) $sel -j $j: the file is refused" "$R" -ne 0
  done
  srun "u-$sel-ref" "$REF" -j 1 -R "$t" "" "${uargs[@]}"
  expect "(u) $sel: the reference refuses it too" "$R" -ne 0
done

# (v) A table whose declared length covers a 2 GiB tail of zeros (sparse),
# its payload and digests intact, read under an address-space limit (the
# second review's D5). Stock never reads the tail and accepts the file; a
# reader that held the declared range in memory ran out of it. The main
# process and the worker only hash that range, in a fixed buffer, so the
# output and the exit code must be stock's at every -j.
# The limit is what this build needs for the intact files at that -j, in
# whole GiB, plus 1 GiB: a reader that held the 2 GiB range would need
# more than that. It is measured, not fixed, because the runtime decides
# how much address space a process reserves: OCaml 5 reserves more for a
# worker than OCaml 4.14 does, and a fixed 4 GiB failed there at -j 2.
# `vo length` runs before `vo pad`. `length` rewrites the whole file, so it
# must run while the file is still small, and it needs no valid segment
# hashes; `pad` only extends the file, so the 2 GiB tail stays sparse. In
# the other order `length` holds the padded file twice in memory (4 GiB)
# and writes it out dense (2.1 GiB on disk).
GiB=1048576  # in KiB, the unit of ulimit -v
fits() {  # fits KIB J: this build checks the intact files at -j J under KIB
  ( ulimit -v "$1"; exec coqchk -silent -o -j "$2" -R "$d/good" "" -norec Use ) \
    > /dev/null 2>&1
}
t=$d/v; rm -rf "$t"; cp -a "$d/good" "$t"
vo length "$t/Dep.vo" opaques 2147483648
vo pad "$t/Dep.vo" 2147483648
for j in 1 2 4 16; do
  k=1
  while ! fits $((k * GiB)) "$j"; do
    k=$((k + 1))
    [ "$k" -le 64 ] || fail "(v) -j $j: the intact files need more than 64 GiB of address space"
  done
  lim=$(((k + 1) * GiB))
  R=0
  ( ulimit -v "$lim"; exec coqchk -silent -o -j "$j" -R "$t" "" -norec Use ) \
    > "$d/v-j$j.out" 2>&1 || R=$?
  rc=$R
  R=0
  ( ulimit -v "$lim"; exec "$REF" -silent -o -j "$j" -R "$t" "" -norec Use ) \
    > "$d/v-j$j-ref.out" 2>&1 || R=$?
  expect "(v) -j $j, limit $((k + 1)) GiB: exit code (the reference's is $R)" "$rc" -eq "$R"
  expect "(v) -j $j, limit $((k + 1)) GiB: exit code" "$rc" -eq 0
  same "v-j$j-ref" "v-j$j" "(v) -j $j"
done
rm -rf "$t"

# (w) A damaged table together with something else that is wrong (the
# third review's D2 to D4, and two cases it added). Stock parses every
# table when it interns the library, after the library's other segments
# and before the checks of its OCaml version and its name, and it interns
# every library before it checks any. So the first table it cannot read,
# in the order it interns them, is its error, unless what else is wrong
# comes earlier in that order. This build reads the tables later when it
# has workers, and must still report stock's error: ocmp compares the
# exit code and the output at every -j. Each case must also be the one
# meant: the reference reports the damaged table.
#   name: NoOp.vo, its table damaged, found as Z.vo, so that it is also
#     not the library it is named for;
#   missing: Use.vo, its table damaged, without its dependency Dep;
#   ocaml: NoOp.vo, its table damaged, and its summary naming another
#     OCaml (ocaml-only, the version alone, shows what that mutation does);
#   chain: UseOp.vo, its table damaged, checked with Op, whose proof of l1
#     is ill-typed; chain2: Op's table damaged too, Op read as UseOp's
#     dependency;
#   roots1, roots2: the files of (s), the two roots in both orders.
wref() {
  grep -q "$2" "$d/o-$1-j1-ref.out" \
    || { cat "$d/o-$1-j1-ref.out" >&2; fail "(w) $1: the reference did not report \"$2\""; }
}
t=$d/w-name; rm -rf "$t"; mkdir "$t"; cp "$d/c/NoOp.vo" "$t/Z.vo"
ocmp w-name -R "$t" "" -norec Z
wref w-name "Corrupted file"
t=$d/w-missing; rm -rf "$t"; mkdir "$t"; cp "$d/good/Use.vo" "$t/"
vo corrupt "$t/Use.vo" opaques
ocmp w-missing -R "$t" "" -norec Use
wref w-missing "Corrupted file"
t=$d/w-ocaml-only; rm -rf "$t"; mkdir "$t"; cp "$d/good/NoOp.vo" "$t/"
vo ocaml "$t/NoOp.vo"
ocmp w-ocaml-only -R "$t" "" -norec NoOp
wref w-ocaml-only "compiled with OCaml"
t=$d/w-ocaml; rm -rf "$t"; mkdir "$t"; cp "$d/c/NoOp.vo" "$t/"
vo ocaml "$t/NoOp.vo"
ocmp w-ocaml -R "$t" "" -norec NoOp
wref w-ocaml "Corrupted file"
t=$d/w-chain; rm -rf "$t"; cp -a "$d/g" "$t"
vo corrupt "$t/UseOp.vo" opaques
ocmp w-chain -R "$t" "" -norec UseOp -norec Op
wref w-chain "Corrupted file"
vo corrupt "$t/Op.vo" opaques
ocmp w-chain2 -R "$t" "" -norec UseOp
wref w-chain2 "UseOp.vo"
ocmp w-roots1 -R "$d/s" "" -norec Op -norec NoOp
wref w-roots1 "Corrupted file"
ocmp w-roots2 -R "$d/s" "" -norec NoOp -norec Op
wref w-roots2 "Corrupted file"

exit 0
