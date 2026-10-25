#!/usr/bin/env bash
# rocqchk -j N checks opaque proofs in forked workers, in batches. A worker
# that holds a batch with a long proof in it used to keep the rest of that
# batch to itself, even while other workers had nothing to do. The main
# process now asks such a worker, with SIGUSR1, to give back the checks it
# has not started, and deals them at once (CheckWorkers.request_release).
#
# Every check must still run exactly once, and the output and the verdict
# must not depend on the schedule. The library below has 140 opaque proofs:
# l1 to l20, two of them long, l1 and l2, the first two the walk defers,
# then 120 short ones, p1 to p120. A batch is a stripe of whole pieces of
# libraries, and a library's piece keeps its jobs in order, so the batch
# that holds l1 holds l2 after it (a model of the dealing gives this for
# any number of dependencies from 8 to 30 at -j 4): l2 runs in parallel
# with l1 only if the worker gives it back while it checks l1.
#  (a) -j 4: the worker that holds l1 gives back what is left of its batch
#      once it has started l1; the batch headed by l2 is dealt before that
#      worker has finished; no worker stops early, and each is asked at
#      most once. How much faster -j 4 is depends on the machine, so the
#      speed lane measures that on a box it controls, not this test;
#  (b) -j 1, 2, 4 and 16: the same output and exit code, and every check
#      run once;
#  (c) each race window, opened on purpose by ROCQCHK_WORKER_RELEASE_AT (a
#      worker sends itself the request at that point): between the fork and
#      the worker's loop, before its first check, between the start of a
#      check and the release test, while a check runs, between two checks,
#      and after the loop: what the worker keeps, every check run once, and
#      the output of -j 1;
#  (d) a batch of one check is never asked to release;
#  (e) an ill-typed proof, l13, in a released tail: coqchk fails with the
#      error text of -j 1, and names Lib.l13;
#  (f) requests that reach the main process, which sends them and never
#      acts on one: from outside, twice, while it runs; and (with
#      ROCQCHK_WORKER_RELEASE_AT=main) to itself just after its first fork,
#      after which no worker may release without being asked. The run is
#      not disturbed.
# The output compared in (b), (c), (e) and (f) is the one a user sees:
# coqchk with -o and without -silent and -d, standard output and error
# together, pids replaced. The counts come from separate runs with
# -d checker-workers.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_WORKER_RELEASE_AT

d=$(mktemp -d)
mkdir "$d/good" "$d/bad" "$d/spliced"

# A proof the VM must run: burn p acc makes about p calls and gives acc
# back, so the time is chosen by the bit length of p and nothing grows.
python3 - "$d" <<'PY'
import sys
d = sys.argv[1]

def pos(n):
    t = "xH"
    for c in bin(n)[3:]:
        t = "(%s %s)" % ("xI" if c == "1" else "xO", t)
    return t

HEADER = """Require Import Corelib.BinNums.PosDef.
Fixpoint burn (p : positive) (acc : positive) : positive :=
  match p with
  | xH => acc
  | xO q => burn q (burn q acc)
  | xI q => burn q (burn q acc)
  end.
"""

LONG = 1 << 23   # about 8 million calls
SHORT = 1 << 13

def gen(bad):
    out = [HEADER]
    for i in range(1, 21):
        p = LONG if i in (1, 2) else SHORT
        if bad and i == 13:
            # Ill-typed once the opaque table of this file is spliced into
            # the good one: there the proof of l13 has type U -> U.
            out.append("Lemma l%d : forall x : positive, positive.\n"
                       "Proof. exact (fun x => x). Qed.\n" % i)
        else:
            out.append("Lemma l%d : burn %s xH = xH.\n"
                       "Proof. vm_cast_no_check (@eq_refl positive xH). Qed.\n" % (i, pos(p)))
        out.append("Definition d%d := l%d.\n" % (i, i))
    # Short proofs after them, in the same library: they keep the batches
    # that finish deals long enough that the piece of this library that
    # holds l1 also holds l2.
    for i in range(1, 121):
        out.append("Lemma p%d : True. Proof. exact I. Qed.\n" % i)
    return "".join(out)

open(d + "/good/Lib.v", "w").write(gen(False))
# The bad file must have the same opaque table layout as the good one, so
# only the statement and the proof of l13 differ.
open(d + "/bad/Lib.v", "w").write(gen(True))
PY

rocq c -native-compiler no -R "$d/good" "" "$d/good/Lib.v"
rocq c -native-compiler no -R "$d/bad" "" "$d/bad/Lib.v"

# The ill-typed library: the library segment of the good .vo (where l13 has
# type [burn … = xH]) with the opaques segment of the bad one (where its
# proof is [fun x => x]). Only the kernel check of that proof tells them
# apart. Same splice as misc/rocqchk_parallel.sh.
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
vg, sg = parse(d + "/good/Lib.vo")
vb, sb = parse(d + "/bad/Lib.vo")
assert vg == vb, "vo_version mismatch"
assert sg["opaques"] != sb["opaques"], "opaques should differ"
spliced = dict(sg)
spliced["opaques"] = sb["opaques"]
write(d + "/spliced/Lib.vo", vg, spliced)
PY

# The scheduling events of a -d checker-workers stream, in order. Its
# messages can be wrapped, so whitespace is collapsed first.
cat > "$d/sched.py" <<'PY'
import re, sys

def events(path):
    text = re.sub(r"\s+", " ", open(path, errors="replace").read())
    pats = [
        ("fork", r"worker (\d+): a batch of (\d+) \(the first is (.+?), the last (.+?)\)"),
        ("ask", r"asking worker (\d+) to release what is left of its (\d+) checks"),
        ("release", r"worker (\d+) releases (\d+) of (\d+) after (\d+), queued again"),
        ("kept", r"worker (\d+) completed the (\d+) checks it kept"),
        ("done", r"done: (\d+) workers forked, (\d+) stopped early, (\d+) released a tail, "
                 r"(\d+) checks run of (\d+) deferred"),
    ]
    found = []
    for kind, pat in pats:
        for m in re.finditer(pat, text):
            found.append((m.start(), kind, m.groups()))
    found.sort()
    return [(k, g) for _, k, g in found]

def fail(msg, ev):
    for k, g in ev:
        print("  %s %s" % (k, " ".join(g)), file=sys.stderr)
    sys.exit("FAILURE: " + msg)

cmd, path = sys.argv[1], sys.argv[2]
ev = events(path)

if cmd == "done":
    # FIELD: forked, stopped, released, run, deferred
    names = ["forked", "stopped", "released", "run", "deferred"]
    d = [g for k, g in ev if k == "done"]
    print(d[-1][names.index(sys.argv[3])] if d else "")

elif cmd == "a":
    # The batch dealt with l2 at its head is the tail that a worker gave
    # back: that worker released at least one check, after it had started
    # at least two jobs (the jobs before l1, then l1), and the batch headed
    # by l2 is forked after the release and before that worker's final
    # report is read, so while it still checks l1.
    l2 = [i for i, (k, g) in enumerate(ev) if k == "fork" and g[2] == "Lib.l2"]
    if len(l2) != 1:
        fail("expected one batch headed by Lib.l2", ev)
    l2 = l2[0]
    rel = [(i, g[0]) for i, (k, g) in enumerate(ev[:l2])
           if k == "release" and int(g[1]) >= 1 and int(g[3]) >= 2]
    if not rel:
        fail("no worker gave back checks after it had started two jobs, "
             "before the batch headed by Lib.l2", ev)
    i, w = rel[-1]
    kept = [j for j, (k, g) in enumerate(ev) if k == "kept" and g[0] == w]
    if kept and not l2 < kept[0]:
        fail("the batch headed by Lib.l2 was not dealt while the worker that "
             "gave it back still ran", ev)

elif cmd == "asks":
    # Each worker is asked at most once, and never for a batch of one.
    size = {g[0]: int(g[1]) for k, g in ev if k == "fork"}
    asked = [g[0] for k, g in ev if k == "ask"]
    if len(asked) != len(set(asked)):
        fail("a worker was asked twice", ev)
    if any(size.get(p, 0) < 2 for p in asked):
        fail("a batch of one check was asked to release", ev)

elif cmd == "unasked":
    # No worker releases without having been asked.
    asked = set()
    for k, g in ev:
        if k == "ask":
            asked.add(g[0])
        if k == "release" and g[0] not in asked:
            fail("worker %s released without being asked" % g[0], ev)

elif cmd == "window":
    # What the worker keeps in each race window.
    kind = sys.argv[3]
    rel = [tuple(int(x) for x in g) for k, g in ev if k == "release"]
    forks = [g for k, g in ev if k == "fork"]
    if kind == "first":
        # Every worker is signalled before its first check, so every one of
        # them releases, keeping 1, and some give something back.
        if len(rel) != len(forks) or any(r[3] != 1 for r in rel):
            fail("not every worker released after 1 check", ev)
        if not any(r[1] >= 1 for r in rel):
            fail("no worker gave anything back", ev)
    elif kind == "second":
        if not any(r[1] >= 1 and r[3] == 2 for r in rel):
            fail("no worker gave something back after 2 checks", ev)
    elif kind == "report":
        # The main process may also ask a worker (the largest batch, while
        # the tail is still useful); every other worker sent itself the
        # request after its loop, so it gives nothing back.
        asked = {g[0] for k, g in ev if k == "ask"}
        own = [tuple(int(x) for x in g) for k, g in ev
               if k == "release" and g[0] not in asked]
        if not own or any(r[1] != 0 or r[3] != r[2] for r in own):
            fail("a worker asked after its loop gave something back", ev)
PY

fail() { >&2 echo "FAILURE: $*"; exit 1; }

expect() {
  [ "$2" "$3" "$4" ] || fail "$1 is $2, expected $3 $4"
}

# dbg LOG ARGS...: rocqchk with the scheduling debug stream, for the counts.
# Its exit code goes to $R.
R=0
dbg() {
  local log=$1; shift
  R=0
  rocqchk -silent -d checker-workers "$@" > "$d/$log" 2>&1 || R=$?
}

# out NAME ARGS...: rocqchk as a user runs it, with -o: its standard output
# and error together, pids replaced, in $d/NAME.out. Exit code in $R.
out() {
  local name=$1; shift
  R=0
  rocqchk -o "$@" > "$d/$name.raw" 2>&1 || R=$?
  sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/$name.raw" > "$d/$name.out"
}

# same NAME WHAT: $d/NAME.out is the output of -j 1.
same() {
  diff -u "$d/o-j1.out" "$d/$1.out" > "$d/$1.diff" \
    || { cat "$d/$1.diff" >&2; fail "$2: the output differs from -j 1"; }
}

sched() { python3 "$d/sched.py" "$@"; }

GOOD=(-worker-budget 60 -R "$d/good" "" -norec Lib)

# (b) Every -j: the same output and exit code as -j 1, and, with the debug
# stream, every check run once.
for j in 1 2 4 16; do
  out "o-j$j" -j $j "${GOOD[@]}"
  expect "(b) -j $j exit code" "$R" -eq 0
  [ "$j" = 1 ] || same "o-j$j" "(b) -j $j"
  dbg "j$j.log" -j $j "${GOOD[@]}"
  expect "(b) -j $j exit code with -d" "$R" -eq 0
  if [ "$j" != 1 ]; then
    expect "(b) -j $j checks run" "$(sched done "$d/j$j.log" run)" -eq 140
    expect "(b) -j $j checks deferred" "$(sched done "$d/j$j.log" deferred)" -eq 140
  fi
done
[ -s "$d/o-j1.out" ] || fail "(b) the output of -j 1 is empty"

# (a) What is left of the batch [the table of Lib, l1, l2, ...] is given
# back while l1 runs, so l2 runs in parallel with it.
sched a "$d/j4.log"
expect "(a) releases at -j 4" "$(sched done "$d/j4.log" released)" -ge 1
expect "(a) workers stopped early at -j 4" "$(sched done "$d/j4.log" stopped)" -eq 0
sched asks "$d/j4.log"
# The wall time is not compared here. How long -j 4 takes against -j 1 is
# a property of the machine, not of the code: a shared runner with few
# cores gives about 1.25x where a quiet 32-core box gives 2.27x, so every
# fixed ratio fails somewhere (Github CI runs 40170124772, 40147210453 and
# 40204758171, each at about 80%). The speed lane measures the ratio on a
# box it controls. What proves the protocol here is that a release
# happened, that no worker stopped early, and that (b) shows every check
# run exactly once with the output and the exit code of -j 1.

# (c) The race windows, each opened on purpose, with what the worker then
# keeps:
#  - "fork" and "entry": the request lands before the first check, so every
#    worker releases, keeping 1;
#  - "started:1", "check:1" and "between:1": the worker keeps 2, whether
#    the request landed between the start of check 1 and the release test,
#    while check 1 ran, or after it;
#  - "report": the batch is over, so the worker gives nothing back.
for case in fork:first entry:first started:1:second check:1:second between:1:second \
            report:report; do
  kind=${case##*:}; w=${case%:*}
  log="w-${w%%:*}.log"
  ROCQCHK_WORKER_RELEASE_AT=$w dbg "$log" -j 4 "${GOOD[@]}"
  expect "(c) $w exit code" "$R" -eq 0
  expect "(c) $w checks run" "$(sched done "$d/$log" run)" -eq 140
  sched window "$d/$log" "$kind"
  ROCQCHK_WORKER_RELEASE_AT=$w out "o-w-${w%%:*}" -j 4 "${GOOD[@]}"
  expect "(c) $w exit code without -d" "$R" -eq 0
  same "o-w-${w%%:*}" "(c) window $w"
done

# (d) A batch of one check is never asked: at -j 16 the checks are dealt
# in batches of one once the queue is short.
sched asks "$d/j16.log"

# (f) Requests that reach the main process. The default action of SIGUSR1
# is to terminate, so the main process must have the handler, and it must
# drop what it records before it forks again.
#  - From outside, twice, once the handler is installed. The handler is
#    installed at the first fork, which nothing prints without -d, so this
#    reads the caught-signal mask of the process (SigCgt; SIGUSR1 is bit 9
#    on Linux), and falls back to waiting one second without /proc.
handler_set() {
  local m
  m=$(awk '/^SigCgt:/ { print $2 }' "/proc/$1/status" 2>/dev/null) || return 1
  [ -n "$m" ] && [ $(( 0x$m & 0x200 )) -ne 0 ]
}
stray() {
  local main; shift
  "$@" &
  main=$!
  if [ -r "/proc/$main/status" ]; then
    for _ in $(seq 1 400); do handler_set "$main" && break; sleep 0.025; done
    handler_set "$main" || fail "(f) the main process never installed the handler"
  else
    sleep 1
  fi
  kill -USR1 "$main" 2>/dev/null || fail "(f) the main process was gone"
  sleep 0.2
  kill -USR1 "$main" 2>/dev/null || true
  R=0
  wait "$main" || R=$?
}
stray stray.log sh -c 'exec rocqchk -silent -d checker-workers "$@" > "$0" 2>&1' \
  "$d/stray.log" -j 4 "${GOOD[@]}"
expect "(f) exit code after a stray request" "$R" -eq 0
expect "(f) checks run after a stray request" "$(sched done "$d/stray.log" run)" -eq 140
stray o-stray.raw sh -c 'exec rocqchk -o "$@" > "$0" 2>&1' "$d/o-stray.raw" -j 4 "${GOOD[@]}"
expect "(f) exit code after a stray request, without -d" "$R" -eq 0
sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/o-stray.raw" > "$d/o-stray.out"
same o-stray "(f) a stray request"
#  - To itself, just after its first fork: every worker forked later must
#    not inherit the request.
ROCQCHK_WORKER_RELEASE_AT=main dbg main.log -j 4 "${GOOD[@]}"
expect "(f) exit code with a request in the main process" "$R" -eq 0
expect "(f) checks run with a request in the main process" "$(sched done "$d/main.log" run)" -eq 140
sched unasked "$d/main.log"
ROCQCHK_WORKER_RELEASE_AT=main out o-main -j 4 "${GOOD[@]}"
expect "(f) exit code with a request in the main process, without -d" "$R" -eq 0
same o-main "(f) a request in the main process"

# (e) An ill-typed proof in a released tail. With the request at the entry
# of each worker, every batch is released after its first job, so l13,
# which is deep in the batch that starts at the library, is checked only
# from checks that were given back.
#
# The first error printed is the one of the proof: at -j 1 the type error;
# with workers, the same text and a line naming the proof. It must be the
# same in every schedule. A second error follows with workers, from the
# main process: "Worker process PID exited with code 129 while checking
# N opaque proofs (the first is ..., the last ...)". It names the batch
# that the failing worker held, so it depends on the schedule, as it does
# without release on request (the batches differ at each -j); it is not
# compared.
BAD=(-worker-budget 60 -R "$d/spliced" "" -norec Lib)
# The first error block of an output: from its first "Fatal Error" line to
# the next one.
errblock() {
  awk '/^Fatal Error/ { n++ } n == 1' "$d/$1.out"
}
out o-bad1 -j 1 "${BAD[@]}"
expect "(e) -j 1 exit code" "$R" -ne 0
errblock o-bad1 > "$d/err1"
grep -q "Type error" "$d/err1" || { cat "$d/o-bad1.out" >&2; fail "(e) no type error at -j 1"; }
for case in 2: 4: 16: 4:entry; do
  j=${case%%:*}; w=${case#*:}
  name="o-bad$j${w:+-$w}"
  ROCQCHK_WORKER_RELEASE_AT=$w out "$name" -j "$j" "${BAD[@]}"
  expect "(e) -j $j $w exit code" "$R" -ne 0
  errblock "$name" > "$d/$name.err"
  grep -qx " *while checking the opaque proof of Lib.l13\." "$d/$name.err" \
    || { cat "$d/$name.out" >&2; fail "(e) -j $j $w did not name Lib.l13 in its first error"; }
  grep -v "while checking the opaque proof of" "$d/$name.err" > "$d/$name.err1"
  diff -u "$d/err1" "$d/$name.err1" > "$d/$name.diff" \
    || { cat "$d/$name.diff" >&2; fail "(e) the error text of -j $j $w differs from -j 1"; }
  [ "$name" = o-bad2 ] || diff -u "$d/o-bad2.err" "$d/$name.err" > "$d/$name.diff2" \
    || { cat "$d/$name.diff2" >&2; fail "(e) the first error of -j $j $w differs from -j 2"; }
done
ROCQCHK_WORKER_RELEASE_AT=entry dbg bad4.log -j 4 "${BAD[@]}"
expect "(e) -j 4 exit code with -d" "$R" -ne 0
grep -q "releases [1-9][0-9]* of [0-9]* after 1" "$d/bad4.log" \
  || { cat "$d/bad4.log" >&2; fail "(e) no batch released a tail after its first job"; }

exit 0
