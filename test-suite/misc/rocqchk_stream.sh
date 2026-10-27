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
# ROCQCHK_WORKER_WINDOW=0 deals a library's checks as soon as it is checked,
# so that workers start while the next libraries are being read, however
# fast this machine reads them (misc/rocqchk_reorder.sh sees one start).
set -eu
export PATH="$BIN:$PATH"
export ROCQCHK_WORKER_WINDOW=0

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
python3 misc/vo_segments.py splice-opaques "$d/good/Bad.vo" "$d/bad/Bad.vo" "$d/src/Bad.vo"
printf 'Bad!' | dd of="$d/src/Magic.vo" bs=1 count=4 conv=notrunc status=none

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

# Cost hints change only the order in which the workers check the proofs:
# the same libraries are accepted with the same output, and the same proof
# is refused. The file also has a line that is not a pair, which is skipped.
printf 'Bad 100\nB 50\nnot a pair here\nA 1\n' > "$d/hints"
r1=0; r2=0
rocqchk -j 4 -R "$d/src" "" -norec A -norec B -norec C > "$d/plain.out" 2> "$d/plain.err" || r1=$?
rocqchk -j 4 -cost-hints "$d/hints" -R "$d/src" "" -norec A -norec B -norec C \
  > "$d/hints.out" 2> "$d/hints.err" || r2=$?
if [ "$r1" = 0 ] && [ "$r2" = 0 ] && cmp -s "$d/plain.out" "$d/hints.out" && cmp -s "$d/plain.err" "$d/hints.err"
then echo "correct libraries, cost hints: same (exit code 0)"
else echo "correct libraries, cost hints: differs (exit codes $r1 and $r2)"; fail=1
fi
compare "ill-typed proof, cost hints" error -cost-hints "$d/hints" \
  -R "$d/src" "" -norec A -norec B -norec Bad
grep -q 'while checking the opaque proof of Bad.l1\.' "$d/stream.log" ||
  { echo "expected the proof of Bad.l1 to be reported with cost hints"; fail=1; }
# Hints that cannot be used are ignored with a warning, and the libraries
# are still checked and accepted: a directory, a device that reports no
# size and never ends, and a file over the 16 MiB bound.
head -c $((17 * 1024 * 1024)) /dev/zero | tr '\0' 'x' > "$d/big.hints"
for src in "$d" /dev/zero "$d/big.hints"; do
  r3=0
  rocqchk -j 4 -cost-hints "$src" -R "$d/src" "" -norec A -norec B -norec C \
    > "$d/dir.out" 2> "$d/dir.err" || r3=$?
  if [ "$r3" = 0 ] && grep -q 'Ignoring the cost hints' "$d/dir.err" && cmp -s "$d/plain.out" "$d/dir.out"
  then echo "unusable cost hints ($src): ignored (exit code 0)"
  else echo "unusable cost hints ($src): not ignored (exit code $r3)"; fail=1
  fi
done
rm -f "$d/big.hints"

exit $fail
