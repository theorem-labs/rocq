#!/usr/bin/env bash

# rocqchk -statement-report and a name that holds a line break only in the
# CANONICAL half of a term's reference to an object only an implementation
# holds, which the report prints after a "?". The opaque proof of Canon.O.n
# names O.D.ax, which the seal hides, by a term whose canonical half is
# O.zqxaXzqxforged.ax. The kernel would refuse the reference once that
# half is changed (Typeops.check_constant), but an admitted library is read
# without validation, and the check at load reads declared names, not the
# names a term holds.
#
# First, on the library as compiled, the report must print that canonical
# half after the "?": that is the text the probe changes, so a pass cannot
# come from another path. Then, with zqxaXzqxforged renamed to zqxa, a line
# break, then zqxforged, in the opaques segment of Canon.vo only, the report
# must stop before the statement's line, with no END line, and keep the exit
# status 0: the name it checks is the name it prints. The stop must quote the
# canonical half, the text that failed, not the valid user half; the warning
# that carries the error escapes it once more, so its quotes and line break
# read \" and \\n.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" Canon
printf 'model BadNames.Canon.model\n' > "$d/req"

# The same report with -j 4, where forked read-ahead processes compute the
# nodes of opaque constants the environment holds with their body. Here the
# forged canonical half sits in the proof of the sealed field O.n, which the
# report reads through the implementation, so the walk computes that node
# itself. Either way the "?" token and the name check are formed only in the
# walk (canonical_token, unprintable_name), never in a forked process, so both
# runs must answer alike, and the forged name must stop both alike.
for jobs in 1 4; do
  rc=0
  "$BIN"rocqchk -silent -j "$jobs" -statement-report "$d/req" -Q "$d/base" BadNames \
    -admit BadNames.Canon > "$d/honest-j$jobs.log" 2>&1 || rc=$?
  echo "--- honest, -j $jobs: exit $rc ---"
  cat -v "$d/honest-j$jobs.log"
  if [ "$rc" -eq 0 ] \
       && matches -x -F 'axiom model BadNames.Canon.O.D.ax ?BadNames.Canon:O.zqxaXzqxforged.ax' "$d/honest-j$jobs.log" \
       && matches '^END STATEMENT REPORT$' "$d/honest-j$jobs.log"; then
    echo "RESULT honest-j$jobs: PASS"
  else
    echo "RESULT honest-j$jobs: FAIL (the report does not print the canonical half the probe changes)"
    status=1
  fi
done
if ! cmp -s "$d/honest-j1.log" "$d/honest-j4.log"; then
  echo "RESULT honest-same: FAIL (-j 4 and -j 1 differ)"
  diff "$d/honest-j1.log" "$d/honest-j4.log"
  status=1
fi

ocaml "$R" "$d/base/Canon.vo" opaques aXzqxforged $'a\nzqxforged'
both_vm c-canonical stop 'would print the name \"BadNames.Canon:O.zqxa\\nzqxforged.ax\", which' zqxforged \
  -statement-report "$d/req" -Q "$d/base" BadNames -admit BadNames.Canon
both_vm c-canonical-j4 stop 'would print the name \"BadNames.Canon:O.zqxa\\nzqxforged.ax\", which' zqxforged \
  -j 4 -statement-report "$d/req" -Q "$d/base" BadNames -admit BadNames.Canon

# A "?" canonical that a forked read-ahead process does compute: [model] in
# plain/Fwd.v is a top-level Qed, so the environment holds it with its body,
# and with Dzqxu renamed to Dzqxv in its proof the reference names an object
# nothing declares, printed as "?" and the term's canonical half. The honest
# report must be the same at -j 1 and -j 4, and at -j 4 the walk must have
# taken that node from a process; then, with the canonical half forged to hold
# a line break, the report must stop alike at both.
compile_plain "$d/fwd" Fwd
printf 'model BadNames.Fwd.model\n' > "$d/fwdreq"
ocaml "$R" "$d/fwd/Fwd.vo" opaques Dzqxu Dzqxv
for jobs in 1 4; do
  rc=0
  "$BIN"rocqchk -silent -j "$jobs" -statement-report "$d/fwdreq" -Q "$d/fwd" BadNames \
    -admit BadNames.Fwd > "$d/fwd-j$jobs.log" 2>&1 || rc=$?
  echo "--- forward, -j $jobs: exit $rc ---"
  cat -v "$d/fwd-j$jobs.log"
  if [ "$rc" -eq 0 ] \
       && matches -x -F 'axiom model BadNames.Fwd.Dzqxv.ax ?BadNames.Fwd:zqxaXzqxforged.ax' "$d/fwd-j$jobs.log" \
       && matches '^END STATEMENT REPORT$' "$d/fwd-j$jobs.log"; then
    echo "RESULT forward-j$jobs: PASS"
  else
    echo "RESULT forward-j$jobs: FAIL (the report does not print the forward reference's canonical half)"
    status=1
  fi
done
if ! cmp -s "$d/fwd-j1.log" "$d/fwd-j4.log"; then
  echo "RESULT forward-same: FAIL (-j 4 and -j 1 differ)"
  diff "$d/fwd-j1.log" "$d/fwd-j4.log"
  status=1
fi
# With the test seam the walk waits for the processes and says how many nodes
# it took from them: the node of [model] must be one, or the -j 4 run proves
# nothing about a process.
COQ_TEST_SUITE_STATEMENT_REPORT_READ_AHEAD=1 "$BIN"rocqchk -silent -j 4 -statement-report "$d/fwdreq" \
  -Q "$d/fwd" BadNames -admit BadNames.Fwd > "$d/fwd-ahead.log" 2>&1 || true
if matches '^read ahead [1-9][0-9]*$' "$d/fwd-ahead.log"; then
  echo "RESULT forward-read-ahead: PASS ($(grep '^read ahead' "$d/fwd-ahead.log"))"
else
  echo "RESULT forward-read-ahead: FAIL (the -j 4 run took no node from a process)"
  cat -v "$d/fwd-ahead.log"
  status=1
fi
ocaml "$R" "$d/fwd/Fwd.vo" opaques aXzqxforged $'a\nzqxforged'
both_vm f-canonical stop 'would print the name \"BadNames.Fwd:zqxa\\nzqxforged.ax\", which' zqxforged \
  -statement-report "$d/fwdreq" -Q "$d/fwd" BadNames -admit BadNames.Fwd
both_vm f-canonical-j4 stop 'would print the name \"BadNames.Fwd:zqxa\\nzqxforged.ax\", which' zqxforged \
  -j 4 -statement-report "$d/fwdreq" -Q "$d/fwd" BadNames -admit BadNames.Fwd
exit $status
