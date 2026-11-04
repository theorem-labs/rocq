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

# The same report with -j 4, where the report runs forked read-ahead
# processes. The forged canonical half sits in the proof of the sealed field
# O.n, which the report reads through the implementation, and the read-ahead
# only computes constants the environment holds with their body: so no forked
# process ever reads it, and the walk checks the name exactly as with -j 1.
# Both runs must answer alike, and the forged name must stop both alike.
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
exit $status
