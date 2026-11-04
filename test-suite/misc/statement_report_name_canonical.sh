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

rc=0
"$BIN"rocqchk -silent -statement-report "$d/req" -Q "$d/base" BadNames -admit BadNames.Canon \
  > "$d/honest.log" 2>&1 || rc=$?
echo "--- honest: exit $rc ---"
cat -v "$d/honest.log"
if [ "$rc" -eq 0 ] \
     && matches -x -F 'axiom model BadNames.Canon.O.D.ax ?BadNames.Canon:O.zqxaXzqxforged.ax' "$d/honest.log" \
     && matches '^END STATEMENT REPORT$' "$d/honest.log"; then
  echo "RESULT honest: PASS"
else
  echo "RESULT honest: FAIL (the report does not print the canonical half the probe changes)"
  status=1
fi

ocaml "$R" "$d/base/Canon.vo" opaques aXzqxforged $'a\nzqxforged'
both_vm c-canonical stop 'would print the name \"BadNames.Canon:O.zqxa\\nzqxforged.ax\", which' zqxforged \
  -statement-report "$d/req" -Q "$d/base" BadNames -admit BadNames.Canon
exit $status
