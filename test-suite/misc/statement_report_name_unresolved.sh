#!/usr/bin/env bash

# rocqchk -statement-report refuses to print a name that holds a line break and
# that only a term of an admitted library holds. The type of M.model names
# A.zqxfoo, renamed to zqx, a line break, then oo, in the library segment of
# M.vo. M is admitted, so it is read without validation, and the check at load
# does not see the name: it reads declared names, not the constants a term
# names. Printed raw on an `axiom` line, the name would start a line of its
# own in the report. The report must stop before the statement's line, so it
# has no END STATEMENT REPORT line, and keep the exit status 0.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" A M
ocaml "$R" "$d/base/M.vo" library zqxfoo $'zqx\noo'
printf 'model BadNames.M.model\n' > "$d/requests"

both_vm b-unresolved stop 'would print the name' oo \
  -statement-report "$d/requests" -Q "$d/base" BadNames -admit BadNames.M
exit $status
