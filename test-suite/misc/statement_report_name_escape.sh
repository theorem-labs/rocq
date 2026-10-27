#!/usr/bin/env bash

# rocqchk -statement-report escapes the text of an exception it catches
# inside the report, here one that holds a name read from a library: the type
# of T3.trusted, admitted, holds a constructor of a record that no library
# declares (recXzqxforged renamed to rec, a line break, then zqxforged, in the
# library segment of T3.vo). The report does not walk a trusted constant; the
# type match of Mo3.model against T3.trusted reaches the constructor and
# raises the anomaly "Inductive ... does not appear in the environment" inside
# the report. The run must keep exit 0, stop the report with no END line, and
# print the caught text escaped, on one line.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" A3 T3 Mo3
ocaml "$R" "$d/base/T3.vo" library recXzqxforged $'rec\nzqxforged'
printf 's BadNames.Mo3.model BadNames.T3.trusted\n' > "$d/requests"

both_vm t-escape stop 'zqxrec\nzqxforged' zqxforged -statement-report "$d/requests" -Q "$d/base" BadNames -admit BadNames.T3 -admit BadNames.Mo3
exit $status
