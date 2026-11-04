#!/usr/bin/env bash

# rocqchk refuses a library that declares a name holding a line break. Rocq's
# own commands refuse such a name, so a test plugin declares it with
# Id.of_string_soft, standing for a crafted .vo. Printed raw, the name would
# start a line of its own in the output, before any statement report: the
# `checking cst:` progress line, which a run without -silent prints, and the
# -o context summary, which lists the axioms of every loaded library. Label is
# checked (-norec Label), and loaded only in Dep mode: as a dependency of TopL
# (-norec TopL), also admitted (-admit), and in a -statement-report run. The
# load must refuse it.

. misc/rocqchk_names/lib.sh

build_plugin
compile_theory Label
compile_theory TopL
printf 'r BadNames.Label.zqxbad\n' > "$d/requests"

msg='has the label "zqxbad\nzqxforged", which is not an identifier.'
both_vm a-norec refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.Label
both_vm i-norecTopL refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.TopL
both_vm i-admitLabel refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.Label -norec BadNames.TopL
both_vm i-report refuse "$msg" zqxforged -statement-report "$d/requests" -Q "$d/theories" BadNames -norec BadNames.TopL
exit $status
