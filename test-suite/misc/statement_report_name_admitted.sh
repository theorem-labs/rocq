#!/usr/bin/env bash

# rocqchk -statement-report and a name that only a term of an admitted library
# holds, and that holds a line break:
#  b-opaque: in the OPAQUE body of MO.model (the opaques segment of MO.vo);
#  b-ind: an INDUCTIVE, in the type of MI.model (the library segment of MI.vo).
# The report must stop before the statement's line, with no END line, and keep
# the exit status 0.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" A2 MO AI MI
msg='would print the name'

cp -r "$d/base" "$d/mo"
ocaml "$R" "$d/mo/MO.vo" opaques fooXzqxforged $'foo\nzqxforged'
printf 'model BadNames.MO.model\n' > "$d/req-mo"
both_vm b-opaque stop "$msg" zqxforged -statement-report "$d/req-mo" -Q "$d/mo" BadNames -admit BadNames.MO

cp -r "$d/base" "$d/mi"
ocaml "$R" "$d/mi/MI.vo" library indXzqxforged $'ind\nzqxforged'
printf 'model BadNames.MI.model\n' > "$d/req-mi"
both_vm b-ind stop "$msg" zqxforged -statement-report "$d/req-mi" -Q "$d/mi" BadNames -admit BadNames.MI
exit $status
