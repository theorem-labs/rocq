#!/usr/bin/env bash

# rocqchk refuses a functor parameter whose PATH (the dirpath inside the MBId)
# holds a line break, and one whose identifier does. The checker prints a
# parameter's MBId in its progress line "checking module type:". The library
# is checked (-norec) and admitted. The load must refuse it.

. misc/rocqchk_names/lib.sh

build_plugin
compile_theory FuncPath
compile_theory FuncName

msg='has the functor parameter "BadNames.zqxbad\nzqxforged.X", which is not made of identifiers.'
both_vm f-path-norec refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.FuncPath
both_vm f-path-admit refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.FuncPath

msg='has the functor parameter "BadNames.FuncName.zqxbad\nzqxforged", which is not made of identifiers.'
both_vm f-name-norec refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.FuncName
both_vm f-name-admit refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.FuncName
exit $status
