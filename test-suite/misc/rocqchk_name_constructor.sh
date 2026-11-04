#!/usr/bin/env bash

# rocqchk refuses a constructor name (mind_consnames), not a type name, that
# holds a line break. The library is checked (-norec) and, separately,
# admitted (Dep mode). The load must refuse it.

. misc/rocqchk_names/lib.sh

build_plugin
compile_theory Cons

msg='has the constructor name "zqxbad\nzqxforged", which is not an identifier.'
both_vm e-norec refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.Cons
both_vm e-admit refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.Cons
exit $status
