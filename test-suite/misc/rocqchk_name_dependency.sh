#!/usr/bin/env bash

# rocqchk refuses a dependency name that holds a line break. L requires
# zqxdepXzqxforged, and Top requires L. In L.vo, depXzqxforged is renamed to
# dep, a line break, then zqxforged: in the summary segment only (md_deps),
# and, separately, in the library segment only (the compiled dependencies). L
# is loaded only in Dep mode: as a dependency of Top (-norec), and admitted
# (-admit). The load must refuse L.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" zqxdepXzqxforged L Top
msg='has the dependency "BadNames.zqxdep\nzqxforged", which is not made of identifiers.'

cp -r "$d/base" "$d/md"
ocaml "$R" "$d/md/L.vo" summary depXzqxforged $'dep\nzqxforged'
both_vm h-mddeps-norecTop refuse "$msg" zqxforged -o -Q "$d/md" BadNames -norec BadNames.Top
both_vm h-mddeps-admitL refuse "$msg" zqxforged -o -Q "$d/md" BadNames -admit BadNames.L

cp -r "$d/base" "$d/comp"
ocaml "$R" "$d/comp/L.vo" library depXzqxforged $'dep\nzqxforged'
both_vm h-compdeps-norecTop refuse "$msg" zqxforged -o -Q "$d/comp" BadNames -norec BadNames.Top
both_vm h-compdeps-admitL refuse "$msg" zqxforged -o -Q "$d/comp" BadNames -admit BadNames.L
exit $status
