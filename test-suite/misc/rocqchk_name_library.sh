#!/usr/bin/env bash

# rocqchk refuses a library whose compiled name is not the name of its file.
# The name the kernel imports a library under is the one in its library
# segment, which the summary's name does not have to match: here zqxlib is
# renamed to zqx, a line break, then ib, in the library segment of zqxlib.vo
# only. The library is admitted, so it is read without validation. Printed
# raw, the name would start a line of its own in the -o context summary, which
# lists the axiom of the library under it. The load must refuse the library.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" zqxlib
ocaml "$R" "$d/base/zqxlib.vo" library zqxlib $'zqx\nib'

msg='contains compiled library "BadNames.zqx\nib" and not library BadNames.zqxlib.'
both_vm c-admit refuse "$msg" ib -o -Q "$d/base" BadNames -admit BadNames.zqxlib
exit $status
