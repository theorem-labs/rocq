#!/usr/bin/env bash

# rocqchk refuses a library whose summary name (md_name) holds a line break,
# while the compiled library's name is the file's. The name clash message
# would print md_name. The library is admitted and, separately, checked. The
# load must refuse it.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" zqxmdXzqxforged
ocaml "$R" "$d/base/zqxmdXzqxforged.vo" summary mdXzqxforged $'md\nzqxforged'

msg='has the library name "BadNames.zqxmd\nzqxforged", which is not made of identifiers.'
both_vm m-admit refuse "$msg" zqxforged -o -Q "$d/base" BadNames -admit BadNames.zqxmdXzqxforged
both_vm m-norec refuse "$msg" zqxforged -o -Q "$d/base" BadNames -norec BadNames.zqxmdXzqxforged
exit $status
