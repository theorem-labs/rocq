#!/usr/bin/env bash

# rocqchk refuses a library with an inductive type whose name holds a line
# break, when that type is not the first of its mutual block. Such a name is
# not a label: the block's label is the first type's name. A test plugin
# declares the block (Rocq's own commands refuse the name), standing for a
# crafted .vo. Printed raw, for instance in the warning of an admitted
# library's bytecode compilation, the name would start a line of its own. The
# library is admitted, so it is read without validation. The load must refuse
# it.

. misc/rocqchk_names/lib.sh

build_plugin
compile_theory Packet

msg='has the inductive type name "zqxtwo\nzqxforged", which is not an identifier.'
both_vm d-admit refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.Packet
exit $status
