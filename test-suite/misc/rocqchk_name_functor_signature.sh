#!/usr/bin/env bash

# rocqchk refuses a label that holds a line break inside a functor's
# signature: in the body of a functor module type (G5), in the body of an
# unsealed functor, whose fields only its signature holds (G6), and in the
# type of a functor parameter (L2, whose parameter has the type L1.TP: QQQ is
# rewritten in the library segment of L2.vo only, so L1 stays valid). On a
# -norec run, the checker prints those fields in its `checking cst:` progress
# lines. Each library is checked (-norec) and admitted. The load must refuse
# it.

. misc/rocqchk_names/lib.sh

build_plugin
msg='has the label "zqxbad\nzqxforged", which is not an identifier.'
for g in G5 G6; do
  compile_theory $g
  both_vm fs-$g-norec refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.$g
  both_vm fs-$g-admit refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.$g
done

compile_plain "$d/base" L1 L2
ocaml "$R" "$d/base/L2.vo" library QQQ $'QQ\n'
msg='has the label "zqxbadQQ\nzqxforged", which is not an identifier.'
both_vm fs-param-norec refuse "$msg" zqxforged -o -Q "$d/base" BadNames -norec BadNames.L2
both_vm fs-param-admit refuse "$msg" zqxforged -o -Q "$d/base" BadNames -admit BadNames.L2
exit $status
