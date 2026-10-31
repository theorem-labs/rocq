#!/usr/bin/env bash

# rocqchk refuses a label that holds a line break and that only the
# implementation (Struct) of a sealed module has: G1 a module sealed by T, G2
# a functor sealed by T, G3 a module N in the implementation, G4 a module type
# U in the implementation. The checker announces the objects of an
# implementation it checks. The load must refuse each library.

. misc/rocqchk_names/lib.sh

build_plugin
msg='has the label "zqxbad\nzqxforged", which is not an identifier.'
for g in G1 G2 G3 G4; do
  compile_theory $g
  both_vm g-$g-norec refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -norec BadNames.$g
done
both_vm g-G1-admit refuse "$msg" zqxforged -o -Q "$d/theories" BadNames -admit BadNames.G1
exit $status
