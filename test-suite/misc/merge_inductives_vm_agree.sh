#!/usr/bin/env bash

# The bytecode VM compares constructed values by tag and arity; the kernel
# compares constructor names. They can therefore disagree about a term that
# mixes two copies' constructors -- which only a library built with the
# option contains.
#
# What this pins: WITH the option, the two conversions agree, so a check may
# use -bytecode-compiler yes. The one cell where they do not agree needs all
# three of: the option OFF, the mixed-name library admitted unchecked
# (-norec, so nothing re-derives it), and the VM on. That cell is asserted
# as the known limit it is, not as correct behaviour: it is the reason a
# reader must not admit a merge-written library unchecked with the option
# off.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_vm_agree

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Mid -merge-inductives
mi_coqc GoodVM -merge-inductives
mi_coqc EvilVM -merge-inductives

# verdict <expected rc> <args...>: the rc of one rocqchk run.
verdict () {
  local want=$1; shift
  set +e
  "$BIN"rocqchk -silent -R "$d" $mi_root "$@" > "$d/last.log" 2>&1
  local got=$?
  set -e
  [ "$got" = "$want" ] || mi_fail "rocqchk $* gave $got, expected $want"
  mi_no_anomaly "rocqchk $*"
}

# With the option, VM on and VM off give the same verdict everywhere.
for bc in yes no; do
  verdict 0 -merge-inductives -bytecode-compiler $bc -norec "$mi_root.Mid"
  verdict 0 -merge-inductives -bytecode-compiler $bc "$mi_root.GoodVM"
  verdict 0 -merge-inductives -bytecode-compiler $bc "$mi_root.EvilVM"
  verdict 0 -merge-inductives -bytecode-compiler $bc -norec "$mi_root.EvilVM"
done

# Without the option they also agree, as long as the mixed-name library is
# checked rather than admitted.
for bc in yes no; do
  verdict 129 -bytecode-compiler $bc -norec "$mi_root.Mid"
  verdict 129 -bytecode-compiler $bc "$mi_root.GoodVM"
  verdict 129 -bytecode-compiler $bc "$mi_root.EvilVM"
done

# The one disagreement, asserted as the limit it is: option off, the
# mixed-name library admitted unchecked, VM on accepts what VM off refuses.
verdict 0   -bytecode-compiler yes -norec "$mi_root.EvilVM"
verdict 129 -bytecode-compiler no  -norec "$mi_root.EvilVM"
