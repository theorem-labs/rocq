#!/usr/bin/env bash

# The same two constructor names, one block in Prop and one in Set. The
# spec's copy has two constructors in Prop, so it is squashed and may only be
# eliminated into Prop; the agent's may be eliminated into anything. Arity,
# sort and elimination data all have to be compared, and this block must not
# merge.
#
# No False witness: a Prop with two constructors that cannot be told apart is
# still a type with two elements, so the agent's library stays true of the
# spec's copy and the merge, wrong as it is, is not by itself contradictory.
# The test pins that Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_sort
