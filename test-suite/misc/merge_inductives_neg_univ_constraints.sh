#!/usr/bin/env bash

# Two monomorphic copies whose own levels carry different constraints: Spec
# has `Constraint u < v`, Agent does not. Everything else reads the same, so
# this is the test that the constraints of the two sides are compared, not
# only the declarations. (It used to use polymorphic blocks; those never
# merge now, which made it pass for the wrong reason -- review finding P3-4.)
#
# No False witness: the test pins that Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_univ_constraints
