#!/usr/bin/env bash

# One constructor takes one argument more: [C : nat -> nat -> t] against
# [C : nat -> t]. Block size, type and constructor names all match, so only
# the constructor's type tells the two blocks apart.
#
# No False witness: granting this merge would leave the agent's [C 0 1] an
# application of a one-argument constructor to two arguments, which no term
# the kernel accepts can be built from, so the strongest thing to pin is that
# Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_ctor_arity
