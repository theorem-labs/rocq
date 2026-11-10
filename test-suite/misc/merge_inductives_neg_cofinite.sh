#!/usr/bin/env bash

# Inductive against coinductive: the two blocks have the same name, the same
# constructor and the same constructor type, and differ only in Finite against
# CoFinite.
#
# Bad.v is the witness of what the refusal buys, and it is a real one. The
# spec's block has no base case, so induction on it proves False; the agent's
# coinductive copy is inhabited by [zeros]. Were the two merged, Bad.v would
# prove False, so it must be refused too.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_cofinite

mi_coqc_fails Bad -merge-inductives
