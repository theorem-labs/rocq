#!/usr/bin/env bash
# incmt3, Review841 round 22, issuecomment-6206781587. B.K is a Module Type
# that includes A; only Print Module Type B.K exposes the copied fields.
. ../structural-copy-lib.sh
uc_structural_copy_refused PK.v fail
