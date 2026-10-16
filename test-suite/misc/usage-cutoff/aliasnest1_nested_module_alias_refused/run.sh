#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. The alias target is a module
# INSIDE the changed library, not the library itself: `Module K := A.M`
# with `A.M` gaining a field. Refused at v1 and fd1fa9c65b, reused at
# 4be0c270eb (#841 REPORT-cutoff2-r16, "the open soundness hole").
. ../structural-copy-lib.sh
uc_structural_copy_refused PK.v ok
