#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. Module alias of a whole library,
# with a plain Definition added to the aliased library. Same hole as
# incdef1 through `Module K := A` rather than `Include A`.
. ../structural-copy-lib.sh
uc_structural_copy_refused PK.v ok
