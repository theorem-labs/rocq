#!/usr/bin/env bash
# tr2 (#841 round 20 review): T, which declares a nested module D : T2,
# gains a field z. B seals X : T, so a fresh B fails and B.vo must be refused.
. ../lt-lib.sh
uc_direct_vernac refused
