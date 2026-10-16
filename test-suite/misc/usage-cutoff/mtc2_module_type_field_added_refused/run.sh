#!/usr/bin/env bash
# mtc2 (#841 round 20 review): Module Type T gains a field. B seals M : T,
# so a fresh B fails (field y missing) and the stale B.vo must be refused.
. ../lt-lib.sh
uc_direct_vernac refused
