#!/usr/bin/env bash
# lt2: A (a direct root) gains foo, a basename B recorded from Y through
# X's Ltac t := exact foo. check_required's G7 shadow rule refuses. A
# fresh B succeeds because Ltac resolved t to Y.foo when X compiled, so
# this is an accepted P3 over-refusal, like nl2, oc1 and cost2.
. ../lt-lib.sh
uc_direct_vernac overrefused
