#!/usr/bin/env bash
# P3 control from #841 issuecomment-6203143572: the reviewer labels nl2
# reused correctly, but this closure-wide basename rule sees newly reachable
# Y.f0 beside X.f0. Fresh B succeeds, so refusal costs only a recompile.
. ../round16-lib.sh
uc_round16 overrefused
