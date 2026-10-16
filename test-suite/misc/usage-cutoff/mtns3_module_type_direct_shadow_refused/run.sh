#!/usr/bin/env bash
# mtns3 (#841 round 22): soundness counterpart of the mtunrel0 fix. A
# directly adds a Module Type named T, shadowing X.T, which B seals M with.
# A fresh B fails (M lacks zzq). The fix drops an empty filtered module-type
# wrapper from A exact objects digest, so the refusal must come from the
# name closure, not from that digest.
. ../lt-lib.sh
uc_direct_vernac refused
