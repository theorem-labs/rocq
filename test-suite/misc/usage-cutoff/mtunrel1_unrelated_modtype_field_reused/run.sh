#!/usr/bin/env bash
# mtunrel1 (#841 round 21 review, P2): mtunrel0 with a field in the unrelated
# Module Type U. A fresh B succeeds, so reuse is expected.
. ../lt-lib.sh
uc_direct_vernac reused
