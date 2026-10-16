#!/usr/bin/env bash
# modsynprec1 (#841 issuecomment-6205909210; reviewer expects REUSED).
# Accepted P3: Module N's notation is active only after Import N. Telling
# that apart needs B's module-import transcript, not a library digest.
. ../round16-lib.sh
uc_round16 overrefused
