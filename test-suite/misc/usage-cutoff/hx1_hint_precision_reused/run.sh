#!/usr/bin/env bash
# hx1 (#841 issuecomment-6205909210; reviewer expects REUSED). Accepted P3:
# B queries wdb, and wdb changes. Refusing any change to a queried hint DB
# is sound; reusing needs a per-query hint transcript, which is not cheap.
# Precision test, not soundness: auto closes True without the hint.
. ../round16-lib.sh
uc_round16 overrefused
