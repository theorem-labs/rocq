#!/bin/bash
# run.sh -- the per-proof replay fixtures (BET-84 gate part 2, dispatch://BET-119).
#
#   run.sh --list
#   run.sh [--only FIXTURE]... [--slow] [--segcmp PATH] BINDIR OUTDIR
#
# BINDIR  the directory that holds `rocq` and `rocqchk` under test
# OUTDIR  where each fixture's trees, objects and logs go (one subdirectory each)
# --only  run one fixture; repeat the option for more
# --slow  also run the fixtures that take minutes (the budget fixture)
# --segcmp  lane R1's segcmp_norm, built; without it the object comparison is in
#         Python and cannot decide a vmlibrary-only difference.  SEGCMP_NORM in
#         the environment does the same.
#
# A Rocq built with dune needs its own ROCQLIB, ROCQRUNTIMELIB and OCAMLPATH:
# this script passes the environment through, so export them before calling it.
# It prints one line per fixture (PASS, FAIL or SKIP) and exits 1 if any failed.
# Nothing but python3 is needed.
set -euo pipefail
exec python3 "$(dirname "${BASH_SOURCE[0]}")/runner.py" "$@"
