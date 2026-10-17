#!/usr/bin/env bash
# ROCQ_DEBUG_ASSUMPTIONS_MEMO=1 reports each reuse of a Print Assumptions
# traversal on standard error, and only there: standard output is the same
# with the variable set or unset, Set Debug "all" included.

set -e

export PATH=$BIN:$PATH

cd misc/print-assumptions-memo
rm -rf _test
mkdir _test
cp Debug.v Debug.err _test
cd _test

rocq c -q Debug.v > plain.out 2> plain.err
ROCQ_DEBUG_ASSUMPTIONS_MEMO=1 rocq c -q Debug.v > debug.out 2> debug.err
diff -u --strip-trailing-cr Debug.err debug.err
diff -u plain.out debug.out
diff -u /dev/null plain.err
