#!/usr/bin/env bash

set -e

# The expected output lists files in the C locale's order; the glob below
# sorts by the collation locale, so fix it before the glob is expanded.
export LC_ALL=C

cd misc/coqdep-require-safe

code=0
$coqdep -worker @ROCQWORKER@ -Q . 'Pfx' ./*.v > stdout 2> stderr || code=$?

diff -u stdout.ref stdout
diff -u stderr.ref stderr

exit $code
