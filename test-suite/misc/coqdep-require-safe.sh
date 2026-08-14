#!/usr/bin/env bash

set -e

cd misc/coqdep-require-safe

code=0
$coqdep -worker @ROCQWORKER@ -Q . 'Pfx' ./*.v > stdout.unsorted 2> stderr || code=$?

# rocqdep dependency lines are a set; their traversal order can differ across
# platforms. Keep checking every complete edge while making the golden output
# independent of that unspecified order.
LC_ALL=C sort stdout.unsorted > stdout

diff -u stdout.ref stdout
diff -u stderr.ref stderr

exit $code
