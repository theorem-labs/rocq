#!/usr/bin/env bash
# Print Assumptions reuses traversals while the environment stays the same,
# and the opaque proofs it reads are not part of the environment. A Require
# that fails because the file it finds holds another library still records
# that file's opaque proofs, under the name of the library in the file, before
# it checks that name. When that library is already loaded, the Require
# replaces its opaque proofs and leaves the environment as it was. A query
# after it must read the new proofs, as without reuse: Main.out is the output
# of Rocq without the reuse.
set -e
export PATH=$BIN:$PATH
cd misc/print-assumptions-memo-opaque-table
rm -rf _test
mkdir -p _test/first _test/second
cp first/Y.v Main.v _test/first
cp second/Y.v _test/second
cd _test
rocq c -q -Q first "" first/Y.v
rocq c -q -Q second "" second/Y.v
cp second/Y.vo first/X.vo
rocq c -q -Q first "" first/Main.v > Main.actual.out 2> Main.actual.err
diff -u ../Main.out Main.actual.out
diff -u /dev/null Main.actual.err
