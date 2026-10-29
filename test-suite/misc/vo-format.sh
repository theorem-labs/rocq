#!/usr/bin/env bash
# What a .vo stores, against the .vo format version (BET-342 M8).
#
# rocq-library-label --vo-representation prints how this build represents a
# .vo; what that printing covers, and what it does not, is at
# [vo_representation] in checker/library_label.ml.
# misc/vo-format/reference.txt holds the printing as it was last recorded,
# with the .vo format version (Coq_config.vo_version, written by
# tools/configure/configure.ml) it was recorded at.
#
# A build whose printing differs reads or writes .vo values differently from
# the build that recorded the reference. Such a build must carry another .vo
# format version, so that a file it would read as the wrong values is
# refused by its magic number instead. So a difference fails, and names what
# to do:
# - the version is the recorded one: bump vo_magic in
#   tools/configure/configure.ml, then record the new printing;
# - the version moved already: record the new printing.
# Recording is one cp, which the failure prints. The test never passes on a
# reference it does not match except in the one case below: a reference left
# behind by a version bump would make every later change pass.
#
# The one difference that passes is an object kind this build has and the
# reference does not. A file names a kind by the hash of its name
# (clib/dyn.ml), and a build that does not know that hash refuses the file
# (Libobject.load_object, library/libobject.ml, Not_found) rather than
# reading a value at the wrong type, so a new kind needs no new .vo
# version. A declared option is one (library/goptions.ml), so a release
# that adds an option would otherwise be told to bump the version, which
# moves every library label. A kind the reference has and this build does
# not, a renamed kind and any other line still fail.
#

set -e

export PATH=$BIN:$PATH

. misc/library-label-tool.inc

cd misc/vo-format
rm -rf _test
mkdir _test
REF=reference.txt
if [ ! -s "$REF" ]; then
  echo "FAIL $PWD/$REF is missing or empty"
  exit 1
fi

"$TOOL" --vo-representation > _test/current.txt
if ! grep -q '^vo_version ' _test/current.txt; then
  echo "FAIL rocq-library-label --vo-representation printed no representation"
  exit 1
fi

diff -u "$REF" _test/current.txt > _test/diff.txt && rc=0 || rc=$?
if [ "$rc" = 0 ]; then
  echo "PASS what a .vo stores is what $REF records"
  exit 0
fi
if [ "$rc" != 1 ]; then
  echo "FAIL diff of $PWD/$REF and _test/current.txt failed (exit $rc)"
  exit 1
fi

version() { awk '$1 == "vo_version" { print $2 }' "$1"; }
recorded=$(version "$REF")
current=$(version _test/current.txt)

# Every differing line, by side; an added object kind is the one difference
# that is not a format change.
grep '^-[^-]' _test/diff.txt | cut -c2- > _test/gone.txt || true
grep '^+[^+]' _test/diff.txt | cut -c2- > _test/new.txt || true
if [ ! -s _test/gone.txt ] && [ -s _test/new.txt ] && ! grep -qv '^object_kind ' _test/new.txt; then
  echo "PASS what a .vo stores is what $REF records, plus $(wc -l < _test/new.txt) object kind(s) this build registers:"
  sed 's/^/       /' _test/new.txt
  echo "     a build without a kind refuses a file that names it, so this needs no .vo version"
  echo "     record it: cp $PWD/_test/current.txt $PWD/$REF"
  exit 0
fi

echo "--- what changed (first 60 lines of the diff)"
head -60 _test/diff.txt
if [ "$recorded" = "$current" ]; then
  echo "FAIL the representation of what a .vo stores changed at .vo format version $current"
  echo "     bump vo_magic in tools/configure/configure.ml, then record the new printing:"
else
  echo "FAIL the .vo format version moved ($recorded -> $current) with the representation"
  echo "     record the new printing:"
fi
echo "     cp $PWD/_test/current.txt $PWD/$REF"
exit 1
