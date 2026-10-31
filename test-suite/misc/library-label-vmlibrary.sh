#!/usr/bin/env bash
# The vmlibrary format in the library label (label version 6, speed-8).
#
# Two builds whose [vmlibrary] segments (the VM bytecode a .vo carries) are in
# different formats cannot read each other's files, so they must never agree
# on a library label: the key carries
# [LibkeyObjects.vmlibrary_format_version], which rocq-library-label prints
# with --vmlibrary-format-version. Why, and what the number means, is the
# version-6 paragraph of vernac/libkeyObjects.mli.
#
# The rule this test holds the build to, in both its cases:
# - the segment starts with a positive version word ([Vmlibrary.format_version]
#   of kernel/vmlibrary.ml, which counts from 1): the key must be that word;
# - it starts with the marshaller's magic, so the build writes no version word:
#   the key must be 0, which no versioned format is.
#
# That is what makes the key and the segment agree: this build binds the
# constant to [Vmlibrary.format_version] (the speed-8 integration member).
# What this test checks is that the key this build reports and the word this
# build's own compiler writes say the same thing; it does not check that the
# key is still bound to that constant. So a key hardcoded to today's value
# passes, and fails once the format moves, as a writer that stops starting
# the segment with its version word fails now.
#
# This test keeps its own copy of the few lines of the lib/objFile.ml layout
# it needs; test-suite/misc/vo_container.py's list of such tests names it.
#
# What this test does not do is compare labels across two formats: no one build
# has both. test-suite/unit-tests/vernac/libkeyObjects_test.ml does that ("a
# label under another vmlibrary format is another label").

set -e

export PATH=$BIN:$PATH

# This test compares a number the label tool prints with the word the compiler
# under test wrote, so the two must come from one build. Unlike the other
# library-label tests it therefore ignores LIBRARY_LABEL, and where no BIN
# says which build that is, it takes the one the rocq it will run belongs to.
unset LIBRARY_LABEL
BIN=${BIN:-$(dirname "$(command -v rocq)")/}
. misc/library-label-tool.inc

fail=0

key=$("$TOOL" --vmlibrary-format-version || echo "no --vmlibrary-format-version")
check "--vmlibrary-format-version prints a number (got '$key')" \
  grep -Eq '^[0-9]+$' <<< "$key"

cd misc
rm -rf _vmlib
mkdir _vmlib
printf 'Definition a := 1 + 1.\nLemma l : a = 2. Proof. reflexivity. Qed.\n' > _vmlib/A.v
rocq c -q -R _vmlib VmlibTest _vmlib/A.v

# The first word of the vmlibrary segment, as a signed 32-bit integer, or a
# line saying why there is none (layout per lib/objFile.ml; the other tests
# that read that layout keep their own copy of these few lines).
word=$(python3 - _vmlib/A.vo <<'PY'
import struct, sys
b = open(sys.argv[1], 'rb').read()
(magic,) = struct.unpack_from(">I", b, 0)
if magic != 0x436F7121:
    print("not a .vo: magic %#x" % magic); raise SystemExit
(sp,) = struct.unpack_from(">Q", b, 8)
(n,) = struct.unpack_from(">I", b, sp); off = sp + 4
found = "no vmlibrary segment"
for _ in range(n):
    (ln,) = struct.unpack_from(">I", b, off); off += 4
    name = bytes(b[off:off+ln]); off += ln
    pos, _sz = struct.unpack_from(">QQ", b, off); off += 32  # pos, len, digest
    if name == b"vmlibrary":
        (found,) = struct.unpack_from(">i", b, pos)
print(found)
PY
)

# The magic the OCaml marshaller writes first, as a signed 32-bit integer:
# Intext_magic_number_small (0x8495A6BE) and _big (0x8495A6BF). A segment that
# starts with one of them carries no version word.
case $word in
  -2070567234|-2070567233)
    check "a build that writes no version word keys the wordless format, 0 (word $word, key $key)" \
      test "$key" = "0"
    ;;
  [1-9]*)
    check "the key names the vmlibrary format this build writes (word $word, key $key; \
this build defines vmlibrary_format_version as Vmlibrary.format_version, now $word)" \
      test "$word" = "$key"
    ;;
  *)
    echo "FAIL the vmlibrary segment of a library this build wrote starts with '$word'"
    fail=1
    ;;
esac

exit $fail
