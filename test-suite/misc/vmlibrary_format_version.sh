#!/usr/bin/env bash
# The vmlibrary segment of a .vo holds VM bytecode: instruction words the C
# interpreter of the READING process dispatches on. A reader whose VM does not
# have an opcode the writer emitted used to jump wherever its own table sends
# that word and die with no message (dispatch://BET-241: a library written by a
# later Rocq made the reader dump core, SIGABRT).
#
# The segment now starts with its own format version (kernel/vmlibrary.ml), read
# before anything in it is unmarshalled. This test raises that version word to a
# value no reader knows, with nothing else changed but that segment's MD5, and
# requires the refusal: an error naming the library and both versions, with
# an ordinary exit status, not a signal and not a silent load.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)

cat > "$d/Defs.v" <<'EOF'
Unset Elimination Schemes.
Inductive bool : Set := true | false.
Definition b : bool := true.
EOF

cat > "$d/Use.v" <<'EOF'
Require Import Defs.
Definition c : bool := b.
EOF

rocq c -noinit -R "$d" "" "$d/Defs.v"

# Control: the file as written loads, so a refusal below is the version alone.
rocq c -noinit -R "$d" "" "$d/Use.v"
rm "$d/Use.vo"

# Raise the segment's format version by one. misc/vo_container.py rewrites the
# container, and the segment keeps its length, so nothing differs but that word
# and the segment's MD5, which the file holds after it and in the summary; the
# script prints the version it found.
found=$(python3 - "$(dirname "$0")" "$d" <<'PY'
import struct, sys
sys.path.insert(0, sys.argv[1])
import vo_container

d = sys.argv[2]
vo_version, segments = vo_container.read(d + "/Defs.vo")
assert "vmlibrary" in segments, "no vmlibrary segment"
data = segments["vmlibrary"]
assert len(data) >= 4, "vmlibrary segment shorter than its version word"
(version,) = struct.unpack_from(">i", data, 0)
# A plain small integer, not a marshalled value: a segment that does not start
# with its format version is the bug this test is about.
assert 0 < version < 1000, "vmlibrary segment does not start with a format version: %d" % version
segments["vmlibrary"] = struct.pack(">i", version + 1) + data[4:]
vo_container.write(d + "/Defs.vo", vo_version, segments)
print(version)
PY
)

set +e
rocq c -noinit -R "$d" "" "$d/Use.v" > "$d/out" 2> "$d/err"
rc=$?
set -e

if [ "$rc" -eq 0 ]; then
  >&2 echo "FAILURE: a vmlibrary segment in format version $((found + 1)) was loaded"
  exit 1
fi
if [ "$rc" -ge 128 ]; then
  >&2 echo "FAILURE: the reader died of signal $((rc - 128)) instead of refusing the segment"
  cat "$d/err" >&2
  exit 1
fi

# One line, so the printer's wrapping cannot hide a word from the match.
msg=$(tr -s '[:space:]' ' ' < "$d/err")
for want in "Defs" \
            "is in vmlibrary format version $((found + 1))" \
            "reads vmlibrary format version $found"; do
  case $msg in
    *"$want"*) ;;
    *)
      >&2 echo "FAILURE: the refusal does not say \"$want\""
      >&2 echo "$msg"
      exit 1 ;;
  esac
done

rm -rf "$d"
