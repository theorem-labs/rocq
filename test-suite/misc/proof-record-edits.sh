#!/usr/bin/env bash

# BET-84 P2. A replay may reuse a proof's stored term only when everything the
# proof read is unchanged, so an edit of an input a proof reads must show in
# its record. Each directory under misc/proof-record-edits/ is one edit: A.v
# and B.v differ in one input of the proofs that its `expect` file names, and
# both compile. Each variant is compiled with -proof-record in a new process,
# at the same path under the same logical name, so that the two compiles
# differ only in the file's text (a recorded value can hold source locations,
# which name the file). check.py then requires each record to refuse the
# other compile (the witnesses are described there).
#
# The cases are channels that the Claude gate at 0f8d815732 found open.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-record-edits/

rm -rf out
status=0
for case in */; do
  case=${case%/}
  [ -f "$case/expect" ] || continue
  compiled=yes
  for v in A B; do
    rm -rf "out/$case/src"
    mkdir -p "out/$case/src" "out/$case/$v"
    cp "$case/$v.v" "out/$case/src/File.v"
    if rocq c -R "out/$case/src" Top -proof-record "out/$case/src/File.v"; then
      mv "out/$case/src/File.proof-record.jsonl" "out/$case/$v/"
    else
      echo "FAIL: $case: $v.v does not compile" >&2
      compiled=no
    fi
  done
  if [ $compiled = yes ]; then
    python3 check.py "$case" "out/$case/A/File.proof-record.jsonl" "out/$case/B/File.proof-record.jsonl" || status=1
  else
    status=1
  fi
done
exit $status
