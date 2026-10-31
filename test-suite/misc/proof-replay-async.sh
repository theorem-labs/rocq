#!/usr/bin/env bash

# BET-84 P3, the replay twin of misc/proof-record-async.sh (reviewer round 2
# of e560ab16e4, X2). Replay decides a proof at its closer, before any of the
# proof's sentences runs, and on a hit it gives no kept sentence to the STM.
# With async proofs the STM runs a proof later, in a worker or when the
# document is joined. So [rocq compile] must refuse -proof-replay and
# -proof-replay-dir with -async-proofs on or lazy, and with -vos (which runs
# with async proofs): a usage error before the file compiles
# (toplevel/coqcargs.ml, check_async_proofs).
#
# - register: Proofs.v of misc/proof-record-async with -proof-record. The
#   record goes to out/rec, read-only.
# - sync: the ordinary grade compile with -proof-replay. Every proof must
#   hit, or the refusals below prove nothing.
# - on, lazy, vos, dir: the same grade compile with -async-proofs on,
#   -async-proofs lazy, -vos, and -async-proofs on with -proof-replay-dir.
#   Each must exit 1, name the async proofs, and write no .vo, no .vos and
#   no summary.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/proof-replay-async/
src=$PWD/../proof-record-async/Proofs.v

rm -rf out
mkdir -p out/reg out/rec
cp "$src" out/reg/Proofs.v
(cd out/reg && rocq c -proof-record Proofs.v)
mv out/reg/Proofs.proof-record.jsonl out/rec/Proofs.proof-record.jsonl
chmod 0444 out/rec/Proofs.proof-record.jsonl
rec=$PWD/out/rec/Proofs.proof-record.jsonl
digest=$(sha256sum "$rec" | cut -d ' ' -f 1)

grade() {
  local name=$1; shift
  rm -rf "out/$name"
  mkdir -p "out/$name"
  cp "$src" "out/$name/Proofs.v"
  (cd "out/$name" && rocq c "$@" -proof-replay-ratio 1 Proofs.v)
}

grade sync -proof-replay "$rec" -proof-replay-digest "$digest"
python3 - out/sync/Proofs.proof-replay.json <<'PY'
import json, sys
s = json.load(open(sys.argv[1], encoding="utf-8"))
print("sync  proofs %s hits %s refused %s" % (s["proofs"], s["hits"], s["refused"]))
if s["refused"] is not None or s["proofs"] < 2 or s["hits"] != s["proofs"]:
    sys.exit("FAIL: the ordinary grade compile must replay every proof")
PY

failed=0
refused() {
  local name=$1 rc=0; shift
  grade "$name" "$@" > "out/$name.log" 2>&1 || rc=$?
  echo "$name exit $rc: $(tail -n 1 "out/$name.log")"
  if [ "$rc" != 1 ]; then
    echo "FAIL: $name: exit $rc, wanted the usage error's 1" >&2; failed=1
  fi
  if ! grep -q -i 'async' "out/$name.log"; then
    echo "FAIL: $name: the error does not name the async proofs" >&2; failed=1
  fi
  for f in Proofs.vo Proofs.vos Proofs.proof-replay.json; do
    if [ -e "out/$name/$f" ]; then
      echo "FAIL: $name: the refused compile wrote $f" >&2; failed=1
    fi
  done
}

refused on -async-proofs on -proof-replay "$rec" -proof-replay-digest "$digest"
refused lazy -async-proofs lazy -proof-replay "$rec" -proof-replay-digest "$digest"
refused vos -vos -proof-replay "$rec" -proof-replay-digest "$digest"
refused dir -async-proofs on -proof-replay-dir "$PWD/out/rec"

exit $failed
