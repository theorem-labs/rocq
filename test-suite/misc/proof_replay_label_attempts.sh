#!/usr/bin/env bash
# Proof replay (BET-84) under -location-free-label. Before it replays a proof,
# replay resolves the names of each later Require to tell whether that Require
# is late (Synterp.require_locate ~warn:false). That check must record no
# attempt (vernac/attempts.ml): the object a replaying compile writes holds the
# attempts the stock compile's object holds, here the one attempt of the Fail
# Require. Every compile runs in the same directory, because an attempt records
# the paths it probed.

set -e

export PATH=$BIN:$PATH

. misc/library-label-tool.inc

D=misc/tmp_proof_replay_label_attempts
rm -rf "$D"
mkdir -p "$D/src" "$D/recs"
cat > "$D/src/A.v" <<'EOF'
Lemma p : True.
Proof. exact I. Qed.

Fail Require Test.Missing.

Lemma q : True.
Proof. exact I. Qed.
EOF
comp() { (cd "$D/src" && rocq c -q -location-free-label -R . Test "$@" A.v); }

# The stock compile.
comp
"$TOOL" --attempts "$D/src/A.vo" > "$D/stock.txt"

# The registration, and its record published as replay reads one.
comp -proof-record
rec="$D/recs/Test.A.proof-record.jsonl"
cp "$D/src/A.proof-record.jsonl" "$rec"
sha256sum "$rec" | cut -d' ' -f1 > "$rec.sha256"
chmod 0444 "$rec" "$rec.sha256"

# The replaying compile.
comp -proof-replay-dir ../recs -proof-replay-ratio 1
"$TOOL" --attempts "$D/src/A.vo" > "$D/replay.txt"

fail=0
n=$(grep -c 'an attempted Require of Test.Missing' "$D/replay.txt" || true)
if [ "$n" != 1 ]; then
  echo "proof_replay_label_attempts: the replaying compile recorded $n attempts of Test.Missing, not 1"
  fail=1
fi
if ! cmp -s "$D/stock.txt" "$D/replay.txt"; then
  echo "proof_replay_label_attempts: the attempts differ from the stock compile's:"
  diff "$D/stock.txt" "$D/replay.txt" || true
  fail=1
fi
if [ $fail = 0 ]; then rm -rf "$D"; fi
exit $fail
