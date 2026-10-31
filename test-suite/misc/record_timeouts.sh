#!/usr/bin/env bash

# rocq compile -record-timeouts writes <base>.timeouts.json beside the output
# file: how many wall-clock timeouts the compilation armed, and how many of
# them fired. Checks the four user-visible timeouts (the Ltac1 timeout tactic,
# Timeout, Default Timeout and the Ltac2 Control.timeout/timeoutf), a timeout
# under the par: selector, which a tactic worker runs and reports back, the
# refusal of -async-proofs and -vos, whose delegated proofs do not report, a
# timeout that fires, a file with no timeout, a failing compilation, one killed
# by SIGKILL, that without the option nothing is removed or written and the
# .vo is unchanged, and that proof replay's budget is not counted and a
# compilation it ends leaves no record.

set -u

export PATH="$BIN:$PATH"

D=misc/tmp_record_timeouts
rm -rf "$D"
mkdir -p "$D"

rc=0
fail () { printf 'record_timeouts: %s\n' "$1"; rc=1; }

compile () { # compile NAME [option...]: compile $D/NAME.v, return its status
  local n=$1; shift
  rocq c -q -R "$D" RecordTimeouts "$@" "$D/$n.v" > "$D/$n.out" 2>&1
}

key () { # key NAME KEY: the value of KEY in NAME's record
  sed -n 's/^{"format":1,"armed":\([0-9]*\),"fired":\([0-9]*\)}$/\1 \2/p' \
      "$D/$1.timeouts.json" 2> /dev/null | cut -d' ' -f"$2"
}

check () { # check NAME MIN_ARMED MIN_FIRED
  local n=$1 mina=$2 minf=$3 a f
  if [ ! -f "$D/$n.timeouts.json" ]; then fail "$n: no record written"; return; fi
  printf '%s: %s\n' "$n" "$(cat "$D/$n.timeouts.json")"
  a=$(key "$n" 1); f=$(key "$n" 2)
  if [ -z "$a" ]; then fail "$n: the record is not one {\"format\":1,...} line"; return; fi
  [ "$a" -ge "$mina" ] || fail "$n: armed $a, expected at least $mina"
  [ "$f" -ge "$minf" ] || fail "$n: fired $f, expected at least $minf"
  [ "$a" -ge "$f" ] || fail "$n: fired $f more than armed $a"
}

case_ () { # case_ NAME MIN_ARMED MIN_FIRED [option...] < source
  local n=$1 mina=$2 minf=$3; shift 3
  cat > "$D/$n.v"
  compile "$n" -record-timeouts "$@" || fail "$n: compilation failed"
  check "$n" "$mina" "$minf"
}

# 1. The Ltac1 timeout tactic.
case_ ltac1 1 0 <<'EOF'
Goal True.
  timeout 3600 idtac.
  exact I.
Qed.
EOF

# 2. The Timeout control.
case_ vernac 1 0 <<'EOF'
Timeout 3600 Check nat.
EOF

# 3. The Default Timeout option.
case_ default 1 0 <<'EOF'
Set Default Timeout 3600.
Check nat.
EOF

# 4. The Ltac2 Control.timeout external.
case_ ltac2 1 0 <<'EOF'
Require Import Ltac2.Ltac2.
Ltac2 Eval Control.timeout 3600 (fun () => ()).
EOF

# 5. The Ltac2 Control.timeoutf external. Ltac2 has no float literal, so the
#    float comes out of a primitive float term.
case_ ltac2f 1 0 <<'EOF'
Require Import Ltac2.Ltac2.
Require Import Corelib.Floats.PrimFloat.
Ltac2 seconds () :=
  match Constr.Unsafe.kind constr:(3600%float) with
  | Constr.Unsafe.Float f => f
  | _ => Control.throw Not_found
  end.
Ltac2 Eval Control.timeoutf (seconds ()) (fun () => ()).
EOF

# 6. A timeout under the par: selector, which a tactic worker arms and reports
#    back to the master with its answer.
case_ par 1 0 <<'EOF'
Lemma par_lemma : True /\ True.
Proof.
  split.
  par: timeout 3600 exact I.
Qed.
EOF

# 7. A delegated proof reports nothing back, so -async-proofs and -vos are
#    refused with the option, and a refused compilation leaves no record.
cat > "$D/async.v" <<'EOF'
Lemma async_lemma : True /\ True.
Proof. split; timeout 3600 exact I. Qed.
EOF
compile async -async-proofs on || fail "async: compilation without the option failed"
if compile async -record-timeouts -async-proofs on; then
  fail "async: -record-timeouts -async-proofs on was accepted"
fi
grep -q 'incompatible with -async-proofs' "$D/async.out" \
  || fail "async: the refusal does not name -async-proofs: $(cat "$D/async.out")"
[ -f "$D/async.timeouts.json" ] && fail "async: the refused compilation wrote a record"
if compile async -record-timeouts -vos; then
  fail "async: -record-timeouts -vos was accepted"
fi
grep -q 'incompatible with -vos' "$D/async.out" \
  || fail "async: the refusal does not name -vos: $(cat "$D/async.out")"
[ -f "$D/async.timeouts.json" ] && fail "async: the refused -vos compilation wrote a record"

# 8. A timeout that fires.
case_ fired 1 1 <<'EOF'
Goal True.
  Fail Timeout 1 do 1000000000 idtac.
Abort.
EOF

# 9. A file with no timeout.
case_ none 0 0 <<'EOF'
Definition zero := 0.
EOF
[ "$(cat "$D/none.timeouts.json")" = '{"format":1,"armed":0,"fired":0}' ] \
  || fail "none: the record is not an empty one"

# 10. A failing compilation still writes the record.
cat > "$D/failing.v" <<'EOF'
Timeout 3600 Check nat.
Check no_such_constant.
EOF
if compile failing -record-timeouts; then fail "failing: compilation succeeded"; fi
[ -f "$D/failing.vo" ] && fail "failing: a .vo was written"
check failing 1 0

# 11. A compilation killed by SIGKILL leaves no record, not even a stale one.
cat > "$D/killed.v" <<'EOF'
Goal True.
  do 1000000000 idtac.
EOF
printf '{"format":1,"armed":0,"fired":0}\n' > "$D/killed.timeouts.json"
rocq c -q -R "$D" RecordTimeouts -record-timeouts "$D/killed.v" > "$D/killed.out" 2>&1 &
killed_pid=$!
# Wait for the compilation to remove the stale record, then kill it.
for _ in $(seq 600); do
  [ -f "$D/killed.timeouts.json" ] || break
  kill -0 "$killed_pid" 2> /dev/null || break
  sleep 0.1
done
kill -9 "$killed_pid" 2> /dev/null
wait "$killed_pid" 2> /dev/null
if [ -f "$D/killed.timeouts.json" ]; then
  fail "killed: a record is there: $(cat "$D/killed.timeouts.json")"
fi

# 12. Without the option, the record is neither removed nor written, and the
#     .vo is the one the option gives.
printf 'not a record\n' > "$D/ltac1.timeouts.json"
compile ltac1 || fail "no option: compilation failed"
cp "$D/ltac1.vo" "$D/ltac1-without.vo"
[ "$(cat "$D/ltac1.timeouts.json")" = 'not a record' ] \
  || fail "no option: the record was touched"
compile ltac1 -record-timeouts || fail "with option: compilation failed"
cmp "$D/ltac1-without.vo" "$D/ltac1.vo" || fail "the option changed the .vo"

# 13. Proof replay's budget (BET-84) runs each sentence under a deadline that
#     stands for the build driver's own per-file kill. It is not a timeout of
#     the file: a replay compile records what the same compile without replay
#     records, none for a file with no timeout and the Timeout's own for one
#     with a Timeout. The record directory is
#     empty, so no proof replays and the budget alone is under test.
mkdir -p "$D/norecords"
budget () { # budget NAME SECONDS: compile NAME with replay's budget
  compile "$1" -record-timeouts -proof-replay-dir "$D/norecords" \
    -proof-replay-ratio 1 -proof-replay-budget "$2"
}
cat > "$D/budget_none.v" <<'EOF'
Lemma budget_lemma : True.
Proof. exact I. Qed.
EOF
budget budget_none 3600 || fail "budget_none: compilation failed: $(tail -n 3 "$D/budget_none.out")"
[ "$(cat "$D/budget_none.timeouts.json" 2> /dev/null)" = '{"format":1,"armed":0,"fired":0}' ] \
  || fail "budget_none: the record is not an empty one: $(cat "$D/budget_none.timeouts.json" 2>&1)"
cat > "$D/budget_one.v" <<'EOF'
Timeout 3600 Check nat.
EOF
compile budget_one -record-timeouts || fail "budget_one: compilation without replay failed"
plain=$(cat "$D/budget_one.timeouts.json" 2> /dev/null)
budget budget_one 3600 || fail "budget_one: compilation failed: $(tail -n 3 "$D/budget_one.out")"
[ -n "$plain" ] && [ "$(cat "$D/budget_one.timeouts.json" 2> /dev/null)" = "$plain" ] \
  || fail "budget_one: replay recorded $(cat "$D/budget_one.timeouts.json" 2>&1), without replay $plain"

# 14. A compile that replay's budget ends exits 124, as the driver's kill
#     does, and leaves no record, as a compile killed by SIGKILL leaves none.
cat > "$D/budget_killed.v" <<'EOF'
Goal True.
  do 1000000000 idtac.
EOF
printf '{"format":1,"armed":0,"fired":0}\n' > "$D/budget_killed.timeouts.json"
budget budget_killed 2
st=$?
[ "$st" = 124 ] || fail "budget_killed: exit status $st, expected 124: $(tail -n 3 "$D/budget_killed.out")"
if [ -f "$D/budget_killed.timeouts.json" ]; then
  fail "budget_killed: a record is there: $(cat "$D/budget_killed.timeouts.json")"
fi

if [ $rc = 0 ]; then rm -rf "$D"; fi
exit $rc
