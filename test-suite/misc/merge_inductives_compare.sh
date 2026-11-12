#!/usr/bin/env bash

# rocqchk -compare with -merge-inductives (dispatch://BET-895).
#
# The comparator loads the challenge into an environment of its own, beside
# the answer's. The merge step keeps state -- the blocks loaded so far, the
# merges made -- that describes ONE environment, so the challenge load is
# given a fresh state and makes its own merges. When the challenge load still
# saw the answer's state, a challenge block found its own answer-side copy as
# a merge candidate, which the challenge environment does not hold, and the
# run ended in an anomaly (exit 129) with no verdict.
#
# plain/: one library, the same source on both sides, no second copy of any
#   type. The option has nothing to merge here, so the verdicts must be the
#   same with it and without it: the honest answer passes, the forged one (a
#   different statement under the task's name) fails.
# copies/: two copies of one inductive, A.colour and B.colour, and a theorem
#   that type-checks only once they are one type. Both environments merge
#   them; the honest answer passes, the forged one fails, and without the
#   option rocqchk refuses the answer itself rather than give a verdict.
set -eu

. misc/merge_inductives_common.bash

src=misc/merge_inductives_compare

mi_setup
mkdir "$d/cwd"

# mc_tree <case> <tree> [option...]: compile the case's shared sources and the
# tree's own into $d/<case>-<tree>, in the order $mc_order, under $mi_root.
mc_tree () {
  local case=$1 tree=$2; shift 2
  local dst="$d/$case-$tree" f
  mkdir -p "$dst"
  cp "$src/$case/$tree"/*.v "$dst/"
  for f in "$src/$case"/*.v; do [ -f "$f" ] && cp "$f" "$dst/"; done
  for f in $mc_order; do
    $coqc -R "$dst" $mi_root "$@" "$dst/$f.v" > "$d/last.log" 2>&1 \
      || mi_fail "$case/$tree/$f.v was refused"
  done
}

prelude_vo () {
  local w p
  w=$("$BIN"rocq -where)
  for p in "$w/theories/Corelib/Init/Prelude.vo" "$w/theories/Init/Prelude.vo"; do
    [ -f "$p" ] && { echo "$p"; return; }
  done
  mi_fail "cannot find Prelude.vo under $w"
}

# mc_config <case>: the config for the case's challenge, every challenge file
# pinned, the prelude pre-checked, and the one flag every honest answer that
# mentions eq records (see compare.sh).
mc_config () {
  local ch="$d/$1-challenge" files="" sep="" f
  for f in $mc_order; do
    files="$files$sep{\"path\": \"$f.vo\", \"sha256\": \"$("$BIN"rocqchk -sha256 "$ch/$f.vo")\"}"
    sep=", "
  done
  cat > "$d/config.json" <<EOF
{"theorems": [{"name": "$mi_root.$mc_theorem"}],
 "permitted_axioms": [],
 "tolerated_flags": [{"kind": "indices-not-mattering", "object": "Corelib.Init.Logic.eq"}],
 "rewrite_rules": false,
 "prechecked": [{"library": "Corelib.Init.Prelude", "sha256": "$("$BIN"rocqchk -sha256 "$(prelude_vo)")"}],
 "challenge_files": [$files]}
EOF
}

# mc_compare <case> <tree> [option...]: run the comparator on the answer tree,
# in an empty directory. Exit code in $mc_status, verdict in $d/out.json,
# output in $d/last.log. An anomaly is a failure whatever the case expects.
mc_compare () {
  local case=$1 tree=$2; shift 2
  local libs=() f
  for f in $mc_order; do libs+=("$mi_root.$f"); done
  rm -f "$d/out.json"
  set +e
  (cd "$d/cwd" && "$BIN"rocqchk $mi_chk_extra "$@" -silent -Q "$d/$case-$tree" $mi_root \
     -compare "$d/config.json" -challenge "$d/$case-challenge" \
     -compare-out "$d/out.json" "${libs[@]}") > "$d/last.log" 2>&1
  mc_status=$?
  set -e
  mi_no_anomaly "rocqchk -compare $* on $case/$tree"
}

# mc_verdict <case> <tree> <verdict> [option...]: the run completes and gives
# the theorem that verdict.
mc_verdict () {
  local case=$1 tree=$2 want=$3; shift 3
  mc_compare "$case" "$tree" "$@"
  [ "$mc_status" = 0 ] || mi_fail "rocqchk -compare $* on $case/$tree exited $mc_status"
  grep -q "\"name\":\"$mi_root.$mc_theorem\",\"verdict\":\"$want\"" "$d/out.json" \
    || mi_fail "rocqchk -compare $* on $case/$tree: the verdict is not $want: $(cat "$d/out.json")"
  echo "$case/$tree ${*:-(no option)}: $want $(grep -o '"reason":"[^"]*"' "$d/out.json" | head -n 1)"
}

# plain: compiled without the option, compared with and without it.
mc_order="P"
mc_theorem=P.thm
for t in challenge answer forged; do mc_tree plain "$t"; done
mc_config plain
for opt in "" -merge-inductives; do
  mc_verdict plain answer pass $opt
  mc_verdict plain forged fail $opt
done

# copies: the theorem needs the merge, so every tree is compiled with it.
mc_order="A B C"
mc_theorem=C.thm
for t in challenge answer forged; do mc_tree copies "$t" -merge-inductives; done
mc_config copies

mc_verdict copies answer pass -merge-inductives
mc_verdict copies forged fail -merge-inductives

# Each environment makes the merge for itself: the answer's when rocqchk
# checks the answer, the challenge's when the comparator loads the challenge.
mc_verdict copies answer pass -merge-inductives-verbose
n=$(grep -c 'Merged inductive MergeTest\.[AB]\.colour' "$d/last.log" || true)
[ "$n" = 2 ] || mi_fail "expected one merge of colour in each environment, saw $n"
grep 'Merged inductive' "$d/last.log"

# Without the option the two copies stay two types, the answer's C does not
# type-check, and rocqchk refuses it with no verdict.
mc_compare copies answer
[ "$mc_status" != 0 ] || mi_fail "rocqchk -compare without the option accepted the copies answer"
[ ! -f "$d/out.json" ] || mi_fail "rocqchk -compare without the option wrote a verdict: $(cat "$d/out.json")"
echo "copies/answer (no option): refused (exit $mc_status), no verdict"
