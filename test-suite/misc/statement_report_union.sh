#!/usr/bin/env bash

# rocqchk -statement-report judges each statement alone, but a check that
# loads the sealings of all the statements loads them together, and each
# sealing adds the universe constraints that its comparison needs. The
# constraints of the statements that read [match] must also be consistent
# together. coqc compiles the sealing of each row once, before the cases; for
# each case, rocqchk then loads together the sealings of its rows that coqc
# accepted. The report must be complete exactly when they load. When they do
# not load, the report is refused: a warning says why and gives the positions
# of the statements that read [match] among the requests, and the report has
# no END STATEMENT REPORT and NO statement line at all. A reader keeps each
# statement that the next statement line closes, so every statement printed
# before the refusal but the last would still count: the checker must decide
# the union before it prints the first statement. All of this must hold, with
# the same output, at every rocqchk -j width (widths, below).
set -eu

D=misc/statement_report_union
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Defs.v" "$d/"

$coqc -noinit -Q "$d" StmtUnion "$d/Defs.v"

# <row>|<model>|<verdict alone>
rows='ab|m_a|match
bc|m_b|match
part|m_part|universes-differ
p_a|m_poly|match
p_c|m_poly|match
p_ab|m_poly|match'

# ab, bc: each sealing loads alone, and the report is complete.
# ab_bc: [a <= b] and [b <= c] contradict [c < a], so the report is refused.
# bc_ab: the same pair in the other request order, refused all the same.
# ab_part: [part] reads universes-differ after its comparison needed [b = c].
#   A statement that does not read match adds nothing, so the report is
#   complete. This guards against refusing too much.
# p_a_p_c: two instances of one polymorphic model, at [a] and at [c]. Each
#   sealing has its own fresh universe, so the report is complete. Sharing it
#   would give [a = c]. This guards against refusing too much.
# p_ab_bc: the polymorphic model's sealing adds [a <= b] through its fresh
#   universe, which [bc]'s [b <= c] contradicts, so the report is refused.
# ab_part_bc: the refusal gives requests 1 and 3, the two that read match.
# <case>|<rows, in request order>|<expected report>
cases='ab|ab|complete
bc|bc|complete
ab_bc|ab bc|refused
bc_ab|bc ab|refused
ab_part|ab part|complete
p_a_p_c|p_a p_c|complete
p_ab_bc|p_ab bc|refused
ab_part_bc|ab part bc|refused'

# rocqchk -j N checks only opaque proofs in worker processes and builds the
# report in the main process after every worker is reaped, so the report must
# not depend on N. Releases carry rocqchk -j, and the grade runs rocqchk at
# widths 4 to 16. Each case runs at -j 1, the sequential reference, and at -j 4
# and -j 16, the ends of that range: at both, the opaque proofs of Defs.v go to
# worker processes (checked below). Each width must pass every check, and must
# give, for each case, the report output byte for byte and the load result
# that -j 1 gives.
widths='1 4 16'

declare -A model alone sealing
fail=0

while IFS='|' read -r row m expected; do
  model[$row]=$m; alone[$row]=$expected
  printf 'Require StmtUnion.Defs.\nModule X <: StmtUnion.Defs.S_%s.\n  Definition f := StmtUnion.Defs.%s.\nEnd X.\n' \
    "$row" "$m" > "$d/Seal_$row.v"
  if $coqc -noinit -Q "$d" StmtUnion "$d/Seal_$row.v" < /dev/null > "$d/seal_$row.log" 2>&1; then
    sealing[$row]=accepted
  elif grep -q 'Signature components for field f do not match' "$d/seal_$row.log"; then
    sealing[$row]=refused
  else
    sealing[$row]=error; cat "$d/seal_$row.log"; fail=1
  fi
  case "${alone[$row]},${sealing[$row]}" in
    match,accepted | universes-differ,refused) ;;
    *) echo "row $row: verdict alone ${alone[$row]}, sealing alone ${sealing[$row]}"; fail=1 ;;
  esac
done <<< "$rows"

# The opaque proofs of Defs.v must give the workers work at every width above
# 1, or the comparison below would compare -j 1 with itself.
for j in $widths; do
  [ "$j" = 1 ] && continue
  if ! "$BIN"rocqchk -j "$j" -d checker-workers -silent -Q "$d" StmtUnion StmtUnion.Defs \
       > "$d/workers_$j.log" 2>&1 \
     || ! grep -q 'done: [1-9][0-9]* workers forked' "$d/workers_$j.log"; then
    echo "-j $j: rocqchk forked no worker process, so this test does not test -j $j"
    cat "$d/workers_$j.log"; fail=1
  fi
done

for j in $widths; do
  w=$d/w$j
  mkdir "$w"
  echo "rocqchk -j $j"
  printf '%-9s %-9s %-9s %s\n' case expected report 'sealings together'
  while IFS='|' read -r case_ case_rows expected; do
    : > "$d/req_$case_"
    libs=()
    for row in $case_rows; do
      printf '%s StmtUnion.Defs.%s StmtUnion.Defs.t_%s\n' "$row" "${model[$row]}" "$row" >> "$d/req_$case_"
      if [ "${sealing[$row]}" = accepted ]; then libs+=("StmtUnion.Seal_$row"); fi
    done

    out=$w/out_$case_
    if ! "$BIN"rocqchk -j "$j" -silent -statement-report "$d/req_$case_" -Q "$d" StmtUnion StmtUnion.Defs \
         > "$out" 2>&1; then
      echo "case $case_: rocqchk exited non-zero"; cat "$out"; fail=1; continue
    fi
    if grep -q '^END STATEMENT REPORT$' "$out"; then
      report=complete
      for row in $case_rows; do
        verdict=$(sed -n "s/^statement $row [^ ]* [^ ]* \([^ ]*\) .*/\1/p" "$out")
        [ "$verdict" = "${alone[$row]}" ] \
          || { echo "case $case_: $row reads '$verdict', alone '${alone[$row]}'"; fail=1; }
      done
    else
      report=refused
      if grep -q '^statement ' "$out"; then
        echo "case $case_: a refused report printed a statement line"; report=malformed
      fi
      if ! grep -q '^STATEMENT REPORT$' "$out"; then
        echo "case $case_: a refused report has no STATEMENT REPORT line"; report=malformed
      fi
      # The positions, counted from 1, of the case's rows that read match alone.
      # The stop warning must be the last line of the output and must be this
      # whole line, so a refusal that also printed a name from the requests,
      # on that line or on a line after it, fails here.
      i=0; n=0; want=
      for row in $case_rows; do
        i=$((i + 1))
        if [ "${alone[$row]}" = match ]; then n=$((n + 1)); want=${want:+$want, }$i; fi
      done
      if ! tail -n 1 "$out" | grep -q "^Warning: Statement report stopped: User error: the $n statements that read match (requests $want) need universe constraints that are inconsistent together, so their sealings cannot all be loaded\$"; then
        echo "case $case_: the last line is not the stop warning for the $n statements that read match (requests $want)"; report=malformed
      fi
    fi

    if "$BIN"rocqchk -j "$j" -silent -Q "$d" StmtUnion "${libs[@]}" > "$w/load_$case_.log" 2>&1; then
      load=load
    elif grep -q 'Universe inconsistency' "$w/load_$case_.log"; then
      load=clash
    else
      load=error; cat "$w/load_$case_.log"
    fi
    echo "$load" > "$w/load_$case_"

    printf '%-9s %-9s %-9s %s\n' "$case_" "$expected" "$report" "$load"
    [ "$report" = "$expected" ] || fail=1
    case "$report,$load" in
      complete,load | refused,clash) ;;
      *) cat "$out"; fail=1 ;;
    esac
  done <<< "$cases"
done

# Each width must give, for each case, the report and the load result that
# -j 1 gives.
for j in $widths; do
  [ "$j" = 1 ] && continue
  while IFS='|' read -r case_ _ _; do
    if ! cmp -s "$d/w1/out_$case_" "$d/w$j/out_$case_"; then
      echo "case $case_: the report at -j $j differs from the report at -j 1"
      diff "$d/w1/out_$case_" "$d/w$j/out_$case_" || true
      fail=1
    fi
    if ! cmp -s "$d/w1/load_$case_" "$d/w$j/load_$case_"; then
      echo "case $case_: loading the sealings gives $(cat "$d/w1/load_$case_" 2> /dev/null) at -j 1 and $(cat "$d/w$j/load_$case_" 2> /dev/null) at -j $j"
      fail=1
    fi
  done <<< "$cases"
done
exit $fail
