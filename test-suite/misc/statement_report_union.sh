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
# the union before it prints the first statement.
# A case marked [diverges] is a known exception to "complete exactly when
# they load": see cp_bc below.
set -eu

D=misc/statement_report_union
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Defs.v" "$d/"

$coqc -noinit -Q "$d" StmtUnion "$d/Defs.v"

# <row>|<model>|<verdict alone>|<sealing alone>
rows='ab|m_a|match|accepted
bc|m_b|match|accepted
part|m_part|universes-differ|refused
p_a|m_poly|match|accepted
p_c|m_poly|match|accepted
p_ab|m_poly|match|accepted
cp|m_cpoly|universes-undecided|accepted'

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
# cp: [cp] reads universes-undecided, and coqc accepts its sealing alone,
#   which then loads: the report is complete.
# cp_bc: KNOWN DIVERGENCE. This case pins the current output; it does not
#   say the output is correct. coqc accepts [cp]'s sealing alone and [bc]'s
#   alone, and rocqchk refuses to load the two together: [cp]'s [a < b] and
#   [bc]'s [b <= c] contradict [c < a]. The report is still complete, [cp]
#   reading universes-undecided and [bc] match, because only the statements
#   that read match are in the check. A reader that pays [bc] on this report
#   pays what a check loading every sealing refuses. The Lean grade's V9b
#   fallback closes it: when a statement reads universes-undecided, it
#   compiles every sealing and loads them all together.
# <case>|<rows, in request order>|<expected report>|[diverges]
cases='ab|ab|complete
bc|bc|complete
ab_bc|ab bc|refused
bc_ab|bc ab|refused
ab_part|ab part|complete
p_a_p_c|p_a p_c|complete
p_ab_bc|p_ab bc|refused
ab_part_bc|ab part bc|refused
cp|cp|complete
cp_bc|cp bc|complete|diverges'

declare -A model alone sealing
fail=0

while IFS='|' read -r row m expected seal; do
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
  # The sealing's result is pinned also where the verdict allows either.
  [ "${sealing[$row]}" = "$seal" ] \
    || { echo "row $row: sealing alone ${sealing[$row]}, expected $seal"; fail=1; }
  case "${alone[$row]},${sealing[$row]}" in
    match,accepted | universes-differ,refused) ;;
    universes-undecided,accepted | universes-undecided,refused) ;;
    *) echo "row $row: verdict alone ${alone[$row]}, sealing alone ${sealing[$row]}"; fail=1 ;;
  esac
done <<< "$rows"

printf '%-9s %-9s %-9s %s\n' case expected report 'sealings together'
while IFS='|' read -r case_ case_rows expected known; do
  : > "$d/req_$case_"
  libs=()
  for row in $case_rows; do
    printf '%s StmtUnion.Defs.%s StmtUnion.Defs.t_%s\n' "$row" "${model[$row]}" "$row" >> "$d/req_$case_"
    if [ "${sealing[$row]}" = accepted ]; then libs+=("StmtUnion.Seal_$row"); fi
  done

  out=$d/out_$case_
  if ! "$BIN"rocqchk -silent -statement-report "$d/req_$case_" -Q "$d" StmtUnion StmtUnion.Defs \
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

  if "$BIN"rocqchk -silent -Q "$d" StmtUnion "${libs[@]}" > "$d/load_$case_.log" 2>&1; then
    load=load
  elif grep -q 'Universe inconsistency' "$d/load_$case_.log"; then
    load=clash
  else
    load=error; cat "$d/load_$case_.log"
  fi

  printf '%-9s %-9s %-9s %s%s\n' "$case_" "$expected" "$report" "$load" "${known:+ ($known)}"
  [ "$report" = "$expected" ] || fail=1
  case "$report,$load,$known" in
    complete,load, | refused,clash, | complete,clash,diverges) ;;
    *) cat "$out"; fail=1 ;;
  esac
done <<< "$cases"
exit $fail
