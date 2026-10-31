#!/usr/bin/env bash

# rocqchk -statement-report's type verdict is the sealing it stands for: for
# each row, [Definition f := <model>] ([Polymorphic] for a polymorphic
# statement), the spelling a grader's checker uses, is compiled by coqc in a
# module sealed by the row's module type. [match] must be accepted, and
# [mismatch] and [universes-differ] refused. [universes-undecided] is the
# verdict for a model whose universe context elaboration can minimize: the
# report does not compare its type, so the sealing may accept or refuse it,
# and the verdict is never [match] for it. A row marked [elab] records one
# measured form where the two sides part for a reason the verdict does not
# cover: the model has the statement's type, so the verdict is [match], and
# the bare alias written here does not elaborate because a maximal implicit
# argument stays unresolved. Implicit arguments are elaboration data, not
# kernel data; whether such an alias elaborates depends on where it is
# written, and a sealing whose module type gives the expected type can
# resolve it.
set -eu

D=misc/statement_report_sealing
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Defs.v" "$d/"

$coqc -noinit -Q "$d" StmtSeal "$d/Defs.v"

# <row>|<model>|<expected verdict>|<expected sealing>|[Polymorphic]|[elab]
rows='same|m_same|match|accepted||
set_type|m_set|match|accepted||
prop_type|m_prop|match|accepted||
indep|m_indep|match|accepted||
incons|m_incons|universes-differ|refused||
qsort|m_qsort|match|accepted||
qsort_lt|m_qsort_lt|universes-differ|refused||
alg|m_alg|universes-differ|refused||
poly_mono|m_poly|match|accepted||
poly_set|m_poly|universes-differ|refused||
poly_mono_lt|m_poly_lt|universes-undecided|refused||
poly_mono_le|m_two|universes-undecided|refused||
poly_poly|m_poly|match|accepted|Polymorphic|
poly_lt|m_poly_lt|universes-undecided|refused|Polymorphic|
poly_strong|m_poly_le|universes-undecided|refused|Polymorphic|
poly_le_le|m_poly_le|universes-undecided|refused|Polymorphic|
poly_univ|m_poly_univ|universes-differ|refused|Polymorphic|
poly_sort|m_poly_sort|universes-undecided|refused|Polymorphic|
poly_ctx|m_poly|universes-differ|refused|Polymorphic|
mono_poly|m_set|match|accepted|Polymorphic|
implicit|m_implicit|match|refused|Polymorphic|elab
different|m_fun|mismatch|refused||
binder|m_binder|mismatch|refused||
poly_different|m_fun|mismatch|refused|Polymorphic|'

: > "$d/requests"
while IFS='|' read -r row model expected seal poly elab; do
  printf '%s StmtSeal.Defs.%s StmtSeal.Defs.t_%s\n' "$row" "$model" "$row" >> "$d/requests"
  printf 'Require StmtSeal.Defs.\nModule X <: StmtSeal.Defs.S_%s.\n  %sDefinition f := StmtSeal.Defs.%s.\nEnd X.\n' \
    "$row" "${poly:+$poly }" "$model" > "$d/Seal_$row.v"
done <<< "$rows"

"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" StmtSeal StmtSeal.Defs > "$d/out" 2>&1 \
  || { cat "$d/out"; exit 1; }
sed -n 's/^statement \([^ ]*\) [^ ]* [^ ]* \([^ ]*\) .*/\1 \2/p' "$d/out" > "$d/verdicts"

# Sealing is refused by a signature mismatch, or by the anomaly that the
# elaborator's universe inference raises when it must make an algebraic
# universe equal to a level (engine/univSubst.ml's [enforce_eq]).
fail=0
printf '%-14s %-19s %-19s %s\n' row expected report sealing
while IFS='|' read -r row model expected seal poly elab; do
  verdict=$(sed -n "s/^$row //p" "$d/verdicts")
  if $coqc -noinit -Q "$d" StmtSeal "$d/Seal_$row.v" < /dev/null > "$d/seal_$row.log" 2>&1; then
    sealing=accepted
  elif grep -q -e 'Signature components for field f do not match' \
         -e 'A universe comparison can only happen between variables' \
         -e 'The following term contains unresolved implicit arguments' "$d/seal_$row.log"; then
    sealing=refused
  else
    sealing=error; cat "$d/seal_$row.log"
  fi
  printf '%-14s %-19s %-19s %s%s\n' "$row" "$expected" "$verdict" "$sealing" "${elab:+ ($elab)}"
  [ "$verdict" = "$expected" ] || fail=1
  # The sealing's result is pinned also where the verdict allows either.
  [ "$sealing" = "$seal" ] || { echo "row $row: sealing $sealing, expected $seal"; fail=1; }
  # Every row's pins must be one of these pairs: a row cannot pin a [match]
  # that its sealing refuses unless it is marked [elab].
  case "$verdict,$sealing,$elab" in
    match,accepted, | mismatch,refused, | universes-differ,refused,) ;;
    universes-undecided,accepted, | universes-undecided,refused,) ;;
    match,refused,elab) ;;
    *) echo "row $row: verdict $verdict with sealing $sealing${elab:+ ($elab)} is not allowed"; fail=1 ;;
  esac
done <<< "$rows"
exit $fail
