#!/usr/bin/env bash
# Print Assumptions reuses traversals while the environment, the current
# module, the opaque-proof accessor and the opaque proofs of the loaded
# libraries stay the same. Four shapes ask what a query must answer to change
# under a name that was queried before, and are not covered by
# print-assumptions-memo-opaque-table.sh, which covers a reloaded library:
#
# - Reset:   a constant redefined under its own name after Reset;
# - Shadow:  the same short names in two modules, queried through Import,
#            which moves a short name to another object without adding
#            anything to the environment;
# - Close:   queries across a module close (a sealed module answers with the
#            axioms of its body while it is open, and with itself once it is
#            closed) and across a section close (its constants are discharged
#            under the names they had inside it);
# - Functor: a module type with parameters, a functor over it applied twice to
#            declared parameters, and queries on constants of both
#            applications in one session, with a third application of the
#            first argument.
#
# Each case is compiled twice, from the same bytes, in two directories that
# give the file the same name, so a message that names it reads the same in
# both:
#
# - cache/   as written: each query reuses what the queries before it
#            recorded;
# - noreuse/ with a definition of its own before each query, which changes
#            the environment and clears the entries, so every query is a walk
#            without reuse. The definitions print nothing and are named apart
#            from everything the case names; each takes the place of the
#            (*NOREUSE*) mark on its query's line, so every line and every
#            other column stays where it was.
#
# The two arms must print the same bytes, and the same bytes as <case>.out,
# which holds the output of Rocq without the cache. The reuse the debug
# variable reports shows the arms are what they claim: without a replay in
# the cache arm, and none in the control, the comparison would hold whatever
# the entries did.

set -e

export PATH=$BIN:$PATH
export LC_ALL=C

cases="Reset Shadow Close Functor"

cd misc/print-assumptions-memo-stale
rm -rf _test
mkdir -p _test/cache _test/noreuse

for f in $cases; do
  cp "$f.v" "_test/cache/$f.v"
  awk '/\(\*NOREUSE\*\)/ { n++; sub(/\(\*NOREUSE\*\)/, "Definition no_reuse_" n " := 0.") } { print }' \
    "$f.v" > "_test/noreuse/$f.v"
done

cd _test
status=0

for f in $cases; do
  for arm in cache noreuse; do
    (
      cd $arm
      rocq c -q -R . Stale "$f.v" > "$f.plain.out" 2> "$f.plain.err"
      ROCQ_DEBUG_ASSUMPTIONS_MEMO=1 rocq c -q -R . Stale "$f.v" > "$f.debug.out" 2> "$f.debug.err"
    )
  done
  diff -u "noreuse/$f.plain.out" "cache/$f.plain.out"
  diff -u "../$f.out" "cache/$f.plain.out"
  diff -u /dev/null "cache/$f.plain.err"
  diff -u /dev/null "noreuse/$f.plain.err"
  diff -u "cache/$f.plain.out" "cache/$f.debug.out"
  diff -u "noreuse/$f.plain.out" "noreuse/$f.debug.out"
  for arm in cache noreuse; do
    grep -v '^\[assumptions-memo\] ' "$arm/$f.debug.err" > "$arm/$f.debug.other.err" || true
    diff -u /dev/null "$arm/$f.debug.other.err"
  done
  replays=$(grep -c '^\[assumptions-memo\] replayed' "cache/$f.debug.err" || true)
  control=$(grep -c '^\[assumptions-memo\] replayed' "noreuse/$f.debug.err" || true)
  echo "$f: $replays replays, $control in the control"
  if [ "$replays" -lt 1 ]; then
    echo "$f: the cache arm reused nothing, so the case tests no reuse"
    status=1
  fi
  if [ "$control" -ne 0 ]; then
    echo "$f: the control reused $control walks, so it is not a walk without reuse"
    status=1
  fi
done

exit $status
