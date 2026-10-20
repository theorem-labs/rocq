#!/usr/bin/env bash
# ROCQ_DEBUG_ASSUMPTIONS_MEMO=1 reports each reuse of a Print Assumptions
# traversal, and each clearing of the entries by the weight bound, on
# standard error, and only there: standard output is the same with the
# variable set or unset, Set Debug "all,-misc" included.
#
# Each file's expected list of reuses (<file>.err) pins which objects are
# reused, so it also pins the cases the reuse leaves out:
# - Debug.v: when the environment changes;
# - Opaque.v: walks that meet a Qed body that cannot be read (-vok against
#   Lib's .vos);
# - Canon.v: entries recorded under another canonical name;
# - Thrash.v, ThrashBlock.v: an object, or an inductive block, whose user
#   name already has an entry under another canonical name is not recorded,
#   so the entry is not replaced;
# - Bound.v: entries that weigh more than twice the heaviest query are
#   cleared before the next query; its clearings sit at the boundary, so the
#   list also pins how recorded objects, replays and blocks are weighed.

set -e

export PATH=$BIN:$PATH

cd misc/print-assumptions-memo
rm -rf _test
mkdir _test
cp Debug.v Debug.err Lib.v Opaque.v Opaque.err Canon.v Canon.err Thrash.v Thrash.err ThrashBlock.v ThrashBlock.err \
  Bound.v Bound.err _test
cd _test

rocq c -q -R . Memo -vos Lib.v

check() {
  local f=$1; shift
  rocq c -q -R . Memo "$@" "$f.v" > "$f.plain.out" 2> "$f.plain.err"
  ROCQ_DEBUG_ASSUMPTIONS_MEMO=1 rocq c -q -R . Memo "$@" "$f.v" > "$f.debug.out" 2> "$f.debug.err"
  diff -u --strip-trailing-cr "$f.err" "$f.debug.err"
  diff -u "$f.plain.out" "$f.debug.out"
  diff -u /dev/null "$f.plain.err"
}

check Debug
check Opaque -vok
check Canon
check Thrash
check ThrashBlock
check Bound
