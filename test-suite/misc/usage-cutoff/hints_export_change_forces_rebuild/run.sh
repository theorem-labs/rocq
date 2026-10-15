#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test
# "hints_export_change_forces_rebuild" (issue list item 7 of 15). Depends
# on: D4 (the exported-object digest covering Hints/Instances/Notations/
# Ltac2/Canonical Structures). Should PASS once D4 lands.
#
# rocq#10's deep review, Major M4, reproduced: A declares P and an
# `#[export] Hint Constructors P`; B proves `b : P` via `auto` using
# exactly that hint. The hint is then removed from A (A rebuilt, B.v/B.vo
# untouched). Hints/Instances/Notations live in Declaremods.library_objects
# (`md_objects`/`md_syntax_objects`), which the kernel's own per-declaration
# interface table never sees (it only ever walks SFBconst/SFBmind) -- so
# before D4, nothing notices the hint vanished, and a dependent whose own
# *compiled proof term* no longer depends on the hint (auto already baked
# `mkP` into B.vo's term at B's own compile time) would be "reused" by the
# interactive loader. That's a misleading LOCAL green signal: a genuinely
# FRESH build of B.v (as the grader's own from-scratch build always does)
# fails, because `auto with hintcutoff` can no longer find a solution.
#
# Assertion: once D4 lands, the stale B.vo MUST be refused for reuse (its
# dependent's own exported-object digest for A no longer matches A's
# current table) -- so a tree that pulls in B.vo via Require against the
# new A forces a REAL rebuild attempt of B.v, which correctly reports the
# actual error state (not a silently-reused but now provably misleading
# green).
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D/B.v" "$WORK/B.v"
cp "$D/A_with_hint.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, with hint): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, via auto with hintcutoff): $(cat "$WORK/setup.log")"

# AFTER: the hint is removed from A. Rebuild A ONLY -- B.v/B.vo untouched.
cp "$D/A_no_hint.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, hint removed) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# (1) A dependent pulling in the stale B.vo against the new A must be
# refused for reuse, not silently accepted.
printf 'Require Import B.\n' > "$WORK/scratch.v"
if out=$(build scratch.v 2>&1); then
  uc_fail "a fresh Require of B succeeded against the stale B.vo after A's exported Hint changed -- D4's objects-digest check did not fire."
fi

# (2) Confirm the refusal in (1) is the CORRECT direction: an actual fresh
# recompile of B.v against the new A really does fail (so this isn't an
# over-eager rejection of something that's actually still fine).
rm -f "$WORK/B.vo" "$WORK/B.glob" "$WORK/B.vo.cutoff-stamp"
if fresh_out=$(build B.v 2>&1); then
  uc_fail "a fresh compile of B.v succeeded even without A's Hint -- the fixture doesn't actually exercise the hint (test is broken), or Hint Constructors is not required for auto here."
fi
echo "$fresh_out" | grep -qi -E 'auto|unable|no applicable tactic' \
  || uc_fail "fresh B.v compile failed, but not with the expected 'auto'/'unable to find' error; got: $fresh_out"

uc_ok "stale B.vo was refused ($(echo "$out" | tail -1)), and a fresh B.v build genuinely fails without the hint ($(echo "$fresh_out" | tail -1))."
