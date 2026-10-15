#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "two_level_false" (issue list item 1
# of 15). Depends on: D1 (comp_transitive_deps / the full transitive-closure
# fix). EXPECTED TO FAIL until commit comp_transitive_deps/Dvo_iface lands
# -- on today's tree (D1 absent) the relaxed loader accepts this exploit, as
# it did in v1.
#
# rocq#10's code-quality review, Blocker 1, reproduced verbatim: X declares
# f; A re-exports X without declaring f itself; B requires only A (never X
# directly) and proves `b : f = 1`. A's own per-declaration interface table
# covers only A's OWN top-level declarations (here just `g`), so it never
# notices that f -- visible through A only by re-export -- has changed.
# When X changes and A is rebuilt (but B.vo is left on disk, untouched),
# the relaxed loader lets a fresh compile of C exploit the stale B.vo: a
# closed proof of False, discriminated from `2 = 1 := b`, with zero axioms.
#
# Assertion: compiling C against the stale B.vo MUST be refused once D1
# lands ("Inconsistent assumptions over module ... X"), not merely print a
# mismatch and exit 0 regardless (the exact anti-pattern rocq#10 Major-6 /
# #841 finding 6 flagged in v1's own verification scripts).
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

# BEFORE: f := 1 everywhere. Build the whole chain.
build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v (BEFORE): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"

# AFTER: f := 2. Rebuild X and A ONLY -- B.vo is left stale on disk, exactly
# as in the reviewer's own driver-routed repro log ("REBUILD X;
# REBUILD-REFUSED A; REBUILD A; REUSED B").
printf 'Definition f := 2.\n' > "$WORK/X.v"
build X.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD X (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# The exploit: compile C fresh against the stale B.vo (B.v/B.vo untouched
# since the BEFORE build).
if out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C compiled against the stale B.vo after a 2-level-down change to f -- this is the Blocker (closed proof of False with no axioms)."
fi
uc_ok "C was refused against the stale B.vo: $(echo "$out" | tail -1)"
