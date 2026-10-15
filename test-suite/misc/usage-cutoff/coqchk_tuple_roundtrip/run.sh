#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "coqchk_tuple_roundtrip" (issue list
# item 15 of 15). Depends on: D1's widened dependency tuple
# (DirPath.t * vodigest * iface_table option * Digest.t) being handled
# CONSISTENTLY by every independently-maintained declaration of that same
# shape across kernel/safe_typing.ml, vernac/library.ml,
# checker/checkLibrary.ml and checker/values.ml's validator schema (plus
# commit 1's Dvo_iface once it lands) -- BugFinderRedTeamV2 Blocker B1.
# EXPECTED TO FAIL until commit comp_transitive_deps/Dvo_iface lands.
#
# A same-arity, different-field-ORDER mistake in any one of those
# declarations is invisible to OCaml's type checker (tuple arity alone
# doesn't catch reordering) and would corrupt exactly the kind of tree this
# test builds: A exports THREE distinguishable declarations (v1=111,
# v2=222, v3=333) plus a non-trivial exported Hint, so its iface_table and
# objects_digest are genuinely non-degenerate (not "zero or one entry,
# every field incidentally the same"); three separate dependents (B, C, D)
# each use exactly one. A degenerate test (a single-entry table, as in
# most of this suite's other cases) could pass even with fields silently
# swapped; this one can't, because a swap would make at least one of
# check1/check2/check3 below come out wrong.
#
# Assertion: `rocqchk -norec` over the whole tree accepts it (no crash, no
# corrupted-validation anomaly), AND the three checked values round-trip
# distinctly and correctly -- not merely "accept/reject", per #841's own
# framing of this test.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/A.v "$D"/B.v "$D"/C.v "$D"/D.v "$D"/Consumer.v "$WORK"/

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

for f in A B C D Consumer; do
  build "$f.v" >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build $f.v: $(cat "$WORK/setup.log")"
done

chk_out=$(cd "$WORK" && "$UC_ROCQCHK" -o -Q . "" -norec A -norec B -norec C -norec D -norec Consumer 2>&1)
chk_rc=$?
if [ "$chk_rc" -ne 0 ]; then
  echo "$chk_out" >&2
  uc_fail "rocqchk rejected (or crashed on, exit $chk_rc) a well-typed tree with a non-degenerate dependency tuple (multi-entry iface_table, non-empty objects_digest) -- a same-arity/different-order tuple mismatch is exactly what this looks like."
fi

values_out=$(cd "$WORK" && printf 'Eval compute in check1.\nEval compute in check2.\nEval compute in check3.\n' \
  | "$COQBIN"rocq repl -batch -Q . "" -require-import Consumer 2>&1)
for pair in "check1:111" "check2:222" "check3:333"; do
  name=${pair%%:*}; expected=${pair##*:}
  echo "$values_out" | grep -q "= $expected" \
    || uc_fail "$name did not round-trip to the expected distinct value $expected -- fields may have been silently swapped/aliased. Full output: $values_out"
done

uc_ok "rocqchk accepted the non-degenerate tree, and check1/check2/check3 round-tripped distinctly to 111/222/333."
