#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 G1, test "g1_admitted_to_qed_reused"
# (new, item 18). Depends on: G1 (the objects-digest partition that excludes
# CONSTANT/INDUCTIVE's cst_kind from the exact-equality check).
#
# A has `Lemma p : t. Admitted.` plus `Definition g := I1.`; B requires A and
# uses only `g` (never `p`). A's `p` goes Admitted -> Qed. Before G1, this
# was REFUSED (cst_kind inside the CONSTANT libobject changed the exact
# objects digest) -- defeating the lever's entire stated purpose. After G1,
# B.vo must be REUSED, bit-for-bit unchanged.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D/B.v" "$WORK/"

build() { ( cd "$WORK" && uc_coqc -Q . T "$1" ); }

cp "$D/A_admitted.v" "$WORK/A.v"
cp "$D/C.v" "$WORK/"
build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, Admitted): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"

before_hash=$(uc_sha256 "$WORK/B.vo")

# AFTER: A's p goes Admitted -> Qed. Rebuild A ONLY.
cp "$D/A_qed.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, Qed) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if ! out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C (requiring B) was refused after an Admitted->Qed edit to an UNUSED declaration in A -- G1's whole point is this must be reused, not refused."
fi

after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C -- B was silently recompiled rather than genuinely reused."

uc_same_interface "$WORK" "g1_admitted_to_qed_reused" T
uc_ok "B.vo reused unchanged (sha256 $after_hash) after compiling C, across A's Admitted->Qed edit: $(echo "$out" | tail -1)"
