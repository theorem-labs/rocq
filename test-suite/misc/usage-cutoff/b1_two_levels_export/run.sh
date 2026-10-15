#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "b1_two_levels_export" (issue list
# item 2 of 15). Depends on: D1 (comp_transitive_deps / the full
# transitive-closure fix). EXPECTED TO FAIL until commit
# comp_transitive_deps/Dvo_iface lands.
#
# rocq#10's deep review, Blocker B1, reproduced in both of its stated
# forms: Z declares z; A either re-exports Z (export variant) or merely
# imports it and copies its value into A's OWN declaration `d := z`
# (noexport variant, proving the bug doesn't need `Require Export` at all);
# Bf requires only A and proves `b : <z-or-d> = 1`. When Z changes and A is
# rebuilt (Bf.vo left stale), a fresh compile of Cf exploits the stale
# Bf.vo for a closed proof of False via `discriminate`.
#
# Assertion: compiling Cf against the stale Bf.vo MUST be refused, in BOTH
# variants, once D1 lands.
. ../lib.sh

D=$(pwd)

run_variant() {
  local variant=$1
  local WORK="$D/work-$variant"
  rm -rf "$WORK"
  mkdir -p "$WORK"
  cp "$D/Z.v" "$WORK/Z.v"
  cp "$D/A_$variant.v" "$WORK/A_$variant.v"
  cp "$D/Bf_$variant.v" "$WORK/Bf_$variant.v"
  cp "$D/Cf_$variant.v" "$WORK/Cf_$variant.v"

  build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

  build Z.v >"$WORK/setup.log" 2>&1 || uc_fail "[$variant] SETUP: could not build Z.v (BEFORE): $(cat "$WORK/setup.log")"
  build "A_$variant.v" >>"$WORK/setup.log" 2>&1 || uc_fail "[$variant] SETUP: could not build A_$variant.v (BEFORE): $(cat "$WORK/setup.log")"
  build "Bf_$variant.v" >>"$WORK/setup.log" 2>&1 || uc_fail "[$variant] SETUP: could not build Bf_$variant.v (BEFORE): $(cat "$WORK/setup.log")"

  # AFTER: z := 2. Rebuild Z and A ONLY -- Bf's .vo is left stale on disk.
  printf 'Definition z := 2.\n' > "$WORK/Z.v"
  build Z.v >"$WORK/rebuild.log" 2>&1 || uc_fail "[$variant] REBUILD Z (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"
  build "A_$variant.v" >>"$WORK/rebuild.log" 2>&1 || uc_fail "[$variant] REBUILD A_$variant (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"

  if out=$(build "Cf_$variant.v" 2>&1); then
    echo "$out" >&2
    uc_fail "[$variant] Cf compiled against the stale Bf.vo after a 2-level-down change to z -- closed proof of False with no axioms."
  fi
  uc_ok "[$variant] Cf was refused against the stale Bf.vo: $(echo "$out" | tail -1)"
}

run_variant export
run_variant noexport
