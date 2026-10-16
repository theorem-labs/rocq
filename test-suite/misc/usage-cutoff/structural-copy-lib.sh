#!/usr/bin/env bash
# Shared protocol for dependents that copy A's structure (#841 round 22:
# Include, module alias, functor application). A0 -> A1 changes A, B copies
# the changed module, and a fresh B compiles. The stale B.vo must be refused.
# If it is reused, the fixture's interface probe (P.v / PK.v) and its C1.v,
# which uses the copied member, are compared between the stale and fresh B.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

# uc_structural_copy_refused PROBE C1_FRESH(ok|fail)
uc_structural_copy_refused() {
  local probe=${1:?probe filename} c1_fresh=${2:?ok or fail}
  local name dir work f stale_c stale_rc stale_probe stale_c1 stale_c1_rc
  local fresh_probe fresh_c1 fresh_c1_rc
  name=$(basename "$PWD")
  dir=$PWD
  work="$dir/work"
  rm -rf "$work"
  mkdir -p "$work"
  for f in "$dir"/*.v; do cp "$f" "$work"/; done
  cp "$dir"/A0.v "$work/A.v"
  build() { ( cd "$work" && uc_coqc -Q . "" "$1" ); }
  for f in X.v A.v R.v B.v; do
    [ -f "$work/$f" ] || continue
    build "$f" >>"$work/setup.log" 2>&1 || uc_fail "$name setup $f: $(cat "$work/setup.log")"
  done
  cp "$dir"/A1.v "$work/A.v"
  build A.v >"$work/after.log" 2>&1 || uc_fail "$name rebuild A1: $(cat "$work/after.log")"

  stale_c=$(build C.v 2>&1)
  stale_rc=$?
  if [ "$stale_rc" -eq 0 ]; then
    stale_probe=$(build "$probe" 2>&1)
    stale_c1=$(build C1.v 2>&1)
    stale_c1_rc=$?
  fi

  mv "$work/B.vo" "$work/B.stale.vo"
  build B.v >"$work/fresh-B.log" 2>&1 || uc_fail "$name fresh B failed: $(cat "$work/fresh-B.log")"
  fresh_probe=$(build "$probe" 2>&1) || uc_fail "$name fresh probe failed: $fresh_probe"
  fresh_c1=$(build C1.v 2>&1)
  fresh_c1_rc=$?
  if [ "$c1_fresh" = ok ]; then
    [ "$fresh_c1_rc" -eq 0 ] || uc_fail "$name fresh C1 failed: $fresh_c1"
  else
    [ "$fresh_c1_rc" -ne 0 ] || uc_fail "$name fresh C1 unexpectedly succeeded: $fresh_c1"
  fi

  if [ "$stale_rc" -eq 0 ]; then
    uc_fail "$name reused a stale B that copies A: probe stale=[$stale_probe] fresh=[$fresh_probe]; C1 stale rc=$stale_c1_rc [$stale_c1] fresh rc=$fresh_c1_rc [$fresh_c1]"
  fi
  printf %s "$stale_c" | grep -qi inconsistent \
    || uc_fail "$name refused stale B for the wrong reason: $stale_c"
  uc_ok "$name correctly refused a stale B that copies A; fresh C1 rc=$fresh_c1_rc"
}
