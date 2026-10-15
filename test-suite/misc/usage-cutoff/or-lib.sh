#!/usr/bin/env bash
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

uc_unrelated_root() {
  local name=$(basename "$PWD")
  local dir=$PWD
  local work="$dir/work"
  mkdir -p "$work"
  cp "$dir"/X.v "$dir"/Z.v "$dir"/B.v "$dir"/C.v "$work"/
  cp "$dir/A0.v" "$work/A.v"
  build() { ( cd "$work" && uc_coqc -Q . "" "$1" ); }
  build X.v >"$work/setup.log" 2>&1 || uc_fail "$name setup X"
  build Z.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup Z"
  build A.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup A0"
  build B.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup B"
  build C.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup C"
  cp "$dir/A1.v" "$work/A.v"
  build A.v >"$work/rebuild.log" 2>&1 || uc_fail "$name rebuild A1"
  cp "$dir/B.v" "$work/B_fresh_check.v"
  fresh_out=$(cd "$work" && uc_coqc -Q . "" B_fresh_check.v 2>&1); fresh_rc=$?
  [ "$fresh_rc" -eq 0 ] || uc_fail "$name fresh B unexpectedly failed: $fresh_out"
  c_out=$(build C.v 2>&1); c_rc=$?
  [ "$c_rc" -eq 0 ] || uc_fail "$name refused an unrelated root: $c_out"
  uc_ok "$name correctly reused"
}
