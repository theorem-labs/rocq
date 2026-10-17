#!/usr/bin/env bash
# Shared protocol for the round-23 adversarial-review fixtures
# (binary-equivalence-taiga#841, /mnt/nvme/sami/cutoff2/adv-r23/*.md).
# Logical prefix T. Every name in SETUP is compiled first, then A (from
# A0.v), B and C. A is then replaced by A1.v and rebuilt alone, and C is
# compiled against the kept B.vo: it must be REFUSED. The case must also be
# a real hazard: against a fresh B, the fresh B compile, the fresh C
# compile or the Probe output must differ from the initial build.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

# uc_adv_refused SETUP...
uc_adv_refused() {
  local name dir work f
  name=$(basename "$PWD"); dir=$PWD; work="$dir/work"
  rm -rf "$work"; mkdir -p "$work"
  cp "$dir"/*.v "$work"/
  cp "$dir/A0.v" "$work/A.v"
  build() { ( cd "$work" && uc_coqc -q -Q . T "$1" ); }
  for f in "$@" A.v B.v C.v; do
    build "$f" >>"$work/setup.log" 2>&1 || uc_fail "$name setup $f: $(cat "$work/setup.log")"
  done
  local probe_initial=""
  [ -f "$work/Probe.v" ] && probe_initial=$(build Probe.v 2>&1)
  cp "$dir/A1.v" "$work/A.v"
  build A.v >"$work/rebuild.log" 2>&1 || uc_fail "$name rebuild A: $(cat "$work/rebuild.log")"

  local kept kept_rc
  kept=$(build C.v 2>&1); kept_rc=$?

  mv "$work/B.vo" "$work/B.kept.vo"
  local fb fb_rc fc fc_rc=0 probe_fresh=""
  fb=$(build B.v 2>&1); fb_rc=$?
  if [ "$fb_rc" -eq 0 ]; then
    fc=$(build C.v 2>&1); fc_rc=$?
    [ -f "$work/Probe.v" ] && probe_fresh=$(build Probe.v 2>&1)
  fi
  if [ "$fb_rc" -eq 0 ] && [ "$fc_rc" -eq 0 ] && [ "$probe_initial" = "$probe_fresh" ]; then
    uc_fail "$name SANITY: a fresh B, C and Probe behave like the initial build, so the case exercises no hazard"
  fi
  [ "$kept_rc" -ne 0 ] || uc_fail "$name reused the stale B.vo although a fresh build differs: fresh B rc=$fb_rc C rc=$fc_rc"
  printf %s "$kept" | grep -qi 'inconsistent assumptions' \
    || uc_fail "$name refused for the wrong reason: $kept"
  uc_ok "$name correctly refused the stale B.vo (fresh B rc=$fb_rc, fresh C rc=$fc_rc)"
}
