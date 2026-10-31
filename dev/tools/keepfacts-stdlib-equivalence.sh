#!/usr/bin/env bash
# The keepfacts closures of a whole Stdlib build, computed over the
# dependencies' stored closures and by every root's own walk
# (ROCQ_KEEPFACTS_FULL_WALK=1), must be equal, and what each costs
# (vernac/keepFacts.ml; design D18, dispatch://INFRA-361).
#
# Usage: dev/tools/keepfacts-stdlib-equivalence.sh PREFIX STDLIB_SRC OUT [LABEL_PREFIX]
#   PREFIX        the install prefix of a build of this tree (bin/rocq,
#                 bin/rocq-library-label, lib/), e.g. from
#                 ./configure -prefix PREFIX && make dunestrap &&
#                 dune build -p rocq-runtime,coq-core,rocq-core @install &&
#                 dune install -p rocq-runtime,coq-core,rocq-core --prefix=PREFIX
#   STDLIB_SRC    the rocq-stdlib sources (a dune project); each arm builds a fresh copy
#   OUT           where the logs, timings and results go (emptied first)
#   LABEL_PREFIX  optional: the prefix of a build to time with -location-free-label but
#                 no keepfacts (the label's cost alone)
# Environment: JOBS (dune -j, default 16); REPEAT=1 builds the off and fast arms twice.
#
# Arms, each `dune build -p rocq-stdlib @install` of a fresh copy, timed with
# /usr/bin/time: off (PREFIX, no flag), label (LABEL_PREFIX, -location-free-label),
# fast (PREFIX, -location-free-label, ROCQ_KEEPFACTS_DEBUG=1), full (PREFIX,
# -location-free-label, ROCQ_KEEPFACTS_FULL_WALK=1). The flag is added by a wrapper
# rocq first on PATH. Then every .vo of the fast and full arms is read with
# rocq-library-label --axiom-report-json and the two documents compared.
# OUT/equivalence.txt: ".vo files, identical, different, full-arm files with closures".
# Exit 0 when every document is identical and every full-arm file carries closures,
# 1 otherwise, 2 on a usage or build error.
set -uo pipefail
[ $# -ge 3 ] || { sed -n '7,18p' "$0"; exit 2; }
P=$(cd "$1" && pwd) SRC=$(cd "$2" && pwd) O=$3 LP=${4:+$(cd "$4" && pwd)}
J=${JOBS:-16}
rm -rf "$O"; mkdir -p "$O"; O=$(cd "$O" && pwd)
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
unset ROCQLIB COQLIB BASH_ENV
export DUNE_CACHE=disabled

# shim DIR PREFIX ENV...: a rocq (and coqc) adding -location-free-label to every compile.
shim() {
  local d=$1 p=$2 e; shift 2
  mkdir -p "$d"
  { echo '#!/usr/bin/env bash'; for e in "$@"; do echo "export $e"; done
    echo "case \"\$1\" in c|compile) sub=\$1; shift; exec $p/bin/rocq \"\$sub\" -location-free-label \"\$@\";; esac"
    echo "exec $p/bin/rocq \"\$@\""; } > "$d/rocq"
  printf '#!/usr/bin/env bash\nexec %s/rocq compile "$@"\n' "$d" > "$d/coqc"
  chmod +x "$d/rocq" "$d/coqc"
}
shim "$W/shim-fast" "$P" ROCQ_KEEPFACTS_DEBUG=1
shim "$W/shim-full" "$P" ROCQ_KEEPFACTS_FULL_WALK=1
[ -z "$LP" ] || shim "$W/shim-label" "$LP"

arms="off fast full"
[ -z "$LP" ] || arms="off label fast full"
[ "${REPEAT:-0}" != 1 ] || arms="$arms fast2 off2"
for arm in $arms; do
  d=$W/stdlib-$arm; cp -r "$SRC" "$d"
  case $arm in
    off*) path=$P/bin; prefix=$P;;
    label) path=$W/shim-label:$LP/bin; prefix=$LP;;
    fast*) path=$W/shim-fast:$P/bin; prefix=$P;;
    full) path=$W/shim-full:$P/bin; prefix=$P;;
  esac
  ( cd "$d" && PATH=$path:$PATH OCAMLPATH=$prefix/lib${OCAMLPATH:+:$OCAMLPATH} \
      /usr/bin/time -f "$arm wall %e s user %U s sys %S s maxrss %M KB" -o "$O/time-$arm.txt" \
      dune build -p rocq-stdlib -j "$J" @install ) > "$O/build-$arm.log" 2>&1 \
    || { echo "arm $arm failed:"; tail -30 "$O/build-$arm.log"; exit 2; }
  cat "$O/time-$arm.txt"
  (cd "$d" && find _build/default -name '*.vo' -printf '%s %P\n' | sort -k2) > "$O/sizes-$arm.txt"
done
for a in $arms; do awk -v a="$a" '{s+=$1;n++} END {printf "%s: %d .vo files, %d bytes\n",a,n,s}' "$O/sizes-$a.txt"; done \
  | tee "$O/sizes.txt"

echo "=== how the fast arm computed each library's closures (ROCQ_KEEPFACTS_DEBUG=1)"
grep -h '^\[keepfacts\]' "$O/build-fast.log" | sort -u > "$O/fast-debug.txt"
echo "one walk over stored closures: $(grep -c 'one walk of' "$O/fast-debug.txt") libraries;" \
  "each root by its own walk: $(grep -c 'each by its own walk' "$O/fast-debug.txt")"
grep 'each by its own walk' "$O/fast-debug.txt" | sed 's/.*own walk (\(.*\))$/\1/' | sort | uniq -c
awk '/one walk of/ {r+=$3; o+=$8; s+=$10} END {printf "totals over the one-walk libraries: %d roots, %d objects walked, %d foreign stored closures used\n", r, o, s}' "$O/fast-debug.txt"

echo "=== equivalence: fast vs full, every .vo's --axiom-report-json"
n=0 same=0 differ=0 present=0
while IFS= read -r v; do
  a=$("$P/bin/rocq-library-label" --axiom-report-json "$W/stdlib-fast/_build/default/$v" 2>&1)
  b=$("$P/bin/rocq-library-label" --axiom-report-json "$W/stdlib-full/_build/default/$v" 2>&1)
  n=$((n+1)); grep -q '"assumptions":{' <<< "$b" && present=$((present+1))
  if [ "$a" = "$b" ]; then same=$((same+1))
  else differ=$((differ+1)); echo "DIFF $v"
    [ $differ -le 10 ] && diff <(sed 's/\],"/],\n"/g' <<< "$a") <(sed 's/\],"/],\n"/g' <<< "$b") | head -40
  fi
done < <(cd "$W/stdlib-full/_build/default" && find . -name '*.vo' | sort)
echo "equivalence: $n .vo files, $same identical documents, $differ different; $present of the full arm's carry closures"
echo "$n $same $differ $present" > "$O/equivalence.txt"
[ "$n" -gt 0 ] && [ "$differ" = 0 ] && [ "$present" = "$n" ]
