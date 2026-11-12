#!/usr/bin/env bash
# Grade-mode forge check for one forge directory.
#
# Usage: forge-check.sh <forge dir> <reverted install root> <base install root>
#
# An install root is <tree>/_build/install/default. The reverted tree has the
# forge's unfix.patch applied, so its checker still has the bug.
#
# Both Control.v and Forge.v are compiled with the reverted coqc. The check
# passes when the reverted checker accepts both files (so Forge.v really
# exploits the bug), the checker under test accepts Control.v, and the checker
# under test refuses Forge.v with the text on the first line of <forge
# dir>/error. It prints four "forge <dir>: ..." lines that CI tools parse.

set -u

if [ "$#" -ne 3 ]; then
  echo "usage: $0 <forge dir> <reverted install root> <base install root>" >&2
  exit 2
fi

forge=$(cd "$1" && pwd) || { echo "cannot open forge dir $1" >&2; exit 2; }
reverted=$(cd "$2" && pwd) || { echo "cannot open install root $2" >&2; exit 2; }
base=$(cd "$3" && pwd) || { echo "cannot open install root $3" >&2; exit 2; }
dir=$(basename "$forge")

unset ROCQLIB COQLIB ROCQRUNTIMELIB COQCORELIB

scratch=$(mktemp -d) || { echo "cannot make a scratch dir" >&2; exit 1; }
trap 'rm -rf "$scratch"' EXIT

cp "$forge/Control.v" "$forge/Forge.v" "$scratch/" || {
  echo "FAIL $dir: cannot copy Control.v and Forge.v"
  exit 1
}
cd "$scratch" || exit 1

for m in Control Forge; do
  if ! "$reverted/bin/coqc" -coqlib "$reverted/lib/coq" -R "$scratch" "" "$m.v"; then
    echo "FAIL $dir: the reverted coqc did not compile $m.v; no check ran"
    exit 1
  fi
done

# chk <install root> <module> <title>: run that rocqchk on the module, print
# its output in a log group, and set out and rc.
chk() {
  rc=0
  out=$("$1/bin/rocqchk" -o -bytecode-compiler yes -coqlib "$reverted/lib/coq" \
    -R "$scratch" "" "$2" 2>&1) || rc=$?
  echo "::group::rocqchk output: $3, $2 ($dir)"
  printf '%s\n' "$out"
  echo "::endgroup::"
}

chk "$reverted" Control "reverted build"; rc_a=$rc
chk "$reverted" Forge "reverted build"; rc_b=$rc
chk "$base" Control "build under test"; rc_c=$rc
chk "$base" Forge "build under test"; rc_d=$rc; base_forge_out=$out

text=$(grep -o -F -f "$forge/error" <<<"$base_forge_out" | head -n1)
expected=$(head -n1 "$forge/error")

echo "forge $dir: reverted-chk Control exit=$rc_a"
echo "forge $dir: reverted-chk Forge exit=$rc_b"
echo "forge $dir: control exit=$rc_c"
echo "forge $dir: base-chk exit=$rc_d error=$text"

ok=1
if [ -z "$expected" ]; then
  echo "FAIL $dir: the first line of $forge/error is empty"
  ok=0
fi
if [ "$rc_a" -ne 0 ]; then
  echo "FAIL $dir: the reverted checker refused Control (exit $rc_a); Control.v or the build is broken"
  ok=0
fi
if [ "$rc_b" -ne 0 ]; then
  echo "FAIL $dir: the reverted checker refused Forge (exit $rc_b); the forge is not a real forge"
  ok=0
fi
if [ "$rc_c" -ne 0 ]; then
  echo "FAIL $dir: the checker under test refused Control (exit $rc_c); it rejects a good proof"
  ok=0
fi
if [ "$rc_d" -eq 0 ]; then
  echo "FAIL $dir: the checker under test accepted Forge; the bug is not fixed"
  ok=0
fi
if [ "$text" != "$expected" ]; then
  echo "FAIL $dir: the checker under test did not print \"$expected\" for Forge (found \"$text\")"
  ok=0
fi

[ "$ok" -eq 1 ] && exit 0
exit 1
