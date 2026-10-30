#!/usr/bin/env bash
# The table of kernel/hConstr.ml puts a hash at the slot its product with an odd
# constant names and walks the following slots while they are taken. The
# constant is invertible, and the hash of a primitive integer literal is the
# literal itself plus 126, so a .v file can carry hashes that all name one slot:
# every insertion and every lookup then walked the whole cluster, and the cost
# of the table became quadratic in the number of such literals (the cross-family
# review of speed-6 measured 65,536 of them at 48.6 times the tree this table
# replaced). A probe now walks at most a fixed number of slots and keeps the
# rest of a cluster in a map, where a lookup costs what the tree cost.
#
# This test builds 65,536 colliding literals and the same number of ordinary
# ones, and requires:
#  - the colliding file to spill, i.e. the bound to engage, and the ordinary
#    file to spill nothing, from the counts [Set Debug "hconstr"] prints;
#  - the colliding file to compile within twice the time of the ordinary one,
#    which the quadratic walk did not.
#
# The ordinary file spills nothing because its hashes are consecutive, which the
# multiplier spreads best. An ordinary library file is not like that: measured
# with Set Debug "hconstr" on six stdlib files, 0 to 3 hashes of between 4,579
# and 119,022 spill, so do not read this control as "no real input ever spills".
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
n=${HCONSTR_COLLISION_N:-65536}

python3 - "$d" "$n" <<'PY'
import sys
d, n = sys.argv[1], int(sys.argv[2])
# kernel/hConstr.ml: slot = (hash * golden) lsr shift, on 63-bit ints, and
# hash_kind (Int i) = 7 * 18 + Uint63.hash i = 126 + i (clib/hashset.ml).
M = 1 << 63
golden = 0x4F1BBCDCBFA53E0B % M
ginv = pow(golden, -1, M)
# Every hash whose product with golden lies in one window of 2^40 shares the
# top 23 bits, so it shares its home slot at every size the table can take here.
shift, target = 40, 1
colliding = [(((target << shift) + j) * ginv) % M for j in range(n)]
assert len({(h * golden) % M >> shift for h in colliding}) == 1
def write(path, name, lits):
    with open(path, "w") as f:
        f.write("From Corelib Require Import PrimInt63 PrimArray.\n")
        f.write("Open Scope uint63_scope.\n")
        f.write("Definition %s : array int := [|\n" % name)
        f.write(";\n".join(str(x) for x in lits))
        f.write("\n| 0 |].\n")
write(d + "/Collide.v", "colliding_literals", [(h - 126) % M for h in colliding])
# The control is the same file with literals whose hashes are consecutive, which
# the multiplier spreads over the slots.
write(d + "/Control.v", "ordinary_literals", list(range(1, n + 1)))
PY

compile() { # compile FILE -> seconds, in $t
  local start stop
  start=$(date +%s%N)
  rocq c -q -R "$d" "" "$d/$1"
  stop=$(date +%s%N)
  t=$(( (stop - start) / 1000000 ))
}

compile Control.v; control=$t
compile Collide.v; collide=$t
echo "ordinary literals: ${control} ms, colliding literals: ${collide} ms"

spilled() { # spilled FILE -> the spilled counts the kernel reports
  rocq c -q -d hconstr -R "$d" "" "$d/$1" 2>&1 | sed -n 's/.*spilled = \([0-9]*\).*/\1/p'
}

collide_spilled=$(spilled Collide.v | sort -rn | head -1)
control_spilled=$(spilled Control.v | sort -rn | head -1)
echo "spilled hashes: colliding ${collide_spilled:-none}, ordinary ${control_spilled:-none}"

if [ -z "$collide_spilled" ] || [ -z "$control_spilled" ]; then
  >&2 echo "FAILURE: the kernel reported no spilled count; is the hconstr debug line there?"
  exit 1
fi
if [ "$collide_spilled" -eq 0 ]; then
  >&2 echo "FAILURE: the colliding literals spilled nothing, so the probe is not bounded"
  exit 1
fi
if [ "$control_spilled" -ne 0 ]; then
  >&2 echo "FAILURE: ordinary literals spilled $control_spilled hashes"
  exit 1
fi
if [ "$collide" -gt $(( 2 * control )) ]; then
  >&2 echo "FAILURE: the colliding literals took ${collide} ms against ${control} ms for the same number of ordinary ones"
  exit 1
fi

rm -rf "$d"
