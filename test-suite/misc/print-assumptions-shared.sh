#!/usr/bin/env bash
# ROCQ_ASSUMPTIONS_SHARED_DIR shares Print Assumptions entries between the
# processes that name one directory. Every query must print, with sharing,
# what it prints without it:
#
# - fresh:      Q1 alone, in an empty directory;
# - reused:     Q2 and Q3 after Q1 filled the directory, so they read its
#               entries (the debug counters must show reads);
# - concurrent: Q1, Q2 and Q3 at once, in an empty directory;
# - changed:    the negative control. Lib is compiled again with top1 proved
#               from the axiom lib_ax, and Q1 runs with the directory the old
#               Lib filled. Its entries for Lib's objects must not be read,
#               since the library changed: Q1 must name lib_ax, as without
#               sharing, and it must still read the entries of Base, which did
#               not change;
# - damaged:    in a directory Q1 filled, one entry is emptied, one is cut to
#               half its length, one has one byte in its middle flipped, and
#               one is deleted while its claim stays, which is what a
#               claimant that was killed during its walk leaves. Q1 must read
#               none of them, take over each claim at once (the system freed
#               the claimants' locks) instead of waiting, and walk the four
#               objects itself;
# - unusable:   a directory that cannot be created turns sharing off.
#
# Q3 also queries objects of the file being compiled, inside and outside a
# section, which are never shared.

set -e

export PATH=$BIN:$PATH
export LC_ALL=C

cd misc/print-assumptions-shared
rm -rf _test
mkdir -p _test
cp Base.v Lib.v Q1.v Q2.v Q3.v _test
cd _test

rc() { rocq c -q -R . S -native-compiler no "$@"; }

rc Base.v
rc Lib.v
for q in Q1 Q2 Q3; do rc $q.v > $q.plain.out; done

status=0

# [shared <dir> <file> <label>]: compiles <file> sharing <dir>; keeps stdout
# and the debug lines.
shared() {
  ROCQ_ASSUMPTIONS_SHARED_DIR=$1 ROCQ_DEBUG_ASSUMPTIONS_SHARED=1 rc "$2.v" > "$2.$3.out" 2> "$2.$3.err"
  grep -v '^\[assumptions-shared\] ' "$2.$3.err" > "$2.$3.other.err" || true
  diff -u /dev/null "$2.$3.other.err"
}

# [count <field> <file> <label>]: the sum of a debug counter over the queries.
count() {
  grep -o "$1 [0-9]*" "$2.$3.err" | awk '{ s += $2 } END { print s + 0 }'
}

mkdir fresh
shared fresh Q1 fresh
diff -u Q1.plain.out Q1.fresh.out
[ "$(count walked Q1 fresh)" -gt 0 ] || { echo "fresh: Q1 walked nothing"; status=1; }
# A copy of the directory only Q1 filled, for the damaged case.
cp -r fresh damaged

for q in Q2 Q3; do
  shared fresh $q reused
  diff -u $q.plain.out $q.reused.out
  reads=$(count read $q reused)
  echo "reused: $q read $reads entries"
  [ "$reads" -gt 0 ] || { echo "reused: $q read no entry, so the case tests no sharing"; status=1; }
done

mkdir concurrent
shared concurrent Q1 concurrent & p1=$!
shared concurrent Q2 concurrent & p2=$!
shared concurrent Q3 concurrent & p3=$!
wait $p1; wait $p2; wait $p3
for q in Q1 Q2 Q3; do diff -u $q.plain.out $q.concurrent.out; done

cp ../changed/Lib.v Lib.v
rc Lib.v
rc Q1.v > Q1.changed.plain.out
if diff -q Q1.plain.out Q1.changed.plain.out > /dev/null; then
  echo "changed: Lib's change does not change Q1's output, so the control tests nothing"
  status=1
fi
shared fresh Q1 changed
diff -u Q1.changed.plain.out Q1.changed.out
reads=$(count read Q1 changed)
walked=$(count walked Q1 changed)
echo "changed: Q1 read $reads entries and walked $walked objects"
[ "$reads" -gt 0 ] || { echo "changed: Q1 read no entry of Base"; status=1; }
[ "$walked" -gt 0 ] || { echo "changed: Q1 walked nothing, so it read entries of the old Lib"; status=1; }

cp ../Lib.v Lib.v
rc Lib.v
set -- $(ls damaged/entries/*/* | grep -v '\.claim$')
: > "$1"
n=$(wc -c < "$2"); head -c $((n / 2)) "$2" > cut.tmp; mv cut.tmp "$2"
n=$(wc -c < "$3"); off=$((n / 2))
b=$(od -An -tu1 -j $off -N1 "$3" | tr -d ' ')
printf "\\$(printf '%03o' $((b ^ 1)))" | dd of="$3" bs=1 seek=$off conv=notrunc 2> /dev/null
rm "$4"
[ -e "$4.claim" ] || { echo "damaged: no claim beside $4"; status=1; }
start=$(date +%s%N)
shared damaged Q1 damaged
elapsed=$(( ($(date +%s%N) - start) / 1000000 ))
diff -u Q1.plain.out Q1.damaged.out
taken=$(grep -o '[0-9]* taken over' Q1.damaged.err | awk '{ s += $1 } END { print s + 0 }')
echo "damaged: Q1 took over $taken claims in $elapsed ms"
[ "$taken" -eq 4 ] || { echo "damaged: expected 4 claims taken over"; status=1; }
[ "$elapsed" -lt 5000 ] || { echo "damaged: Q1 waited for a claimant that is gone"; status=1; }

shared "$PWD/missing/dir" Q1 unusable
diff -u Q1.plain.out Q1.unusable.out
grep -q 'sharing off' Q1.unusable.err || { echo "unusable: sharing stayed on"; status=1; }

exit $status
