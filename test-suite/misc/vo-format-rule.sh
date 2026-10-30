#!/usr/bin/env bash
# misc/vo-format.sh's rule for a new .vo segment, both ways (D18 keepfacts,
# dispatch://INFRA-361, review gate 1).
#
# A wrapper stands in for rocq-library-label: it prints the real
# --vo-representation of the build under test, edited, and misc/vo-format.sh
# runs against the committed reference with the wrapper as LIBRARY_LABEL, in a
# copy of its directory (so this test and misc/vo-format.sh can run at once).
# - unedited: rc 0 (the reference records this build);
# - a segment the reference does not record, appended after every recorded
#   one: rc 1, telling to record it with no vo_magic bump;
# - that segment inserted before a recorded one, the recorded keepfacts
#   segment moved before vmlibrary, a second segment under a recorded name,
#   a changed field of the recorded keepfacts segment: rc 1, telling to bump
#   vo_magic.

set -e
export PATH=$BIN:$PATH

. misc/library-label-tool.inc
REAL=$TOOL

W=$PWD/misc/_vofrule
rm -rf "$W"
mkdir -p "$W/misc/vo-format"
cp misc/vo-format.sh misc/library-label-tool.inc "$W/misc/"
cp misc/vo-format/reference.txt "$W/misc/vo-format/"

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }

# run NAME AWK_PROGRAM: misc/vo-format.sh with the printing edited by
# AWK_PROGRAM; sets rc, output in $W/NAME.out.
run() {
  local name=$1
  printf '%s\n' "$2" > "$W/$name.awk"
  printf '#!/usr/bin/env bash\n[ "$1" = --vo-representation ] || exit 2\n"%s" --vo-representation | awk -f "%s"\n' \
    "$REAL" "$W/$name.awk" > "$W/$name.wrap"
  chmod +x "$W/$name.wrap"
  (cd "$W" && LIBRARY_LABEL="$W/$name.wrap" bash misc/vo-format.sh) > "$W/$name.out" 2>&1 && rc=0 || rc=$?
}
show() { sed 's/^/    | /' "$W/$1.out" | head -20; }
expect_record() { # NAME: rc 1, record with no bump
  if [ "$rc" = 1 ] && grep -q 'no vo_magic bump' "$W/$1.out" && ! grep -q 'bump vo_magic in' "$W/$1.out"; then
    pass "$1: rc 1, record the printing with no vo_magic bump"
  else bad "$1: expected rc 1 and record with no bump, got rc $rc:"; show "$1"; fi
}
expect_bump() { # NAME: rc 1, bump vo_magic
  if [ "$rc" = 1 ] && grep -q 'bump vo_magic in' "$W/$1.out" && ! grep -q 'no vo_magic bump' "$W/$1.out"; then
    pass "$1: rc 1, bump vo_magic"
  else bad "$1: expected rc 1 and a vo_magic bump, got rc $rc:"; show "$1"; fi
}

if ! grep -q '^segment keepfacts ' misc/vo-format/reference.txt; then
  echo "FAIL the reference records no keepfacts segment; the cases below edit it"; exit 1
fi

run unedited '{ print }'
if [ "$rc" = 0 ]; then pass "unedited: rc 0"; else bad "unedited: rc $rc:"; show unedited; fi

run appended '{ print } END { print "segment zzz root #0"; print "  #0 = string" }'
expect_record appended

run inserted '/^segment summary / { print "segment zzz root #0"; print "  #0 = string" } { print }'
expect_bump inserted

run reordered '/^segment vmlibrary / { v = 1 } /^segment keepfacts / { v = 0; k = 1 }
{ if (v) vm = vm $0 ORS; else if (k) kf = kf $0 ORS; else printf "%s", $0 ORS }
END { printf "%s%s", kf, vm }'
expect_bump reordered

run reused '{ print } END { print "segment vmlibrary root #0"; print "  #0 = string" }'
expect_bump reused

run changed_field '/^segment / { k = ($2 == "keepfacts") }
k && /= sum\(bool,2,0,\)$/ { sub(/sum\(bool,2,0,\)$/, "int"); hit = 1 }
{ print }
END { if (!hit) exit 3 }'
expect_bump changed_field

exit $fail
