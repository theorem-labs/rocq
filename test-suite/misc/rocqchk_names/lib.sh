# Shared by the misc/rocqchk_name_*.sh and misc/statement_report_name_*.sh
# tests, which the test-suite runs from test-suite/: rocqchk must refuse, or
# stop its statement report at, a name that is not made of identifiers. Each
# probe prints rocqchk's output (through cat -v, so a control character shows)
# and one RESULT line.

set -eu

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

A=misc/rocqchk_names
R=$A/rename.ml
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
status=0

build_plugin () {
  cp -r "$A/_CoqProject" "$A/src" "$d/"
  mkdir -p "$d/theories"
  ( cd "$d" && rocq makefile -f _CoqProject -o Makefile && make src/bad_name_plugin.cmxs ) \
    > "$d/plugin.log" 2>&1 || { cat "$d/plugin.log"; echo "plugin build failed"; exit 1; }
}

# compile_theory NAME: theories/NAME.v, with the plugin, as BadNames.NAME.
compile_theory () {
  cp "$A/theories/$1.v" "$d/theories/"
  $coqc -I "$d/src" -Q "$d/theories" BadNames "$d/theories/$1.v"
}

# compile_plain DIR NAME...: each plain/NAME.v in DIR, in order, as BadNames.NAME.
compile_plain () {
  local dir=$1; shift
  mkdir -p "$dir"
  for n in "$@"; do
    cp "$A/plain/$n.v" "$dir/"
    $coqc -Q "$dir" BadNames "$dir/$n.v"
  done
}

# raw_line FILE PREFIX: a line of FILE starts with PREFIX, the lines split as
# Python's str.splitlines splits them, with the text read as UTF-8 and as
# Latin-1. If the check itself fails (no python3, a Python error), the script
# stops, so that failure cannot read as "no raw line".
raw_line () {
  local rc=0
  python3 -c '
import sys
data = open(sys.argv[1], "rb").read()
hit = False
for enc in ("utf-8", "latin-1"):
    try:
        text = data.decode(enc)
    except UnicodeDecodeError:
        continue
    hit = hit or any(l.startswith(sys.argv[2]) for l in text.splitlines())
sys.exit(0 if hit else 3)' "$1" "$2" || rc=$?
  case $rc in
    0) return 0 ;;
    3) return 1 ;;
    *) echo "raw_line: the python3 check exited $rc" >&2; exit 1 ;;
  esac
}

# matches ARGS...: grep -a -q ARGS, true when a line matches and false when
# none does. If grep itself fails (a read error), the script stops, so that
# failure cannot read as "no match".
matches () {
  local rc=0
  grep -a -q "$@" || rc=$?
  case $rc in
    0) return 0 ;;
    1) return 1 ;;
    *) echo "matches: grep exited $rc" >&2; exit 1 ;;
  esac
}

# probe ID KIND EXPECTED FORGED ARGS...: run rocqchk ARGS.
#  refuse: PASS when rocqchk exits non-zero, prints EXPECTED (a fixed string),
#    and no line starts with FORGED.
#  stop: PASS when rocqchk exits 0 with a STATEMENT REPORT line, no END
#    STATEMENT REPORT line, a "Statement report stopped" warning, EXPECTED,
#    and no line that starts with FORGED.
probe () {
  local id=$1 kind=$2 expected=$3 forged=$4; shift 4
  local rc=0 raw=no has=no verdict start=no end=no warn=no
  "$BIN"rocqchk "$@" > "$d/out.log" 2>&1 || rc=$?
  echo "--- $id: rocqchk $* ; exit $rc ---"
  cat -v "$d/out.log"
  echo "--- end $id ---"
  if raw_line "$d/out.log" "$forged"; then raw=yes; fi
  if matches -F -- "$expected" "$d/out.log"; then has=yes; fi
  if matches '^STATEMENT REPORT$' "$d/out.log"; then start=yes; fi
  if matches '^END STATEMENT REPORT$' "$d/out.log"; then end=yes; fi
  if matches '^Warning: Statement report stopped:' "$d/out.log"; then warn=yes; fi
  case $kind in
    refuse)
      if [ "$rc" -ne 0 ] && [ $has = yes ] && [ $raw = no ]; then verdict=PASS-REFUSED
      elif [ "$rc" -eq 0 ] && [ $raw = yes ]; then verdict=FAIL-RAW
      elif [ "$rc" -eq 0 ]; then verdict=FAIL-ACCEPTED
      elif [ $raw = yes ]; then verdict=FAIL-RAW-ON-ERROR
      else verdict=FAIL-OTHER-ERROR
      fi ;;
    stop)
      if [ "$rc" -eq 0 ] && [ $start = yes ] && [ $end = no ] && [ $warn = yes ] \
           && [ $has = yes ] && [ $raw = no ]; then verdict=PASS-STOPPED
      elif [ "$rc" -eq 0 ] && [ $raw = yes ]; then verdict=FAIL-RAW
      else verdict=FAIL-OTHER
      fi ;;
  esac
  echo "RESULT $id: $verdict (exit $rc, raw line: $raw, expected text: $has, report start/end/stopped: $start/$end/$warn)"
  case $verdict in PASS-*) ;; *) status=1 ;; esac
}

# both_vm ID KIND EXPECTED FORGED ARGS...: probe with the vm_compute machine
# off (the default) and on.
both_vm () {
  local id=$1 kind=$2 expected=$3 forged=$4; shift 4
  probe "$id-vmoff" "$kind" "$expected" "$forged" "$@"
  probe "$id-vmon" "$kind" "$expected" "$forged" -bytecode-compiler yes "$@"
}
