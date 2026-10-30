#!/usr/bin/env bash
# ROCQ_VM_INLINE=0 is the arm that generates the code this build's base
# generates (kernel/vmbytegen.ml, [levers_on]). It used to turn off only the
# compile-time expansion of a small called constant's body and to leave the
# native binary-number operations of kernel/vmznative.ml pinned, so the arm
# still compiled every function the machine recognizes differently from the
# base, and was not the control it is read as.
#
# This test compiles the three pinned functions (misc/vm_levers_off/Pins.v) with
# the levers on and off, and reads the two dumps: with the levers on the machine
# pins each function and emits its znative instruction; with them off it reads no
# body for an operation and emits none.
#
# The pin is part of compiling a declaration, so the switch also changes the
# bytecode a library file carries; the test requires that too, because an arm
# that is to generate and run the base's code must build its libraries under the
# switch. The expansion is the other half of the switch and is not tested here:
# only the in-process compiler of kernel/vmsymtable.ml performs it, and a
# declaration compiled into a library file is compiled with no expansion either
# way.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
cp "$(dirname "$0")/vm_levers_off/Pins.v" "$d/Pins.v"

dump() { # dump VALUE NAME -> the two dumps of one compilation, keeping its library file
  env ROCQ_VM_INLINE="$1" rocq c -d vmznative -d vmbytecode -R "$d" "" "$d/Pins.v" 2>&1
  cp "$d/Pins.vo" "$d/$2.vo"
}

on=$(dump 1 on)
off=$(dump 0 off)

fail() { >&2 echo "FAILURE: $1"; >&2 echo "--- levers on"; >&2 echo "$on"; >&2 echo "--- levers off"; >&2 echo "$off"; exit 1; }

for want in "padd native pos_add" "zpos_sub native pos_sub" "zadd native add"; do
  case $on in
    *"$want"*) ;;
    *) fail "with the levers on, the machine does not report \"$want\"" ;;
  esac
done
case $on in
  *"znative "*) ;;
  *) fail "with the levers on, no znative instruction is emitted" ;;
esac

case $off in
  *"znative "*) fail "with ROCQ_VM_INLINE=0, a znative instruction is still emitted" ;;
  *) ;;
esac
case $off in
  *" native "*) fail "with ROCQ_VM_INLINE=0, a body is still pinned to a native operation" ;;
  *) ;;
esac

# The pin goes into the declaration's bytecode, so the two compilations above
# wrote different library files.
if cmp -s "$d/on.vo" "$d/off.vo"; then
  >&2 echo "FAILURE: the switch left the library file's bytecode unchanged"
  exit 1
fi

# A misspelt switch must stop the process: a run that silently kept the levers
# on would be read as the base's.
set +e
env ROCQ_VM_INLINE=yes rocq c -R "$d" "" "$d/Pins.v" > "$d/o" 2> "$d/e"
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  >&2 echo "FAILURE: ROCQ_VM_INLINE=yes was accepted"
  exit 1
fi
case $(cat "$d/e") in
  *"ROCQ_VM_INLINE=yes"*) ;;
  *)
    >&2 echo "FAILURE: ROCQ_VM_INLINE=yes does not say what is wrong"
    >&2 cat "$d/e"
    exit 1 ;;
esac

rm -rf "$d"
