#!/usr/bin/env bash

# The -o summary refuses where its walk of the module implementations
# (checker/mod_impl.ml) stops. A library coqc writes reaches only the walk's
# two bounds (misc/rocqchk_application_bound_summary.sh); every other stop
# needs a shape coqc does not write, which an admitted library can hold,
# since rocqchk does not check it. forge.ml writes each such shape into a
# copy of the honest Stops.v, one shape to a copy, and rocqchk -o must refuse
# each copy with that stop's error:
#   alias-cycle             Self := Self
#   alias-two-cycle         Ping := Pong and Pong := Ping
#   implementation-cycle    Up := Down and Down := Up.C: the module Up is
#                           needed while Up is read
#   functor-implementation  NotF, which is not a functor, gets a functor's
#                           expression
#   with-functor            RW applies a 'with' constraint
#   expression-arguments    Gexpr's expression binds two parameters, and its
#                           type has one
#   path-chain              Chain.M := Chain and Chain.G (X : S) := X.M.G X.M:
#                           RC := Chain.G Chain resolves Chain.M...M.G with one
#                           more M at each step
#   argument-chain          G := G A: RG := G A resolves G with one argument
#                           more at each step
# Both chains end at the step bound, in time. Their errors are matched by a
# pattern, since the length of the path or the number of arguments depends
# on the steps taken. The stop where an application's arguments do not fit
# its functor's parameters is the one misc/rocqchk_functor_loop_summary.sh
# reaches. The honest library is the control: rocqchk -o lists the axiom ax
# of F's body under RC, RE and RW.
set -eu

. misc/rocqchk_summary_common.bash

D=misc/rocqchk-walk-stop
L=WalkStop.Stops
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest"
cp "$D/Stops.v" "$d/honest/"
$coqc -noinit -Q "$d/honest" WalkStop "$d/honest/Stops.v"

lists "$d/honest.log" "$L.RC.ax
$L.RE.ax
$L.RW.ax" -Q "$d/honest" WalkStop -admit "$L"

# forged <shape>: forge.ml's <shape> in a copy of the honest library, then
# what rocqchk -o's refusal says after its first sentence.
forged() {
  mkdir "$d/$1"
  cp "$d/honest/Stops.vo" "$d/$1/"
  ocaml "$D/forge.ml" "$1" "$d/$1/Stops.vo" > /dev/null || { echo "forge.ml $1 failed" >&2; exit 1; }
  refusal "$d/$1.log" -Q "$d/$1" WalkStop -admit "$L"
}

# stop <shape> <where and why>: the refusal of <shape> says exactly that.
stop() {
  local got
  got=$(forged "$1")
  if [ "$got" != "the walk of the module implementations stopped at $2." ]; then
    echo "rocqchk -o refused the $1 library with another error"
    cat "$d/$1.log"
    exit 1
  fi
}

stop alias-cycle "the alias $L.Self := $L.Self, whose target it is already reading: the aliases form a cycle"
stop alias-two-cycle "the alias $L.Pong := $L.Ping, whose target it is already reading: the aliases form a cycle"
stop implementation-cycle "the module $L.Up, whose implementation it needs while it reads it: the implementations form a cycle"
stop functor-implementation "the module $L.NotF, which is not a functor but is implemented by a functor or by a 'with' constraint"
stop with-functor "the application $L.RW, whose functor is a 'with' constraint"
stop expression-arguments "the application $L.RE := $L.Gexpr $L.A, whose arguments do not fit the parameters that the expression defining its functor binds"

# chain <shape> <pattern>: the refusal of <shape> matches the extended
# regular expression <pattern> after "stopped at ".
chain() {
  local got
  got=$(forged "$1")
  if ! printf '%s\n' "$got" | grep -q -x -E "the walk of the module implementations stopped at $2"; then
    echo "rocqchk -o refused the $1 library with another error"
    cat "$d/$1.log"
    exit 1
  fi
}

bound=', which would take it past 100000 steps, the most it takes for one summary\.'
chain path-chain "the application WalkStop\.Stops\.RC := WalkStop\.Stops\.Chain(\.M)+\.G WalkStop\.Stops\.Chain(\.M)+$bound"
chain argument-chain "the application WalkStop\.Stops\.RG := WalkStop\.Stops\.G( WalkStop\.Stops\.A){8} \.\.\. \([0-9]+ more\)$bound"
