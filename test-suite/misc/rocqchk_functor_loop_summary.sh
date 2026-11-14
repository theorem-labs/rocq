#!/usr/bin/env bash

# The -o summary reads a functor application through its functor's body
# (checker/mod_impl.ml), and the applications in that body in turn. rocqchk
# does not check an admitted library, so its functor's body can apply that
# functor again, which coqc never writes: forge.ml makes F's body in the
# honest Loop.v hold Grow := F Loc. In F's body read as R := F A, F's own
# path names R, so the walk reads Grow as R's expression F A applied to
# R.Loc as well: one argument more than F takes. It cannot read that
# application, so rocqchk -o must end, and refuse to print a summary, with
# an error that names it. The honest library is the control: it lists R.ax
# alone.
set -eu

. misc/rocqchk_summary_common.bash

D=misc/rocqchk-functor-loop
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
mkdir "$d/honest" "$d/forged"
cp "$D/Loop.v" "$d/honest/"

$coqc -noinit -Q "$d/honest" FunctorLoop "$d/honest/Loop.v"
cp "$d/honest/Loop.vo" "$d/forged/"
ocaml "$D/forge.ml" "$d/forged/Loop.vo"

lists "$d/honest.log" FunctorLoop.Loop.R.ax -Q "$d/honest" FunctorLoop -admit FunctorLoop.Loop

got=$(refusal "$d/forged.log" -Q "$d/forged" FunctorLoop -admit FunctorLoop.Loop)
expected="the walk of the module implementations stopped at the application FunctorLoop.Loop.R.Grow := FunctorLoop.Loop.F FunctorLoop.Loop.A FunctorLoop.Loop.R.Loc, whose arguments do not fit the functor's parameters."
if [ "$got" != "$expected" ]; then
  echo "rocqchk -o refused the forged functor with another error"
  cat "$d/forged.log"
  exit 1
fi
