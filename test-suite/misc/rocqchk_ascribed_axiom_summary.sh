#!/usr/bin/env bash
# The Axioms section of rocqchk -o and Print Assumptions must name the same
# constants where [Module M : T := E] puts T in the environment and E defines
# the field. The summary once read "no body in the environment" as "assumed"
# and named a definition (dispatch://BET-245), a name only one of the two
# accounts prints, which the BET grader's join reads as a smuggled assumption.
#
# The shapes are the ones output-coqchk/ascribed_axiom_summary.v declares,
# read here through the other account: that file pins the whole summary under
# -norec, and this test runs Print Assumptions over each of its proofs and
# then checks each name of two lists in both accounts, the constants both
# must name and the modules neither may (or, for Open, the field itself,
# which a module name would match beyond), under a recursive check as well,
# where the library is read as a dependency.
set -eu
export PATH="$BIN:$PATH"

src=output-coqchk/ascribed_axiom_summary.v
lib=ascribed_axiom_summary

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$src" "$d/"

cat > "$d/Use.v" <<EOF
Require $lib.
Print Assumptions $lib.over_definition.
Print Assumptions $lib.over_axiom.
Print Assumptions $lib.over_chain.
Print Assumptions $lib.over_submodule.
Print Assumptions $lib.over_include.
Print Assumptions $lib.over_global_axiom.
Print Assumptions $lib.nested.
Print Assumptions $lib.open_definition.
Print Assumptions $lib.open_axiom.
Print Assumptions $lib.declared.
Print Assumptions $lib.open_opaque.
Print Assumptions $lib.of_type.
Print Assumptions $lib.applied.
Print Assumptions $lib.over_type.
EOF
rocq c -native-compiler no -R "$d" "" "$d/$lib.v"
rocq c -native-compiler no -R "$d" "" "$d/Use.v" > "$d/pa.log" 2>&1

# Print one summary section: its "* <title>" line and the lines under it, up to
# the next "* " bullet. awk's index() takes the title literally.
section() { awk -v h="* $1" 'index($0, h) == 1 { p = 1; print; next } p && /^\* / { exit } p { print }' "$2"; }

# Each constant both accounts must name.
assumed="$lib.OverAxiom.Asc.p $lib.global_ax $lib.Nested.Plain.inner_ax
         $lib.OpenAssumed.p $lib.Declared.p $lib.Applied.Asc.p
         $lib.OverType.Held.Asc.p"
# Each module whose field an expression defines: neither account names it.
defined="$lib.OverDefinition $lib.OverChain $lib.OverSubmodule
         $lib.OverInclude $lib.Open.p $lib.OpenOpaque
         $lib.OverGlobalAxiom"

for name in $assumed; do
  grep -q "^$name : " "$d/pa.log"
done
for name in $defined; do
  if grep -qF "$name" "$d/pa.log"; then
    echo "Print Assumptions named $name, whose field an expression defines"; exit 1
  fi
done
# A module type carries [Module Asc : U := Defines] of its own, and OfType is
# declared, so nothing implements it and its field is a parameter. The summary
# keeps the name; Print Assumptions reads the type's expression and prints
# none, which is the direction a join of the two fails closed on.
if grep -qF "$lib.OfType" "$d/pa.log"; then
  echo "Print Assumptions named a field of a declared module"; exit 1
fi

for args in "Use" "-norec $lib"; do
  # shellcheck disable=SC2086
  rocqchk -o -silent -R "$d" "" $args > "$d/chk.log" 2>&1
  axioms=$(section 'Axioms' "$d/chk.log")
  for name in $assumed $lib.OfType.Asc.p; do
    printf '%s\n' "$axioms" | grep -qx "    $name"
  done
  for name in $defined; do
    if printf '%s\n' "$axioms" | grep -qF "$name"; then
      echo "the summary named $name, whose field an expression defines ($args)"
      exit 1
    fi
  done
done
