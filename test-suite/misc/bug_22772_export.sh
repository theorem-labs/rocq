#!/usr/bin/env bash

# rocq#22772, the fourth route to False collected by the BET-970 planner
# (dispatch://BET-970/artifact/rocq-22772-probes-md): a trusted library
# exports the primitive array operations, and the agent file writes no array
# word, no array literal and no exact_no_check -- it closes the false goal
# with "lazy. intros x y. reflexivity.".  The trusted half must still compile
# and pass rocqchk in both bytecode modes; the agent half must be refused.

set -u

export COQBIN=$BIN
export PATH="$BIN:$PATH"

D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
cp misc/bug_22772_export/TrustedMem.v misc/bug_22772_export/Export.v "$D/"

$coqc -Q "$D" T "$D/TrustedMem.v"
R=$?
if [ $R != 0 ]; then
  echo "TrustedMem.v must compile, got exit $R"
  exit 1
fi

$coqc -Q "$D" T "$D/Export.v"
R=$?
if [ $R = 0 ]; then
  echo "Export.v must be refused, but rocq compile accepted it"
  exit 1
fi

for vm in yes no; do
  "${BIN}rocqchk" -o -bytecode-compiler $vm -Q "$D" T -norec T.TrustedMem
  R=$?
  if [ $R != 0 ]; then
    echo "rocqchk -bytecode-compiler $vm must accept T.TrustedMem, got exit $R"
    exit 1
  fi
done

exit 0
