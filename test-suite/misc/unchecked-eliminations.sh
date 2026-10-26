#!/usr/bin/env bash

# There is intentionally no vernacular setter for the [check_eliminations]
# typing flag. This test builds a tiny plugin that toggles it via
# [Global.set_typing_flags] (the way rocq-lean-import does), declares a
# squashed Prop inductive with a large elimination while the flag is off, and
# checks that both [Print Assumptions] and [rocq check] report it.

set -ex

export COQBIN=$BIN
export PATH=$COQBIN:$PATH
export LC_ALL=C

cd misc/unchecked-eliminations/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/elim_flag_plugin.cmxs

# Compile the .v, capturing the Print Assumptions / Print Typing Flags output.
rocq c -I src -Q theories UncheckedElim theories/unchecked.v 2>&1 | tee log

# checked_or (declared with the flag on) must NOT be reported.
# Anchor at line start so this does not match "unchecked_or".
grep -q "^checked_or relies on unchecked sort eliminations" log && {
  >&2 echo "checked_or should not rely on unchecked eliminations"
  exit 1
}

# unchecked_or and its constructors (declared with the flag off) must be
# reported as relying on unchecked sort eliminations.
grep -q "^unchecked_or relies on unchecked sort eliminations" log
grep -q "^unchecked_l relies on unchecked sort eliminations" log
grep -q "^unchecked_r relies on unchecked sort eliminations" log

# The theory summary line appears under Set Printing All Assumptions.
grep -q "Sort elimination constraints are not checked (logic is inconsistent)" log

# Print Typing Flags reports the flag only while it is disabled; the final
# Print Typing Flags (flag restored) must not mention it.
grep -q "check_eliminations: false" log
grep -q "check_eliminations: true" log && {
  >&2 echo "check_eliminations should not be shown when at its default"
  exit 1
}

# rocq check must report the inductive in its context summary.
# `| tee` makes the pipeline's status tee's, and this script has no pipefail,
# so the checker's own status is read on the next line: without it a checker
# that CRASHED after printing would pass every grep below.
rocq check -Q theories UncheckedElim -o -silent -norec UncheckedElim.unchecked 2>&1 | tee chklog
rc=${PIPESTATUS[0]}
[ "$rc" -eq 0 ] || { >&2 echo "rocq check exited $rc"; exit 1; }

grep -q "Constants/Inductives relying on unchecked sort eliminations" chklog
grep -q "UncheckedElim.unchecked.unchecked_or" chklog
# ... and the one hidden behind an opaque seal, which the summary's
# environment fold cannot see (rocq-prover/rocq#22632). The whole name is
# matched, so that a listed recursor cannot stand in for the inductive.
grep -qE '^ +UncheckedElim\.unchecked\.Sealed\.hidden_or$' chklog

# rocq check -statement-report reports it for a constant whose closure reaches
# the inductive.
reqs=$(mktemp)
printf 'large UncheckedElim.unchecked.unchecked_large -\n' > "$reqs"
rocq check -Q theories UncheckedElim -statement-report "$reqs" -silent -norec UncheckedElim.unchecked 2>&1 | tee srlog
rc=${PIPESTATUS[0]}
rm -f "$reqs"
[ "$rc" -eq 0 ] || { >&2 echo "rocq check -statement-report exited $rc"; exit 1; }
grep -q "^flag large unchecked-eliminations UncheckedElim.unchecked.unchecked_or$" srlog
