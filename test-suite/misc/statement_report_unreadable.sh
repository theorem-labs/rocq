#!/usr/bin/env bash

# An opaque body the checker cannot READ is reported as an axiom, as a body
# stored nowhere is (vernac/assumptions.ml's get_constant_body). The two are
# different events and the verdict alone cannot tell them apart, so the checker
# must NAME the failure: a warning carrying the constant and the error. Without
# it, a damaged table — or a lazy reader refusing a table whose bytes changed
# since intern — reads as a clean report of one more axiom.
# The exit status stays the successful check's on purpose: a body stored
# nowhere is an ordinary answer, and failing the check on it would turn every
# delayed proof into a failed grade.
set -eu

D=misc/statement_report_unreadable
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D/Opaque.v" "$d/"

$coqc -Q "$d" Unreadable "$d/Opaque.v"
printf 'r1 Unreadable.Opaque.model -\n' > "$d/requests"

# Ordinary run: the body is read, so nothing is an axiom and nothing is warned.
"$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" Unreadable Unreadable.Opaque > "$d/clean" 2>&1
grep -q '^END STATEMENT REPORT$' "$d/clean"
if grep -q 'could not be read' "$d/clean"; then
  echo "an ordinary run must not warn" >&2; cat "$d/clean" >&2; exit 1
fi
if grep -q '^axiom r1 Unreadable.Opaque.secret$' "$d/clean"; then
  echo "a readable opaque body is not an axiom" >&2; cat "$d/clean" >&2; exit 1
fi

# The read fails. The seam is a test variable the checker reads only when it is
# set (check_closure.ml's test_unreadable_opaque, beside test_fault): the real
# failures it stands for are not reachable from this suite's own objects.
if ! env COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE=Unreadable.Opaque.secret \
  "$BIN"rocqchk -silent -statement-report "$d/requests" -Q "$d" Unreadable Unreadable.Opaque > "$d/out" 2>&1; then
  echo "the check itself must still pass: an unreadable body is reported, not fatal" >&2
  cat "$d/out" >&2
  exit 1
fi

# The report is whole, so a parser still reads it as evidence.
grep -q '^STATEMENT REPORT$' "$d/out"
grep -q '^END STATEMENT REPORT$' "$d/out"

# The failure is named, with the constant and the cause.
grep -q 'Statement report: the opaque body of Unreadable.Opaque.secret could not be read' "$d/out"
grep -q 'test unreadable opaque body' "$d/out"

# And it still reads as an axiom, so the report never understates what the
# proof rests on.
grep -q '^axiom r1 Unreadable.Opaque.secret$' "$d/out"
