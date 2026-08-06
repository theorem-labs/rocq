#!/usr/bin/env bash

set -eu

export PATH="$BIN:$PATH"

cd misc/restricted-model-policy
rm -rf _test
mkdir _test
cp ./*.v _test/
cd _test

expect_rejected() {
  source=$1
  if rocq c -q -l Bootstrap.v "$source" > "$source.log" 2>&1; then
    echo "$source should have been rejected by the restricted-model policy" >&2
    exit 1
  fi
  grep -F "Restricted model compilation rejects" "$source.log"
}

# The policy is opt-in: ordinary Rocq retains its normal file-output behavior.
rocq c -q NormalMode.v
test -f normal-mode.out

# Gallina and ordinary proof execution are unchanged in restricted mode.
rocq c -q -l Bootstrap.v Allowed.v

# A Require is accepted only when the trusted command line loaded it before
# Bootstrap.v installed the policy hook.
rocq c -q -require Corelib.Classes.RelationClasses -l Bootstrap.v PreloadedRequire.v
expect_rejected UnloadedRequire.v

expect_rejected Redirect.v
expect_rejected Load.v
expect_rejected DeclareML.v
expect_rejected Chdir.v
expect_rejected ExtraDependency.v
expect_rejected UniverseChecking.v
expect_rejected BypassCheck.v
expect_rejected Extension.v
expect_rejected PrintUniverses.v
expect_rejected Rollback.v

# Rejection happens outside VernacControl, so [Fail] cannot turn a forbidden
# command into an accepted one, and neither direct nor loaded payloads run.
expect_rejected FailRedirect.v
test ! -e redirect.out
test ! -e fail-redirect.out
test ! -e payload.out
