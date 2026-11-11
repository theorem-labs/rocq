#!/usr/bin/env bash
# The checks of rocqchk -compare (dispatch://BET-894, dispatch://BET-901).
#
# Each case is a directory under misc/compare/<case>/:
#
#   challenge/*.v     the task as the agent receives it, proofs Admitted
#   answer/*.v        an honest answer; it must pass
#   bad-<name>/*.v    an answer that must fail: at least one theorem's
#                     verdict is fail, or, with a file `refuse` in the case
#                     directory, the run itself must exit non-zero
#   pre/*.v           optional, libraries bound with -Q under the root Pre,
#                     in pre-order or alphabetically. Shared.vo, when there
#                     is one, is declared pre-checked; Pin.vo is pinned only
#                     by a config that writes @PRECHECKED_PIN@
#   pre-order         optional, the order to compile pre/*.v in
#   shared/*.v        optional, libraries under the root Img, reached
#                     through ROCQPATH and bound by no -Q: they stand for
#                     the IMAGE's own installed libraries, which a test must
#                     neither compile nor write into
#   shared-order      optional, the order to compile shared/*.v in
#   bad-<name>/vendor/*.v
#                     optional, a tree the bad answer binds under a second
#                     root, Vendor, that no challenge file lives under
#   bad-<name>/vendor-root
#                     optional, the root that tree is bound to (default
#                     Vendor)
#   config.tmpl       the config, with @SHA256:<file>@ for a challenge
#                     file's digest and @PRECHECKED@ for the pre-checked
#                     array
#   expected.json     the verdict the honest answer must give; only the
#                     (name, verdict) pairs are compared, because a reason
#                     is prose
#   expected-flags    optional, one flag kind per line that the honest
#                     answer's passing verdict must record
#   order             optional, the order to compile the .v files in
#                     (default: alphabetical)
#   refuse-<name>/    optional, a directory holding a raw config.json that
#                     the run must refuse with a non-zero exit
#   fail-config/expected-reason
#                     optional, a regular expression the failed reason must
#                     match

#   bad-<name>/tolerate-<flag>.tmpl
#                     optional, a config that tolerates <flag>: that bad
#                     answer must pass under it with the flag recorded
#   bad-<name>/expected-reason
#                     optional, a regular expression the failed reason must
#                     match
#
# The runner takes a case name, or runs every case when given none.
#
# The challenge and the answer are compiled from the SAME source layout, at
# the same paths and under the same logical root (Top), which is what the
# grader does: nothing is renamed.

set -eu

: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"

here=$(cd "$(dirname "$0")" && pwd)
cases_dir="$here/compare"

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# The (name, verdict) pairs of a verdict file, sorted. A reason is prose and
# is not compared; its presence is.
verdicts() {
  grep -o '"name":"[^"]*","verdict":"[^"]*"' "$1" | sort
}

prelude_vo() {
  local w p
  w=$(rocq -where)
  for p in "$w/theories/Corelib/Init/Prelude.vo" "$w/theories/Init/Prelude.vo"; do
    [ -f "$p" ] && { echo "$p"; return; }
  done
  fail "cannot find Prelude.vo under $w"
}

# The verdict file parses, when a JSON reader is at hand. A reader that is
# not there leaves the check out rather than passing it silently; the suite
# prints which.
json_valid() {
  if command -v python3 > /dev/null; then
    python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$1"
  else
    echo "  (no python3: the verdict file is not parsed)" >&2
  fi
}

# ---------------------------------------------------------------- sha256
#
# The comparator carries its own SHA-256, because the checker links no
# digest library. It is trusted code, so it is checked against FIPS 180-4's
# vectors and against sha256sum here, and compare.sh compares it with
# sha256sum on every challenge file it builds (see run_case).
case_sha256() {
  local d
  d=$(mktemp -d)
  local n=0
  check_vector() { # <content-producer> <expected>
    n=$((n + 1))
    "$1" > "$d/v$n"
    local got
    got=$(rocqchk -sha256 "$d/v$n")
    [ "$got" = "$2" ] || fail "sha256 vector $n is $got, expected $2"
    if command -v sha256sum > /dev/null; then
      local ref
      ref=$(sha256sum "$d/v$n" | cut -d' ' -f1)
      [ "$got" = "$ref" ] || fail "sha256 vector $n is $got, sha256sum says $ref"
    fi
  }
  v_empty() { printf ''; }
  v_abc() { printf 'abc'; }
  v_448() { printf 'abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq'; }
  v_896() { printf '%s' 'abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu'; }
  v_million() { for _ in $(seq 1 1000); do printf '%01000d' 0 | tr '0' 'a'; done; }
  check_vector v_empty e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
  check_vector v_abc ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  check_vector v_448 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
  check_vector v_896 cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1
  check_vector v_million cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0
  # a file of 1 MiB of random bytes, against sha256sum
  if command -v sha256sum > /dev/null; then
    head -c 1048576 /dev/urandom > "$d/rand"
    local got ref
    got=$(rocqchk -sha256 "$d/rand")
    ref=$(sha256sum "$d/rand" | cut -d' ' -f1)
    [ "$got" = "$ref" ] || fail "sha256 of a random file is $got, sha256sum says $ref"
  fi
  rm -rf "$d"
  echo "ok sha256"
}

# ---------------------------------------------------------------- a case

# The image stand-in: when a case ships shared/, every coqc and rocqchk of
# that case runs with ROCQPATH pointing at a directory holding those
# libraries under the root Img. A -Q would make them the answer's side; the
# image's own libraries are bound by no -Q, and a test must not write into
# the installation it runs against.
rocq_env=()

# Compile every .v of <src> into <dst>, under the logical root Top, with the
# pre-checked library of <pre> on the load path when there is one.
build_tree() {
  local src=$1 dst=$2 pre=$3 order=$4 vendor=${5:-} vroot=${6:-Vendor}
  mkdir -p "$dst"
  cp "$src"/*.v "$dst"/
  local args=(-R "$dst" Top)
  [ -n "$pre" ] && args+=(-R "$pre" Pre)
  [ -n "$vendor" ] && args+=(-R "$vendor" "$vroot")
  # A tree may need a flag of its own, for example -allow-rewrite-rules.
  if [ -f "$src/coqc-flags" ]; then
    local extra
    read -r extra < "$src/coqc-flags"
    args+=($extra)
  fi
  local f
  for f in $order; do
    (cd "$dst" && "${rocq_env[@]}" coqc "${args[@]}" "$f") || fail "$src/$f does not compile"
  done
}

file_order() {
  local src=$1
  if [ -f "$src/../order" ]; then
    cat "$src/../order"
  else
    (cd "$src" && ls *.v | sort)
  fi
}

# The config: @SHA256:<file>@ becomes that challenge file's digest,
# @PRECHECKED@ the pre-checked array and @PRECHECKED_PIN@ the entry for
# pre/Pin.vo, which only a config that asks for it pins.
make_config() {
  local tmpl=$1 chdir=$2 out=$3 pre=$4
  local pre_json=""
  if [ -n "$pre" ] && [ -f "$pre/Shared.vo" ]; then
    local sha
    sha=$(rocqchk -sha256 "$pre/Shared.vo")
    pre_json="{\"library\":\"Pre.Shared\",\"sha256\":\"$sha\"}"
  fi
  local pin_json=""
  if [ -n "$pre" ] && [ -f "$pre/Pin.vo" ]; then
    local pin_sha
    pin_sha=$(rocqchk -sha256 "$pre/Pin.vo")
    pin_json=",{\"library\":\"Pre.Pin\",\"sha256\":\"$pin_sha\"}"
  fi
  local prelude
  prelude=$(prelude_vo)
  local prelude_sha
  prelude_sha=$(rocqchk -sha256 "$prelude")
  local all="{\"library\":\"Corelib.Init.Prelude\",\"sha256\":\"$prelude_sha\"}"
  [ -n "$pre_json" ] && all="$all,$pre_json"
  local text
  text=$(cat "$tmpl")
  local f
  for f in "$chdir"/*.vo; do
    local base sha
    base=$(basename "$f")
    sha=$(rocqchk -sha256 "$f")
    # Every digest the comparator writes into a config is also checked
    # against sha256sum, so a defect in the comparator's SHA-256 cannot hide
    # behind its own agreement with itself.
    if command -v sha256sum > /dev/null; then
      local ref
      ref=$(sha256sum "$f" | cut -d' ' -f1)
      [ "$sha" = "$ref" ] || fail "rocqchk -sha256 $f is $sha, sha256sum says $ref"
    fi
    text=${text//"@SHA256:$base@"/$sha}
  done
  local zero=0000000000000000000000000000000000000000000000000000000000000000
  text=${text//"@PRECHECKED_BAD@"/"{\"library\":\"Corelib.Init.Prelude\",\"sha256\":\"$zero\"}"}
  text=${text//"@PRECHECKED@"/$all}
  text=${text//"@PRECHECKED_PIN@"/$pin_json}
  # The standard library's eq is built without -indices-matter, so every
  # honest answer reaches that flag on that object. A tolerated flag names
  # its object, so tolerating it here tolerates nothing of the agent's own.
  text=${text//"@TOLERATED@"/'{"kind": "indices-not-mattering", "object": "Corelib.Init.Logic.eq"}'}
  printf '%s\n' "$text" > "$out"
}

# Run the comparator on one answer tree. Prints the exit code; the verdict
# file is $work/out.json.
run_compare() {
  local work=$1 answer=$2 config=$3 pre=$4 vendor=${5:-} vroot=${6:-Vendor}
  local args=(-silent -Q "$answer" Top)
  [ -n "$pre" ] && args+=(-Q "$pre" Pre)
  [ -n "$vendor" ] && args+=(-Q "$vendor" "$vroot")
  local libs=()
  local f
  for f in "$answer"/*.vo; do libs+=("Top.$(basename "$f" .vo)"); done
  set +e
  "${rocq_env[@]}" rocqchk "${args[@]}" -compare "$config" -challenge "$work/challenge" \
    -compare-out "$work/out.json" "${libs[@]}" > "$work/log" 2>&1
  local code=$?
  set -e
  echo "$code"
}

run_case() {
  local name=$1
  local c="$cases_dir/$name"
  [ -d "$c" ] || fail "no case $name"
  local work
  work=$(mktemp -d)

  # The image stand-in, reached through ROCQPATH and bound by no -Q.
  rocq_env=()
  if [ -d "$c/shared" ]; then
    mkdir -p "$work/rocqpath/Img"
    cp "$c/shared"/*.v "$work/rocqpath/Img"/
    local sorder
    if [ -f "$c/shared-order" ]; then sorder=$(cat "$c/shared-order")
    else sorder=$(cd "$work/rocqpath/Img" && ls *.v | sort); fi
    local sf
    for sf in $sorder; do
      (cd "$work/rocqpath/Img" && ROCQPATH="$work/rocqpath" coqc -Q . Img "$sf") \
        || fail "$name: the image library $sf does not compile"
    done
    rocq_env=(env "ROCQPATH=$work/rocqpath")
  fi

  local pre=""
  if [ -d "$c/pre" ]; then
    pre="$work/pre"
    mkdir -p "$pre"
    cp "$c/pre"/*.v "$pre"/
    local porder
    if [ -f "$c/pre-order" ]; then porder=$(cat "$c/pre-order")
    else porder=$(cd "$pre" && ls *.v | sort); fi
    local pf
    for pf in $porder; do
      (cd "$pre" && "${rocq_env[@]}" coqc -Q . Pre "$pf") \
        || fail "$name: the library $pf does not compile"
    done
  fi

  local order
  order=$(file_order "$c/challenge")
  build_tree "$c/challenge" "$work/challenge" "$pre" "$order"
  make_config "$c/config.tmpl" "$work/challenge" "$work/config.json" "$pre"

  # the honest answer
  local order_a code
  order_a=$(file_order "$c/answer")
  build_tree "$c/answer" "$work/answer" "$pre" "$order_a"
  code=$(run_compare "$work" "$work/answer" "$work/config.json" "$pre")
  [ "$code" = "0" ] || { cat "$work/log"; fail "$name: the honest answer exits $code"; }
  [ -f "$work/out.json" ] || fail "$name: no verdict file"
  json_valid "$work/out.json" || fail "$name: the verdict file is not valid JSON"
  diff <(verdicts "$work/out.json") <(verdicts "$c/expected.json") \
    || { cat "$work/out.json"; fail "$name: the honest answer's verdicts differ"; }
  if [ -f "$c/expected-flags" ]; then
    local flag
    while IFS= read -r flag; do
      [ -z "$flag" ] && continue
      grep -q "\"kind\":\"$flag\"" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name: the passing verdict does not record $flag"; }
    done < "$c/expected-flags"
  fi

  # the answers that must fail
  local bad
  for bad in "$c"/bad-*; do
    [ -d "$bad" ] || continue
    local b
    b=$(basename "$bad")
    local bdir="$work/$b"
    local border
    border=$(file_order "$bad")
    # A bad answer may ship a tree of its own under a SECOND root, bound
    # with -Q and holding no challenge counterpart: a library the answer
    # wrote that the comparator must not take for one of the image's. The
    # root is Vendor, or the name in vendor-root, which a case uses to bind
    # a name the image itself serves.
    local bvendor="" vroot="Vendor"
    if [ -f "$bad/vendor-root" ]; then read -r vroot < "$bad/vendor-root"; fi
    if [ -d "$bad/vendor" ]; then
      bvendor="$work/$b-vendor"
      mkdir -p "$bvendor"
      cp "$bad/vendor"/*.v "$bvendor"/
      local vf
      for vf in $(cd "$bvendor" && ls *.v | sort); do
        (cd "$bvendor" && "${rocq_env[@]}" coqc -R . "$vroot" ${pre:+-R "$pre" Pre} "$vf") \
          || fail "$name/$b: the vendor library $vf does not compile"
      done
    fi
    build_tree "$bad" "$bdir" "$pre" "$border" "$bvendor" "$vroot"
    code=$(run_compare "$work" "$bdir" "$work/config.json" "$pre" "$bvendor" "$vroot")
    if [ -f "$bad/refuse" ]; then
      [ "$code" != "0" ] || fail "$name/$b: the run should not have completed"
    else
      [ "$code" = "0" ] || { cat "$work/log"; fail "$name/$b: the run exits $code"; }
      grep -q '"verdict":"fail"' "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b: no theorem failed"; }
      if [ -f "$bad/expected-reason" ]; then
        local reason
        while IFS= read -r reason; do
          [ -z "$reason" ] && continue
          grep -Eq -- "$reason" "$work/out.json" \
            || { cat "$work/out.json"; fail "$name/$b: the failure does not match $reason"; }
        done < "$bad/expected-reason"
      fi
    fi
    echo "  ok $name/$b"
    # A named tolerance is a documented cost: it must turn this exact bad
    # answer into a pass and the verdict must say that it did.
    local tolerate
    for tolerate in "$bad"/tolerate-*.tmpl; do
      [ -f "$tolerate" ] || continue
      local flag
      flag=$(basename "$tolerate" .tmpl)
      flag=${flag#tolerate-}
      make_config "$tolerate" "$work/challenge" "$work/tolerated-config.json" "$pre"
      code=$(run_compare "$work" "$bdir" "$work/tolerated-config.json" "$pre" "$bvendor" "$vroot")
      [ "$code" = "0" ] || { cat "$work/log"; fail "$name/$b/$flag: the run exits $code"; }
      grep -q '"verdict":"pass"' "$work/out.json" \
        && ! grep -q '"verdict":"fail"' "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b/$flag: the tolerated answer did not pass"; }
      grep -q "\"kind\":\"$flag\"" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b/$flag: the passing verdict does not record $flag"; }
      echo "  ok $name/$b/$flag"
      code=$(run_compare "$work" "$work/answer" "$work/tolerated-config.json" "$pre")
      [ "$code" = "0" ] || { cat "$work/log"; fail "$name/$b/$flag: the unchanged answer exits $code"; }
      grep -q '"verdict":"pass"' "$work/out.json" \
        && ! grep -q "\"kind\":\"$flag\"" "$work/out.json" \
        || { cat "$work/out.json"; fail "$name/$b/$flag: an unused tolerance was recorded"; }
    done
  done

  # configs that must be refused
  local ref
  for ref in "$c"/refuse-*; do
    [ -d "$ref" ] || continue
    local r
    r=$(basename "$ref")
    rm -f "$work/out.json"
    if [ -f "$ref/config.tmpl" ]; then
      make_config "$ref/config.tmpl" "$work/challenge" "$work/bad-config.json" "$pre"
    else
      cp "$ref/config.json" "$work/bad-config.json"
    fi
    code=$(run_compare "$work" "$work/answer" "$work/bad-config.json" "$pre")
    [ "$code" != "0" ] || fail "$name/$r: the run should not have completed"
    [ ! -f "$work/out.json" ] || fail "$name/$r: a verdict file was written anyway"
    echo "  ok $name/$r"
  done

  # A config under which the honest answer must fail, rather than one the
  # comparator refuses.
  local fc
  for fc in "$c"/fail-config; do
    [ -d "$fc" ] || continue
    make_config "$fc/config.tmpl" "$work/challenge" "$work/fail-config.json" "$pre"
    code=$(run_compare "$work" "$work/answer" "$work/fail-config.json" "$pre")
    [ "$code" = "0" ] || { cat "$work/log"; fail "$name/fail-config: the run exits $code"; }
    grep -q '"verdict":"fail"' "$work/out.json" \
      || { cat "$work/out.json"; fail "$name/fail-config: the honest answer passed"; }
    if [ -f "$fc/expected-reason" ]; then
      local reason
      while IFS= read -r reason; do
        [ -z "$reason" ] && continue
        grep -Eq -- "$reason" "$work/out.json" \
          || { cat "$work/out.json"; fail "$name/fail-config: the failure does not match $reason"; }
      done < "$fc/expected-reason"
    fi
    echo "  ok $name/fail-config"
  done

  # A config whose bytes are not UTF-8. It is written here rather than kept
  # as a file, because a repository's text files are UTF-8.
  if [ -f "$c/utf8-refusal" ]; then
    rm -f "$work/out.json"
    printf '{"theorems": [{"name": "Top.A.\xff"}], "challenge_files": [{"path": "A.vo", "sha256": "%s"}]}\n' \
      "$(rocqchk -sha256 "$work/challenge/A.vo")" > "$work/bad-config.json"
    code=$(run_compare "$work" "$work/answer" "$work/bad-config.json" "$pre")
    [ "$code" != "0" ] || fail "$name: a config that is not UTF-8 was accepted"
    [ ! -f "$work/out.json" ] || fail "$name: a verdict file was written anyway"
    echo "  ok $name/refuse-invalid-utf8"
  fi

  rm -rf "$work"
  echo "ok $name"
}

# ------------------------------------------------- an answer without proofs
#
# A library built with -vos holds no opaque proof. The kernel reaches for a
# body that is not there and the run fails, so such an answer can never be
# graded. The sources are written here: a case directory would hold a tree
# that no other check uses.
case_vos() {
  local work
  work=$(mktemp -d)
  mkdir -p "$work/challenge" "$work/answer"
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof.' 'Admitted.' \
    > "$work/challenge/A.v"
  printf '%s\n' 'Definition two := 2.' 'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' \
    > "$work/answer/A.v"
  (cd "$work/challenge" && coqc -R . Top A.v)
  (cd "$work/answer" && coqc -R . Top -vos A.v)
  # The grader receives .vo files; a -vos build renamed to .vo is the shape
  # an answer without its proofs takes.
  mv "$work/answer/A.vos" "$work/answer/A.vo"
  local sha prelude_sha
  sha=$(rocqchk -sha256 "$work/challenge/A.vo")
  prelude_sha=$(rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.A.thm\"}], \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
  local code
  code=$(run_compare "$work" "$work/answer" "$work/config.json" "")
  [ "$code" != "0" ] || { cat "$work/log"; fail "vos: an answer without its proofs was graded"; }
  [ ! -f "$work/out.json" ] || fail "vos: a verdict file was written anyway"
  rm -rf "$work"
  echo "ok vos"
}

# ------------------------------- the two sides on different shared libraries
#
# The challenge and the answer must record the same digest for a pre-checked
# library. Here the answer is built against another copy of the shared
# library, so the digests differ and the run stops before the challenge
# reaches an environment.
case_digest() {
  local work
  work=$(mktemp -d)
  mkdir -p "$work/pre" "$work/pre2" "$work/challenge" "$work/answer"
  printf '%s\n' 'Definition shared_two : nat := 2.' > "$work/pre/Shared.v"
  printf '%s\n' 'Definition shared_two : nat := 2.' 'Definition extra : nat := 3.' \
    > "$work/pre2/Shared.v"
  (cd "$work/pre" && coqc -R . Pre Shared.v)
  (cd "$work/pre2" && coqc -R . Pre Shared.v)
  printf '%s\n' 'Require Import Pre.Shared.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$work/challenge/A.v"
  printf '%s\n' 'Require Import Pre.Shared.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' > "$work/answer/A.v"
  (cd "$work/challenge" && coqc -R . Top -R "$work/pre" Pre A.v)
  (cd "$work/answer" && coqc -R . Top -R "$work/pre2" Pre A.v)
  local sha pre_sha prelude_sha
  sha=$(rocqchk -sha256 "$work/challenge/A.vo")
  pre_sha=$(rocqchk -sha256 "$work/pre2/Shared.vo")
  prelude_sha=$(rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.A.thm\"}], \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}," \
    "   {\"library\": \"Pre.Shared\", \"sha256\": \"$pre_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
  local code
  code=$(run_compare "$work" "$work/answer" "$work/config.json" "$work/pre2")
  [ "$code" != "0" ] \
    || { cat "$work/log"; fail "digest: the two sides' shared libraries differ and the run passed"; }
  [ ! -f "$work/out.json" ] || fail "digest: a verdict file was written anyway"
  rm -rf "$work"
  echo "ok digest"
}

# ------------------- a pre-checked library under the answer's own root
#
# The challenge directory stands in for the answer's directory under each
# -R root. A pre-checked library may sit under that same root, in a
# directory of its own; the challenge directory must still stand in, or an
# honest answer cannot be graded at all.
case_sibling() {
  local work
  work=$(mktemp -d)
  mkdir -p "$work/shared" "$work/challenge" "$work/answer"
  printf '%s\n' 'Definition shared_two : nat := 2.' > "$work/shared/Lib.v"
  (cd "$work/shared" && coqc -R . Top Lib.v)
  printf '%s\n' 'Require Import Top.Lib.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$work/challenge/A.v"
  printf '%s\n' 'Require Import Top.Lib.' 'Definition two := shared_two.' \
    'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' > "$work/answer/A.v"
  (cd "$work/challenge" && coqc -R . Top -R "$work/shared" Top A.v)
  (cd "$work/answer" && coqc -R . Top -R "$work/shared" Top A.v)
  local sha lib_sha prelude_sha
  sha=$(rocqchk -sha256 "$work/challenge/A.vo")
  lib_sha=$(rocqchk -sha256 "$work/shared/Lib.vo")
  prelude_sha=$(rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.A.thm\"}]," \
    " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}," \
    "   {\"library\": \"Top.Lib\", \"sha256\": \"$lib_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"A.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
  set +e
  rocqchk -silent -R "$work/answer" Top -R "$work/shared" Top \
    -compare "$work/config.json" -challenge "$work/challenge" \
    -compare-out "$work/out.json" Top.A > "$work/log" 2>&1
  local code=$?
  set -e
  [ "$code" = "0" ] || { cat "$work/log"; fail "sibling: an honest answer exits $code"; }
  grep -q '"verdict":"pass"' "$work/out.json" \
    || { cat "$work/out.json"; fail "sibling: the honest answer did not pass"; }
  rm -rf "$work"
  echo "ok sibling"
}

# ------------------------- the answer libraries named only by -norec
#
# The grading side names each answer library with -norec and nothing
# positionally: check exactly these, load the rest. That selection must
# reach the same verdict as the positional one, so the case runs both
# forms over the same trees -- an honest answer, which must pass, and a
# wrong one, which must not. Before the fix of dispatch://BET-901 the
# -norec arm named no root for the challenge directory to stand in for,
# so the first challenge file failed to intern and no verdict was
# written at all.
#
# The libraries sit under a root with a dotted prefix and in
# subdirectories, the shape a task tree takes (-Q tree Top, Sub/B.v).
case_norec() {
  local work
  work=$(mktemp -d)
  local side
  for side in challenge answer bad; do
    mkdir -p "$work/$side/SubA" "$work/$side/SubB"
    printf '%s\n' 'Definition two : nat := 2.' > "$work/$side/SubA/Defs.v"
  done
  printf '%s\n' 'Require Import Top.SubA.Defs.' \
    'Theorem thm : two = 2.' 'Proof.' 'Admitted.' > "$work/challenge/SubB/Proof.v"
  printf '%s\n' 'Require Import Top.SubA.Defs.' \
    'Theorem thm : two = 2.' 'Proof. reflexivity. Qed.' > "$work/answer/SubB/Proof.v"
  # A wrong answer: the theorem is there under the right name, with another
  # statement. The comparator must not pass it.
  printf '%s\n' 'Require Import Top.SubA.Defs.' \
    'Theorem thm : two = two.' 'Proof. reflexivity. Qed.' > "$work/bad/SubB/Proof.v"
  for side in challenge answer bad; do
    (cd "$work/$side" && coqc -R . Top SubA/Defs.v) \
      || fail "norec: $side/Defs.v does not compile"
    (cd "$work/$side" && coqc -R . Top SubB/Proof.v) \
      || fail "norec: $side/Proof.v does not compile"
  done
  local spec_sha proof_sha prelude_sha
  spec_sha=$(rocqchk -sha256 "$work/challenge/SubA/Defs.vo")
  proof_sha=$(rocqchk -sha256 "$work/challenge/SubB/Proof.vo")
  prelude_sha=$(rocqchk -sha256 "$(prelude_vo)")
  printf '%s\n' \
    "{\"theorems\": [{\"name\": \"Top.SubB.Proof.thm\"}]," \
    " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
    " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
    " \"challenge_files\": [{\"path\": \"SubA/Defs.vo\", \"sha256\": \"$spec_sha\"}," \
    "   {\"path\": \"SubB/Proof.vo\", \"sha256\": \"$proof_sha\"}]}" > "$work/config.json"

  # <selection-form> <answer tree> -> prints the exit code, verdict in out.json
  norec_run() {
    local form=$1 tree=$2
    local sel=()
    case "$form" in
      norec) sel=(-norec Top.SubA.Defs -norec Top.SubB.Proof) ;;
      positional) sel=(Top.SubA.Defs Top.SubB.Proof) ;;
    esac
    rm -f "$work/out.json"
    set +e
    rocqchk -silent -Q "$tree" Top -compare "$work/config.json" \
      -challenge "$work/challenge" -compare-out "$work/out.json" "${sel[@]}" \
      > "$work/log" 2>&1
    local code=$?
    set -e
    echo "$code"
  }

  local form code
  for form in norec positional; do
    code=$(norec_run "$form" "$work/answer")
    [ "$code" = "0" ] || { cat "$work/log"; fail "norec/$form: the honest answer exits $code"; }
    [ -f "$work/out.json" ] || fail "norec/$form: no verdict file"
    grep -q '"verdict":"pass"' "$work/out.json" \
      || { cat "$work/out.json"; fail "norec/$form: the honest answer did not pass"; }
    code=$(norec_run "$form" "$work/bad")
    if [ "$code" = "0" ]; then
      grep -q '"verdict":"fail"' "$work/out.json" \
        || { cat "$work/out.json"; fail "norec/$form: the wrong answer did not fail"; }
    else
      [ ! -f "$work/out.json" ] || fail "norec/$form: a verdict file was written anyway"
    fi
    echo "  ok norec/$form"
  done
  rm -rf "$work"
  echo "ok norec"
}

# ---------------------------------------------------- the recorded forgeries
#
# Six proofs of False that a kernel defect once accepted (rocq#22378,
# #22383, #22391, #22675, the VM forgery of dispatch://BET-357 and the
# array forgery of dispatch://BET-630). The cut this branch sits on carries
# the fix for each, so none of them may reach a passing verdict. Three
# outcomes count as not-pass, and the case prints which one each takes:
# the forgery does not compile, rocqchk refuses it, or the verdict is fail.
#
# The trees are read-only recordings; COMPARE_FORGERIES points at them and
# the case is skipped where they are not mounted.
: "${COMPARE_FORGERIES:=/mnt/durable/sami/eval-driven-development/round4/verified-grading/wrong-answers-e2e/trees}"

case_forgeries() {
  if [ ! -d "$COMPARE_FORGERIES" ]; then
    echo "skip forgeries (no $COMPARE_FORGERIES)"
    return
  fi
  local f
  for f in os-22378 os-22383 os-22391 os-22675 os-vm357 os-parray630; do
    local src="$COMPARE_FORGERIES/$f/plain/Lib"
    [ -d "$src" ] || fail "forgeries: no $src"
    local work
    work=$(mktemp -d)
    mkdir -p "$work/challenge" "$work/answer"
    local side
    for side in challenge answer; do
      cp "$src/Forge.v" "$work/$side/Forge.v"
      [ -f "$src/hurkens.v" ] && cp "$src/hurkens.v" "$work/$side/hurkens.v"
    done
    printf '%s\n' 'Require Import Forge.' 'Theorem forged : False.' 'Proof.' 'Admitted.' \
      > "$work/challenge/Main.v"
    printf '%s\n' 'Require Import Forge.' 'Theorem forged : False.' \
      'Proof. exact contradiction. Qed.' > "$work/answer/Main.v"
    local order="Forge.v Main.v"
    [ -f "$src/hurkens.v" ] && order="hurkens.v Forge.v Main.v"
    local ok="" v
    for v in $order; do
      (cd "$work/challenge" && coqc -R . Top "$v") > "$work/cc" 2>&1 \
        || { ok="the challenge does not compile: $(grep -m1 -i error "$work/cc" | cut -c1-110)"; break; }
    done
    if [ -z "$ok" ]; then
      for v in $order; do
        (cd "$work/answer" && coqc -R . Top "$v") > "$work/ac" 2>&1 \
          || { ok="the answer does not compile: $(grep -m1 -i error "$work/ac" | cut -c1-110)"; break; }
      done
    fi
    if [ -z "$ok" ]; then
      local sha prelude_sha
      sha=$(rocqchk -sha256 "$work/challenge/Main.vo")
      prelude_sha=$(rocqchk -sha256 "$(prelude_vo)")
      printf '%s\n' \
        "{\"theorems\": [{\"name\": \"Top.Main.forged\"}]," \
        " \"tolerated_flags\": [{\"kind\": \"indices-not-mattering\", \"object\": \"Corelib.Init.Logic.eq\"}]," \
        " \"prechecked\": [{\"library\": \"Corelib.Init.Prelude\", \"sha256\": \"$prelude_sha\"}]," \
        " \"challenge_files\": [{\"path\": \"Main.vo\", \"sha256\": \"$sha\"}]}" > "$work/config.json"
      local libs=() g
      for g in "$work/answer"/*.vo; do libs+=("Top.$(basename "$g" .vo)"); done
      set +e
      rocqchk -silent -R "$work/answer" Top -compare "$work/config.json" \
        -challenge "$work/challenge" -compare-out "$work/out.json" "${libs[@]}" \
        > "$work/log" 2>&1
      local code=$?
      set -e
      if [ "$code" != "0" ]; then
        ok="rocqchk refuses it: $(grep -m1 -i error "$work/log" | cut -c1-110)"
      elif grep -q '"verdict":"fail"' "$work/out.json"; then
        ok="the verdict is fail"
      else
        cat "$work/out.json"
        fail "forgeries/$f: the forgery PASSES"
      fi
    fi
    echo "  ok forgeries/$f: $ok"
    rm -rf "$work"
  done
  echo "ok forgeries"
}

main() {
  if [ $# -gt 0 ]; then
    case "$1" in
      sha256) case_sha256 ;;
      vos) case_vos ;;
      digest) case_digest ;;
      sibling) case_sibling ;;
      norec) case_norec ;;
      forgeries) case_forgeries ;;
      *) run_case "$1" ;;
    esac
  else
    case_sha256
    local c
    for c in "$cases_dir"/*/; do
      run_case "$(basename "$c")"
    done
    case_vos
    case_digest
    case_sibling
    case_norec
    case_forgeries
  fi
}

main "$@"
