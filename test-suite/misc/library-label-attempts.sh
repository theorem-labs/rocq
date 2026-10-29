#!/usr/bin/env bash
# Attempted-resolution records (vernac/attempts.ml) and the library label.
#
# Under -location-free-label, library Test.A attempts a resolution that leaves no dependency behind: a
# Require under Fail (binary-equivalence #861's reproduction: the library is
# absent when A is compiled and present later), a Require under Succeed
# (rolled back), a Load under Succeed, a plain Load, a Declare ML Module
# under Fail (no such plugin) and one under Succeed. Each case checks that
# A.vo records the attempt (rocq-library-label --attempts, and the same
# records as JSON with --attempts-json, read by Python's json module and
# checked against the schema documented in vernac/attempts.mli), and that
# when what the attempt found changes -- which files it resolved to, not
# their content, which left the key at label version 4 for a plugin
# (misc/library-label-plugin.sh) -- A compiled again is another library
# or no longer compiles: its stored digest, the label, changes
# (rocq-library-label --stored), and coqc and rocqchk -o refuse Test.B,
# compiled against the first A, over the new one. Compiling A twice in an
# unchanged tree gives the same label, and a library with no such attempt
# stores no record. With STOCK_BIN set to the bin directory of a stock build
# of the same base, that build's rocq and rocqchk do the refusing. Test.B is
# compiled by this rocq in either case: a stock coqc does not know the
# ATTEMPTS object kind, so it cannot load a library that holds one.

set -e

export PATH=$BIN:$PATH
LOAD=${STOCK_BIN:-$BIN}

. misc/library-label-tool.inc

mkdir -p misc/library-label-attempts
cd misc/library-label-attempts
rm -rf _test
mkdir _test
fail=0

comp() { # comp DIR FILE
  rocq c -q -location-free-label -R "_test/$1" Test "_test/$1/$2.v"
}
label() { "$TOOL" --stored "_test/$1/A.vo"; }
attempts() { "$TOOL" --attempts "_test/$1/A.vo"; }
setup() { mkdir -p "_test/$1"; printf '%b' "$2" > "_test/$1/A.v"; }
# dependent DIR: Test.B, compiled against the current Test.A of DIR.
dependent() {
  printf 'Require Test.A.\nDefinition b := 0.\n' > "_test/$1/B.v"
  comp "$1" B
}
# refused DIR: coqc and rocqchk -o refuse Test.B over the current Test.A.
refused() {
  printf 'Require Test.B.\n' > "_test/$1/C.v"
  ! "$LOAD"rocq c -q -R "_test/$1" Test "_test/$1/C.v" > "_test/$1/coqc.log" 2>&1 &&
    grep -q "makes inconsistent assumptions over library Test.A" "_test/$1/coqc.log" &&
    ! "$LOAD"rocqchk -silent -o -R "_test/$1" Test -norec Test.A -norec Test.B > "_test/$1/chk.log" 2>&1 &&
    grep -q "Inconsistent assumptions over module Test.A" "_test/$1/chk.log"
}
# json WHAT DIR CONDITION: the --attempts-json document of DIR's A.vo
# follows the schema of vernac/attempts.mli, and the Python CONDITION holds
# of it (j: the document, r: its record, sha: the SHA-256 of a file now).
cat > _test/attempts_json.py <<'PY'
import hashlib, json, re, sys
def valid(j):
    if set(j) != {"attempts_json_version", "record"} or j["attempts_json_version"] != 1:
        return False
    r = j["record"]
    if r is None:
        return True
    if set(r) != {"attempts", "digests", "loadpaths"} or not r["attempts"]:
        return False
    for lp in r["loadpaths"]:
        for e in lp:
            if not isinstance(e.get("dir"), str) or type(e.get("recursive")) is not bool: return False
            if not e["recursive"]:
                if set(e) != {"dir", "recursive"}: return False
            elif set(e) != {"dir", "recursive", "subdirs"}: return False
            elif e["subdirs"] is not None and not all(isinstance(s, str) for s in e["subdirs"]): return False
    for d in r["digests"]:
        if set(d) != {"file", "sha256"} or not isinstance(d["file"], str): return False
        if not re.fullmatch("[0-9a-f]{64}|unreadable", d["sha256"]): return False
    names = [d["file"] for d in r["digests"]]
    if names != sorted(set(names)): return False
    files = set(names)
    for a in r["attempts"]:
        if set(a) != {"request", "probes", "library", "found", "loadpath"}: return False
        q = a["request"]; k = q.get("kind")
        if k == "require_qualified":
            if set(q) != {"kind", "root", "name"} or not (q["root"] is None or isinstance(q["root"], str)): return False
        elif k in ("require_absolute", "load", "ml_module"):
            if set(q) != {"kind", "name"}: return False
        else:
            return False
        if not isinstance(q["name"], str): return False
        for p in a["probes"]:
            if set(p) != {"dir", "file", "exists"} or not isinstance(p["exists"], bool): return False
            if not isinstance(p["dir"], str) or not isinstance(p["file"], str): return False
        if not (a["library"] is None or isinstance(a["library"], str)): return False
        if not all(isinstance(f, str) and f in files for f in a["found"]): return False
        l = a["loadpath"]
        if type(l) is not int or (l == -1) != (k == "ml_module") or not (-1 <= l < len(r["loadpaths"])): return False
    return True
def sha(f):
    with open(f, "rb") as h: return hashlib.sha256(h.read()).hexdigest()
j = json.load(sys.stdin); r = j["record"]
sys.exit(0 if valid(j) and eval(sys.argv[1]) else 1)
PY
json() { # json WHAT DIR CONDITION
  local what=$1 dir=$2 cond=$3
  if "$TOOL" --attempts-json "_test/$dir/A.vo" > "_test/$dir/attempts.json" &&
     python3 _test/attempts_json.py "$cond" < "_test/$dir/attempts.json"; then echo "PASS $what"
  else echo "FAIL $what: $(cat "_test/$dir/attempts.json")"; fail=1; fi
}

# 0. No attempt that nothing else records: no record, a stock file.
setup none "Require Test.Y.\nDefinition a := Test.Y.y.\n"
printf 'Definition y := 0.\n' > _test/none/Y.v
comp none Y; comp none A
check "a plain Require stores no record" test "$(attempts none)" = "no attempts"
json "a plain Require: the JSON has no record" none 'r is None'

# 0b. Without -location-free-label, an attempt is not recorded: a stock file.
setup noflag "Fail Require Test.X.\nDefinition a := 0.\n"
rocq c -q -R _test/noflag Test _test/noflag/A.v
check "without the flag, no record" test "$(attempts noflag)" = "no attempts"
json "without the flag: the JSON has no record" noflag 'r is None'

# 1. Require under Fail of a library absent when A is compiled (#861).
setup fail "Fail Require Test.X.\nDefinition a := 0.\n"
comp fail A
r=$(attempts fail); echo "$r"
check "Fail Require: the attempt is recorded" has "$r" "an attempted Require of Test.X"
check "Fail Require: the record says X.vo was absent" has "$r" "fail/X.vo absent"
json "Fail Require: the JSON has the request, X.vo absent, no library, nothing read" fail \
  'any(a["request"]["kind"] in ("require_qualified", "require_absolute") and a["request"]["name"] == "Test.X"
       and any(p["dir"].endswith("fail") and p["file"] == "X.vo" and p["exists"] is False for p in a["probes"])
       and a["library"] is None and a["found"] == [] for a in r["attempts"])'
printf 'Definition x := 0.\n' > _test/fail/X.v
comp fail X
check "Fail Require: once X exists, A no longer compiles" bash -c "! rocq c -q -R _test/fail Test _test/fail/A.v > /dev/null 2>&1"

# 2. Require under Succeed: rolled back, so not a dependency of A.
setup succeed "Succeed Require Test.Y.\nDefinition a := 0.\n"
printf 'Definition y := 0.\n' > _test/succeed/Y.v
comp succeed Y; comp succeed A
r=$(attempts succeed); echo "$r"
check "Succeed Require: the attempt and the file it read are recorded" has "$r" "succeed/Y.vo sha256"
json "Succeed Require: the JSON has the library, the file read and its SHA-256, the load path searched" succeed \
  'any(a["library"] == "Test.Y" and len(a["found"]) == 1 and a["found"][0].endswith("succeed/Y.vo")
       and any(d["file"] == a["found"][0] and d["sha256"] == sha(a["found"][0]) for d in r["digests"])
       and any(e["dir"].endswith("succeed") for e in r["loadpaths"][a["loadpath"]])
       and any(p["exists"] is True and p["file"] == "Y.vo" for p in a["probes"]) for a in r["attempts"])'
d1=$(label succeed); comp succeed A; d2=$(label succeed)
check "Succeed Require: compiled again, nothing changed: the same label" test "$d1" = "$d2"
dependent succeed
printf 'Definition y := 1.\n' > _test/succeed/Y.v
comp succeed Y; comp succeed A
check "Succeed Require: the library changed: another label" test "$d1" != "$(label succeed)"
check "Succeed Require: coqc and rocqchk refuse the dependent" refused succeed

# 3. Load under Succeed.
setup succeedload "Succeed Load L.\nDefinition a := 0.\n"
printf 'Definition l := 0.\n' > _test/succeedload/L.v
comp succeedload A
r=$(attempts succeedload); echo "$r"
check "Succeed Load: the attempt and the file it read are recorded" has "$r" "succeedload/L.v sha256"
json "Succeed Load: the JSON has the Load and the file read" succeedload \
  'any(a["request"] == {"kind": "load", "name": "L.v"} and len(a["found"]) == 1
       and a["found"][0].endswith("succeedload/L.v") for a in r["attempts"])'
d1=$(label succeedload)
dependent succeedload
printf 'Definition l := 1.\n' > _test/succeedload/L.v
comp succeedload A
check "Succeed Load: the file changed: another label" test "$d1" != "$(label succeedload)"
check "Succeed Load: coqc and rocqchk refuse the dependent" refused succeedload

# 4. A plain Load: it leaves no object either.
setup load "Load L.\nDefinition a := l.\n"
printf 'Definition l := 0.\n' > _test/load/L.v
comp load A
check "Load: the attempt is recorded" has "$(attempts load)" "an attempted Load of L.v"
d1=$(label load)
dependent load
printf 'Definition l := 0.\n(* a comment *)\n' > _test/load/L.v
comp load A
check "Load: the file changed: another label" test "$d1" != "$(label load)"
check "Load: coqc and rocqchk refuse the dependent" refused load

# 5. Declare ML Module under Fail, of a plugin that does not exist.
setup failml "Fail Declare ML Module \"libkey_test_plugin\".\nDefinition a := 0.\n"
comp failml A
r=$(attempts failml); echo "$r"
check "Fail Declare ML Module: the attempt is recorded, nothing read" has "$r" "Declare ML Module of libkey_test_plugin: probes \[\] read \[\]"
d1=$(label failml)
dependent failml
mkdir -p _test/ocamlpath/libkey_test_plugin
printf 'plugin(byte) = "p.cma"\nplugin(native) = "p.cmxs"\n' > _test/ocamlpath/libkey_test_plugin/META
printf 'not a plugin' > _test/ocamlpath/libkey_test_plugin/p.cmxs
cp _test/ocamlpath/libkey_test_plugin/p.cmxs _test/ocamlpath/libkey_test_plugin/p.cma
OCAMLPATH="$PWD/_test/ocamlpath${OCAMLPATH:+:$OCAMLPATH}" comp failml A
check "Fail Declare ML Module: the plugin exists now: another label" test "$d1" != "$(label failml)"
check "Fail Declare ML Module: coqc and rocqchk refuse the dependent" refused failml

# 6. Declare ML Module under Succeed (rolled back): it resolves to other
# files. Their content is not in the key at label version 4; the files it
# resolved to are, and here they are another copy at another findlib path.
setup succeedml "Succeed Declare ML Module \"zarith\".\nDefinition a := 0.\n"
comp succeedml A
check "Succeed Declare ML Module: the plugin's files are recorded" has "$(attempts succeedml)" "zarith.cmxs sha256"
json "Succeed Declare ML Module: the JSON has the plugin, its files, no load path" succeedml \
  'any(a["request"] == {"kind": "ml_module", "name": "zarith"} and a["loadpath"] == -1
       and any(f.endswith("zarith.cmxs") for f in a["found"]) for a in r["attempts"])'
d1=$(label succeedml)
dependent succeedml
zdir=$(ocamlfind query zarith)
mkdir -p _test/zarith-changed
cp -r "$zdir" _test/zarith-changed/zarith
chmod -R u+w _test/zarith-changed
OCAMLPATH="$PWD/_test/zarith-changed${OCAMLPATH:+:$OCAMLPATH}" comp succeedml A
check "Succeed Declare ML Module: it resolved to other files: another label" test "$d1" != "$(label succeedml)"
check "Succeed Declare ML Module: coqc and rocqchk refuse the dependent" refused succeedml

# 7. The same source compiled three times, each time in a fresh directory at
# the same path, gets the same label, whatever else the working directory
# holds: the working directory is a load path entry that is not recursive
# (a subdirectory of it never becomes an entry), so its other subdirectories
# are no input. At 76d8b5da they were recorded, and a Fail Require library
# compiled in an end-to-end run whose working directory held fewer variant
# directories got another label (D18Mut's first run).
det() { # det SUBDIR...: Test.A compiled in a fresh _test/det/cwd/lib, from _test/det/cwd that also holds SUBDIRs
  rm -rf _test/det; mkdir -p _test/det/cwd/lib
  local s; for s in "$@"; do mkdir -p "_test/det/cwd/$s"; done
  printf 'Fail Require Test.Missing.\nDefinition a := 0.\n' > _test/det/cwd/lib/A.v
  (cd _test/det/cwd && rocq c -q -location-free-label -R lib Test lib/A.v)
  "$TOOL" --stored _test/det/cwd/lib/A.vo
}
l1=$(det); l2=$(det other); l3=$(det other more Third .hidden)
check "three fresh compiles at one path, other directories beside: one label ($l1 $l2 $l3)" \
  test "$l1" = "$l2" -a "$l2" = "$l3"
json "the JSON marks the working directory not recursive and lists no subdirectory of it" det/cwd/lib \
  '(any(e["dir"].endswith("det/cwd") and e["recursive"] is False for lp in r["loadpaths"] for e in lp)
    and any(e["dir"].endswith("det/cwd/lib") and e["recursive"] is True and e["subdirs"] == []
            for lp in r["loadpaths"] for e in lp))'
# A new subdirectory of a directory a recursive -R made an entry does become
# an entry (it is a library's directory at the next compile), so it is an
# input: the label changes. This is what the record of a recursive entry is
# for, and what a scan that reported no subdirectory at all would lose.
mkdir -p _test/det/cwd/lib/Sub
(cd _test/det/cwd && rocq c -q -location-free-label -R lib Test lib/A.v)
check "a new subdirectory under the -R root: another label" \
  test "$l3" != "$("$TOOL" --stored _test/det/cwd/lib/A.vo)"

exit $fail
