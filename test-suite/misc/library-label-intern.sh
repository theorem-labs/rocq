#!/usr/bin/env bash
# What interning a library's file writes to the tables of loaded libraries.
#
# A Require interns each library's file and fills tables that a [Fail] does not roll
# back (vernac/library.ml): the library's file name, its opaque table and opaque-proof
# handle and, under -location-free-label, its stored closures. They are filled only
# once the file is known to hold the library asked for, and only for the exact record
# [Library.intern_from_file] returned ([Library.Intern.t]'s contract).
#
# A findlib plugin built here, kfintern, reads two of them: KfLoadDirs prints the
# native compiler's load path, the directory of each loaded library's file as the
# file-name table holds it ([Nativelib.get_load_paths], [Library.get_used_load_paths]);
# KfShape prints what [Global.body_of_constant] reads for a constant (0 no body, 1 a
# constructor, 2 another term, Not_found when its library's opaque table is not
# there). KfRequire Same and KfRequire Copy require one library from one file through
# an [Intern.t] that returns the record intern_from_file returned, or a copy of it.
#
# A's `c : True` is proved by `exact I` (q1) or `exact (match tt with tt => I end)`
# (q2); X.vo is q2's A.vo at another logical path, Y.X.
# - I_fail: `Require A. Fail Require Y.X.` (X.vo holds A.A, so the Require fails, as
#   I_bad, the same Require without Fail, shows): the load path still names q1's
#   directory, never X.vo's;
# - I_same: KfRequire Same of q1's A: its directory is in the load path, and A.c's
#   body reads (shape 1);
# - I_copy: KfRequire Copy of q1's A breaks the contract, so nothing is filled: its
#   directory is not in the load path, and reading A.c's body fails with Not_found.

set -e
export PATH=$BIN:$PATH

cd misc
rm -rf _intern
mkdir -p _intern/{pkg/kfintern,q1,q2,x}
D=_intern

fail=0
pass() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
comp() { rocq c -q -location-free-label "$@"; }

# The plugin.
cat > $D/pkg/kfintern/META <<'EOF'
requires = "rocq-runtime.vernac"
plugin(native) = "p.cmxs"
EOF
cat > $D/pkg/kfintern/p.mlg <<'EOF'
DECLARE PLUGIN "kfintern"

{
open Names
open Stdarg

let dirpath s = DirPath.make (List.rev_map Id.of_string (String.split_on_char '.' s))

(* A [Library.Intern.t] that interns [file], whatever library it is asked
   for; with [copy], it returns a copy of the record [intern_from_file]
   returned, which the contract of [Intern.t] forbids. *)
let intern ~copy file _ =
  match Library.intern_from_file file with
  | Ok m, p when copy -> Ok (Obj.obj (Obj.dup (Obj.repr m))), p
  | r -> r

let require ~copy dp file =
  Library.require_library_syntax_from_dirpath ~cmd_safe:false ~intern:(intern ~copy file)
    [(None, dirpath dp)]

let shape s =
  match Nametab.global (Libnames.qualid_of_string s) with
  | GlobRef.ConstRef c ->
    (match Global.body_of_constant Library.indirect_accessor c with
     | None -> "0"
     | Some (b, _, _) -> if Constr.isConstruct b then "1" else "2"
     | exception Not_found -> "Not_found")
  | _ -> "not a constant"
}

VERNAC COMMAND EXTEND KfRequire CLASSIFIED AS SIDEFF
| [ "KfRequire" "Copy" string(dp) string(file) ] SYNTERP AS needed {
    require ~copy:true dp file
  } -> { Library.require_library needed }
| [ "KfRequire" "Same" string(dp) string(file) ] SYNTERP AS needed {
    require ~copy:false dp file
  } -> { Library.require_library needed }
END

VERNAC COMMAND EXTEND KfShow CLASSIFIED AS QUERY
| [ "KfShape" string(c) ] -> { Feedback.msg_notice Pp.(str "SHAPE " ++ str (shape c)) }
| [ "KfLoadDirs" ] -> {
    Feedback.msg_notice Pp.(str "DIRS " ++ str (String.concat ";" (!Nativelib.get_load_paths ())))
  }
END
EOF
( cd $D/pkg/kfintern && coqpp p.mlg > build.log 2>&1 &&
  ocamlfind ocamlopt -thread -shared -package rocq-runtime.vernac -o p.cmxs p.ml >> build.log 2>&1 ) ||
  { echo "FAIL cannot build the test plugin kfintern"; cat $D/pkg/kfintern/build.log; exit 1; }
export OCAMLPATH="$PWD/$D/pkg${OCAMLPATH:+:$OCAMLPATH}"

printf 'Lemma c : True.\nProof. exact I. Qed.\n' > $D/q1/A.v
printf 'Lemma c : True.\nProof. exact (match tt with tt => I end). Qed.\n' > $D/q2/A.v
comp -R $D/q1 A $D/q1/A.v
comp -R $D/q2 A $D/q2/A.v
cp $D/q2/A.vo $D/x/X.vo

# run NAME ARGS... -- LINES...: B.v of NAME holds `Declare ML Module "kfintern".` and
# LINES; it is compiled with ARGS; rc in NAME/rc, output in NAME/out.
run() {
  local name=$1 d=$D/$1; shift
  local args=()
  while [ "$1" != -- ]; do args+=("$1"); shift; done; shift
  mkdir -p $d
  printf '%s\n' 'Declare ML Module "kfintern".' "$@" > $d/B.v
  if comp "${args[@]}" -R $d Bdep $d/B.v > $d/out 2>&1; then echo ok > $d/rc; else echo failed > $d/rc; fi
}
# dirs NAME: the load path NAME's KfLoadDirs printed, one directory per line.
dirs() { sed -n 's/^DIRS //p' $D/$1/out | tr ';' '\n'; }
# has_dir NAME DIR: NAME's load path holds a directory that ends with DIR.
has_dir() { dirs $1 | grep -q -- "$2\$"; }

run I_fail -R $D/q1 A -Q $D/x Y -- 'Require A.' 'Fail Require Y.X.' 'KfLoadDirs.'
# I_bad: the same Require without Fail, to show why it fails.
run I_bad -R $D/q1 A -Q $D/x Y -- 'Require A.' 'Require Y.X.'
if [ "$(cat $D/I_fail/rc)" = ok ] && has_dir I_fail "$D/q1" && ! has_dir I_fail "$D/x" \
   && [ "$(cat $D/I_bad/rc)" = failed ] \
   && tr '\n' ' ' < $D/I_bad/out | grep -q 'contains library *A\.A *and not library *Y\.X'; then
  pass "I_fail: after Require A and a failed Require of a file that holds A.A, the load path names A's directory, not the file's: $(dirs I_fail | grep -- "$D" | tr '\n' ' ')"
else
  bad "I_fail ($(cat $D/I_fail/rc)): load path '$(dirs I_fail | tr '\n' ' ')': $(tr '\n' ' ' < $D/I_fail/out | cut -c1-400); I_bad ($(cat $D/I_bad/rc)): $(tr '\n' ' ' < $D/I_bad/out | cut -c1-300)"
fi

run I_same -- "KfRequire Same \"A.A\" \"$PWD/$D/q1/A.vo\"." 'KfLoadDirs.' 'KfShape "A.c".'
if [ "$(cat $D/I_same/rc)" = ok ] && has_dir I_same "$D/q1" && grep -q '^SHAPE 1$' $D/I_same/out; then
  pass "I_same: through an Intern.t that returns intern_from_file's record, A's directory is in the load path and A.c's body reads"
else
  bad "I_same ($(cat $D/I_same/rc)): load path '$(dirs I_same | tr '\n' ' ')': $(tr '\n' ' ' < $D/I_same/out | cut -c1-400)"
fi

run I_copy -- "KfRequire Copy \"A.A\" \"$PWD/$D/q1/A.vo\"." 'KfLoadDirs.' 'KfShape "A.c".'
if [ "$(cat $D/I_copy/rc)" = ok ] && ! has_dir I_copy "$D/q1" && grep -q '^SHAPE Not_found$' $D/I_copy/out; then
  pass "I_copy: through an Intern.t that returns a copy of the record, nothing is filled: A's directory is not in the load path, and A.c's body does not read (Not_found)"
else
  bad "I_copy ($(cat $D/I_copy/rc)): load path '$(dirs I_copy | tr '\n' ' ')': $(tr '\n' ' ' < $D/I_copy/out | cut -c1-400)"
fi

exit $fail
