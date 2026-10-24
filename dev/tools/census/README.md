# Census check for per-proof replay

Per-proof replay (dispatch://BET-84) lets the grade compile reuse a proof term that the registration
compile stored, and skip the proof's tactics. The term is used only when every input the proof read has
the same value. The inputs are listed in the channel census, CHANNELS.md (`sami-rocqperf
/mnt/nvme/sami/speed/coord/reuse/CHANNELS.md`, research on Rocq 459869e3c2). GRADE's review added rows
M1-M7.

This directory holds gate part 1 ("every channel is covered"):

- `census_check.py`: lists every site in a source tree that can hold state a proof reads, and every
  exception handler that can turn a critical exception into a different term. It fails when a site has
  no census row or written ruling, or when a ruling names a site that no longer exists.
- `rulings/*.json`: one rulings file per audited source tree. Each file names the commit it was audited
  at.
- `output/*.txt`: the `--list` output of each run at the audited commits.
- The table below maps each census row to the code that records it, or to the check that makes a
  proof ineligible.

## Running it

```sh
python3 dev/tools/census/census_check.py --root . --rulings dev/tools/census/rulings/rocq.json
python3 dev/tools/census/census_check.py --root <coqhammer checkout> --rulings dev/tools/census/rulings/coqhammer.json
python3 dev/tools/census/census_check.py --root <smpl checkout> --rulings dev/tools/census/rulings/smpl.json
python3 dev/tools/census/census_check.py --root <rocq-read-file checkout> --rulings dev/tools/census/rulings/rocq-read-file.json
python3 -m unittest discover -s dev/tools/census     # the script's own tests
```

Exit status: 0 when every site is ruled, 1 when a site is `UNMAPPED` or a ruling is `STALE` or
`INVALID` (one line each on stdout), 2 on a usage or read error. `--list` prints every site with its
disposition. Python 3.8+, standard library only. The fork's CI runs the Rocq check and the tests
(`.github/workflows/ci-github.yml`, job `census`). binary-equivalence-taiga's `test-scripts` job runs the
three plugin checks against the pins in `harness/toolchains/9.2/rocq-verify-harness.opam` and
`Dockerfile`.

## What it lists

| Kind | Sites |
|---|---|
| `summary` | `Summary.ref`, `Summary.ref_tag`, `Summary.declare_summary[_tag]`, `Summary.declare_ml_modules_summary`, `Summary.MakeObservable` |
| `object` | `declare_object`, `declare_object_full`, `declare_named_object[_full\|_gen]` (Libobject) |
| `nosummary-option` | `declare_option ~no_summary:true` (an option outside the Summary) |
| `summary-open` | `open Summary`, `include Summary` or `module X = Summary`, which could hide registrations from the scan |
| `catchall` | `with _ ->`, `\| _ ->` in a `try`, `\| exception _ ->`, or a named handler that does not test `CErrors.noncritical` and does not end by re-raising the caught exception unchanged |

A site key has no line number: `<kind>:<path>:<name>`. The name is the registered string for Summary,
object and option sites. For a catch-all it is the enclosing top-level binding plus the handler's
pattern and the start of its body. A repeated key gets a suffix `#2`, `#3`. So a key survives edits that
move lines, and changes when the handler itself changes.

The scan follows OCaml lexing: nested comments, strings, quoted strings and character literals. It does
not parse OCaml. It lists each of the six handlers the plan names (`pretyping/evarsolve.ml:1786`,
`pretyping/evarconv.ml:285,1022`, `tactics/equality.ml:466`, `stm/stm.ml:779`, `vernac/topfmt.ml:460`).
Every line that `git grep -E 'with +_ *->|with +(e|exn|any|ex|err|_e|reraise) *->'`
finds and the scan does not list was read by hand at 03d5bb248e. Each is either an `MEwith _` match arm
or a handler that re-raises the caught exception.

Rulings take one of three forms: `{"row": "<census row>"}`, `{"ruling": "<reason>"}` (a written ruling,
for example that no tactic reaches the site), or `{"ineligible": "<reason>"}` (a proof that reaches the
site stores no term). `@name` refers to an entry in the file's `reasons` object.

## Audited trees

| Tree | Commit | Scope | Sites | Result |
|---|---|---|---|---|
| theorem-labs/rocq | 03d5bb248e (9.2/qed-skip-typecheck) | every directory linked into `rocq compile` or a plugin it loads | 269: summary 104, object 78, nosummary-option 3, catchall 84 | 0 problems |
| coqhammer (coq-hammer-tactics 1.3.2+9.2) | 1d581299c2 | `src/lib`, `src/tactics` (the installed package; `src/plugin` is not installed) | 7 catchall | 0 problems |
| smpl (rocq-smpl.dev) | 1c3578c1f6 | `src` | summary 1, object 1 | 0 problems |
| rocq-read-file 0.0.2 | 68887ad0c3 | `src` | 2 catchall | 0 problems |

## Census rows not in CHANNELS.md

The scan found tables that a tactic reads and that CHANNELS.md does not list. They get rows N1-N5 here.

| Row | What is read | Where |
|---|---|---|
| N1 | Printing state: notation uninterpretation (`interp/notationextern.ml:241`), printing rules (`printing/ppextend.ml:79,82`), Ltac notation printing (`plugins/ltac/pptactic.ml:71`). A tactic's result depends on it only when printed text becomes data: Ltac2 `Message.to_string` (`plugins/ltac2/tac2core.ml:194`). | `Message.to_string` |
| N2 | `stepl`/`stepr` lemmas (`Declare Left Step`, `Declare Right Step`): `"transitivity-steps-l"`, `"transitivity-steps-r"` | `plugins/ltac/extratactics.mlg:377-398` |
| N3 | Inductives whose case analysis is dependent by default although they are in Prop: `"PROP-BUT-DEFAULT-DEPENDENT-ELIM"` | `tactics/elimschemes.ml:24-49`, read by `destruct`, `case` and scheme lookup |
| N4 | Default solver tactics: `Obligation Tactic` (`vernac/g_obligations.mlg:21-30`) and `Set Firstorder Solver` (`plugins/firstorder/g_ground.mlg:37-65`) | `vernac/tactic_option.ml:51-90` |
| N5 | smpl databases (`Smpl Create`, `Smpl Add`), read by the `smpl` tactic | smpl `src/smpl.mlg:36-145` |

## Census row table

"Recorded" means the record holds a read with its key and value digest, at the code named. "Ineligible"
means a proof that does it stores no term, with the reason in its record entry. Where a row says
"proposed", the code is a later commit on this branch. Its status is in the last column.

| Row | Channel | How it is recorded or made ineligible | Census sites |
|---|---|---|---|
| 1 | Global env: constants, inductives, constructors, projections, rewrite rules, modules, module types | Each lookup, with a digest of the value: `Environ.lookup_constant[_opt\|_key]`, `lookup_mind[_key]`, `lookup_rewrite_rules`, `lookup_module`, `lookup_modtype` (`kernel/environ.ml`). Retroknowledge: a digest in key item 2 | `library/global.ml` `global_env`; objects `CONSTANT`, `INDUCTIVE` |
| 2 | Universes, constraints, sort qualities | One digest of the whole universe graph and quality graph at the proof's start (GRADE, 2026-10-24 05:09Z) | inside `global_env` |
| 3 | Section context, variable opacity | Digest of the named context and `Decls.variable_opacity` at `Declare.initialize_named_context_for_proof` (`vernac/declare.ml:1815`) | `"VARIABLE"` summary and object |
| 4 | Typing flags, conversion oracle | Digest of `Environ.typing_flags` at proof start; each `Conv_oracle.get_strategy` and `get_transp_state` query | object `STRATEGY` |
| 5 | `simpl` behaviour | Each `ReductionBehaviour.get` (`pretyping/reductionops.ml:186`) | `"reductionbehaviour"`, `REDUCTIONBEHAVIOUR` |
| 6 | Nametabs | Each `locate`, `locate_all`, `exists`, `shortest_qualid` in the `Nametab` tables, a failed lookup recorded as absent | nametab `the_tab`, `warntab`; objects `EXPORTNAMES`, universe and sort name states |
| 7 | Hint databases | Each database the proof searches, by name, with a digest of that database, at `Hints.searchtable_map`, `current_db`, `current_pure_db`, `make_db_list` (`tactics/hints.ml:843-855,1592`) | `"searchtable"`, `HINT-COUNTER`, `AUTOHINT_DB`, `AUTOHINT` |
| 8 | Typeclasses, instances, typeclass solvers | Each table the proof reads, by name, with its digest, at `Typeclasses.class_info`, `instances_of`, `all_instances` (`pretyping/typeclasses.ml:83-179`); `typeclass_instances` through row 7 | `"classes"`, `"instances"`, `autogoal_cache`, `typeclass_solvers`, objects from `vernac/classes.ml` |
| 9 | Ltac definitions, Tactic Notation | Each lookup at `Tacenv.interp_ltac`, `interp_alias`, `check_alias`, `locate_tactic` (`plugins/ltac/tacenv.ml:29-122`); ML tactics by row 16 | `tactic-alias`, `tactic-definition`, `TACTIC-NOTATION-COUNTER`, Tactic grammar objects |
| 10 | Ltac2 definitions | Each lookup at `Tac2env.interp_global`, `interp_constructor`, `interp_projection`, `interp_type`, `interp_notation`, `interp_primitive` (`plugins/ltac2/tac2env.ml:84-151`) | `ltac2-state`, `ltac2-notations`, `TAC2-*` objects; `ltac2-compiled-state` ruled a derived cache |
| 11 | Notations, scopes, delimiters, argument scopes, number and string notations | Each lookup at `Notation.interp_notation`, `interp_prim_token`, `find_scope`, `current_scopes`, `find_delimiters_scope` (`interp/notation.ml`) | `"symbols"`, `LOCAL-CUSTOM-ENTRY`, notation objects |
| 12 | Implicit arguments, argument renaming, bidirectionality hints | Each lookup at `Impargs.implicits_of_global`, `Arguments_renaming.arguments_names`, the bidirectionality-hint lookup | `implicits`, `section-implicits`, `rename-arguments`, `bidirectionalityhints` |
| 13 | Options and option tables; `Set Warnings` | A digest of every option's value and every option table at proof start (options have no single read point) | `goptions.ml` declare and table sites; SSR option refs |
| 14 | Canonical structures, coercions, records, hooks | Each table the proof reads, by name, with its digest: `Structures.*.find`, `CanonicalSolution.find`, `Coercionops.lookup_path_between`, `class_info`, `coercion_info` | record and coercion tables, `canonical_solution_hooks_hacked`, `coercion_hooks`, `PRIMPROJS`, `STRUCTURE` |
| 15 | Rewrite and plugin tables | Each table the proof reads, by name, with its digest: `Autorewrite.find_rewrites`, `Ring.find_ring_structure`, zify `init_cache`, `Rocqlib.lib_ref`, `DeclareScheme.lookup_scheme`, `Keys`, funind and SSR view tables | 24 sites |
| 16 | ML-registered tables | The binary and every loaded plugin, with load order, in key item 2 | `inited-plugins`, ML-modules summary, `ML-MODULE` |
| 17 | Fresh names | Composite of rows 1, 3, 6 and 20; the lexer keyword state is in the parsed sentences (key item 1) | `GRAMMAR_LEXER` |
| 18 | Evar, meta, universe and SSR counters | Writes: the advance of each counter (counter totals) | evar and meta counters, `SSR:abstractid` |
| 19 | `Proof using` | The declared set and the named collections it uses | `proofusing-nameset` |
| 20 | Lib state: module path, section prefix | Key item 3 | outside the Summary |
| 21 | Opaque table, proof stack, Program obligations | Ineligible: a command inside the proof, or `abstract`, found in the parsed sentences | outside the Summary |
| 22 | Time and timeouts | Ineligible: `Timeout`, `Time`, Ltac2 `timeout` in the parsed sentences | |
| 23 | Files and external processes | Ineligible: `psatz` with an external prover, `native_compute`; micromega caches are already blocked in grading | `NATIVE-LIBRARY-LOAD` ruled |
| 24 | Resource limits | Stack limit in key item 2; memory cap recorded outside the key (GRADE, 12:19Z); `RLIMIT_AS`, `RLIMIT_DATA` and `vm.overcommit_memory` recorded, and replay refused with an address-space limit | |
| M1 | Abbreviations | Each lookup in `interp/abbreviation.ml` | `ABBREVIATIONS`, `ABBREVIATION` |
| M2 | Reserved types | Each `Reserve.find_reserved_type` (`interp/reserve.ml:108`) | `reserved-type`, `reserved-type-rev` |
| M3 | Generalizable variables | One digest of `"generalizable-ident"` | summary and object |
| M4 | Schemes created (write) | The schemes the proof created | object `SCHEME` |
| M5 | Universe constraint sources (write) | The record the declaration writes | summary and object |
| M6 | `-skip-qed-typecheck` unchecked mark (write) | Not stored: replay writes the mark of the grade compile's flags | |
| M7 | Template default levels | One digest of `"template default univs"` | summary and object |
| S2.1 | Parser state, load paths, loaded libraries | Load paths and loaded libraries in key item 2; the grammar in the parsed sentences (key item 1) | 13 sites |
| N1 | Printing state | Ineligible: Ltac2 `Message.to_string` in the parsed sentences | 4 sites |
| N2 | `stepl`/`stepr` lemmas | Each table read, with its digest, at `step` (`plugins/ltac/extratactics.mlg:383`) | 3 sites |
| N3 | Prop inductives with dependent elimination | Each `is_prop_but_default_dependent_elim` query (`tactics/elimschemes.ml:38`) | 2 sites |
| N4 | Default solver tactics | A digest of each default tactic at proof start | 2 sites |
| N5 | smpl databases | Each database the `smpl` tactic reads, by name, with its digest | 2 sites (smpl) |

Catch-all handlers (84 in Rocq, 7 in coqhammer, 2 in rocq-read-file):

| Disposition | Sites | Reason |
|---|---|---|
| Ineligible when a critical exception is caught | `pretyping/evarconv.ml` `decompose_proj` (2), `evar_eqappr_x`; `pretyping/evarsolve.ml` `invert_definition`; `tactics/equality.ml` `lookup_eq_eliminator_opt` | `critical-caught` |
| Ineligible when the tactic appears | coqhammer `hhpartac.ml` (4): `best`, `sbest`, `hbest` | `parallel-race` |
| Ineligible when the command appears | rocq-read-file `read_file.ml:23,40`: `ReadFileBytes`, `ReadFileInt63`, `ReadFileString` | `readfile-command` |
| Ruled: allocation precondition | coqhammer `hammer_errors.ml` (2), `hhlib.ml` (1) | `allocation-precondition`, `string-prefix` |
| Ruled: no critical exception reaches it | guards on `noncritical`, `precatchable_exception`, `is_sync_anomaly` (33); `!Flags.in_debugger` (3); a specific exception (1) | `narrow-guard`, `debugger-only`, `specific-exception` |
| Ruled: re-raises | 18 | `reraises` (7), `reraises-annotated` (5), `reraised-by-caller` (4), `reraises-unless-noncritical` (1), `reraises-async` (1) |
| Ruled: outside elaboration | 24 | `driver` (13), `printing-only` (5), `external-process` (3), `error-printing` (2), `toplevel-convert` (1) |

## Status

- This commit: the census check, its tests, the rulings and the run output.
- Later commits on this branch: the recorder (`rocq compile` option, record format, the choke points above),
  and the instrumentation of the five `critical-caught` handlers. When a handler is instrumented, its entry
  turns `STALE` and is removed in the same commit.
