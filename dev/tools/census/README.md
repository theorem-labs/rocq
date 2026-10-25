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
means a proof that does it stores no term, with the reason in its record entry. Every row below is
implemented on this branch; the recorder is `lib/proof_recorder.ml`, and `rocq compile -proof-record`
writes the record (`lib/proof_record.mli` is the format). The `reason` column names the string the
record entry carries.
| Row | Channel | How it is recorded, or the check that makes a proof ineligible | Code |
|---|---|---|---|
| 1 | Global env: constants, inductives, constructors, projections, rewrite rules, modules, module types | Recorded: each lookup, with a digest of the value found, or absent. Channels `constant`, `constant_exists`, `rewrite_rules`, `inductive`, `inductive_exists`, `module`, `modtype`. Each key is digested once per compile and recorded once per proof | `kernel/environ.ml` `Recorded`, `lookup_constant[_opt\|_key]`, `mem_constant`, `lookup_rewrite_rules`, `lookup_mind_key`, `mem_mind`, `lookup_module`, `lookup_modtype` |
| 1 | Retroknowledge | In key item 2: only `Register` writes it, and the loaded libraries are part of the key | `vernac/proof_record_env.ml` `toolchain` |
| 2 | Universes, constraints, sort qualities | Recorded: one digest of the whole universe graph and one of the quality graph, at each proof's start (GRADE, 2026-10-24 05:09Z). Writes: the levels and constraints each declaration adds | `proof_record_env.ml` `read_at_start`; `vernac/declare.ml` `declare_constant` |
| 3 | Section context, variable opacity | Recorded: a digest of the named context and of `Decls.variable_opacity` over it, at each proof's start | `proof_record_env.ml` `read_at_start` |
| 4 | Typing flags, conversion oracle | Recorded: one digest of `Environ.typing_flags` at each proof's start. The oracle is a field of that record (`Environ.oracle env = (typing_flags env).conv_oracle`), so the digest covers every oracle query | `proof_record_env.ml` `read_at_start`; `kernel/environ.ml:324,329` |
| 5 | `simpl` behaviour | Recorded: each `ReductionBehaviour.get`, by constant | `pretyping/reductionops.ml` `ReductionBehaviour.get` |
| 6 | Nametabs | Recorded: each `locate`, `locate_upto`, `locate_all`, `of_path` and `exists`, in every nametab, with the value found or absent. The channel is the table's own summary name | `library/nametab.ml` `MakeImperative` |
| 7 | Hint databases | Recorded: each database the proof searches, by name, with a digest of that database. With `-proof-record-tables`, every database at the proof's start | `tactics/hints.ml` `searchtable_map`, `current_db`, `register_tables` |
| 8 | Typeclasses, instances | Recorded: the `classes` and `instances` tables, by name, with a digest, on each read. With `-proof-record-tables`, both at the proof's start | `pretyping/typeclasses.ml` `read_classes`, `read_instances`, `register_tables` |
| 9 | Ltac definitions and aliases | Recorded: each `interp_ltac`, `is_ltac_for_ml_tactic`, `interp_alias`, `check_alias`, by kernel name. The nametab lookup that finds the name is row 6; the ML tactic table is row 16 | `plugins/ltac/tacenv.ml` |
| 10 | Ltac2 definitions | Recorded: each `interp_global`, `interp_constructor`, `interp_projection`, `interp_type`, `interp_alias`, `interp_notation`, by kernel name. The primitive map is row 16 | `plugins/ltac2/tac2env.ml` `find` |
| 11 | Notations, scopes, number and string notations | Recorded: each `interp_notation` and each `interp_prim_token`, keyed by the notation and the open scopes, with a digest of the interpretation found. The scope stack is part of that key, so `find_scope` and `current_scopes` need no separate read | `interp/notation.ml` `record_notation`, `interp_prim_token_gen` |
| 12 | Implicit arguments, argument renaming | Recorded: each `Impargs.implicits_of_global`, with the renaming applied, so `Arguments_renaming.arguments_names` is inside the digest | `interp/impargs.ml` `implicits_of_global` |
| 13 | Options, option tables, `Set Warnings` | Recorded: one digest of `Goptions.get_tables ()` (every option's current value) and one of `CWarnings.get_flags ()`, at each proof's start | `proof_record_env.ml` `read_at_start` |
| 14 | Canonical structures, coercions, records | Recorded: the record-structure table by inductive, the canonical-solution table by projection, and the coercion graph, each with a digest, on each read | `pretyping/structures.ml` `Structure.find`, `mem`, `CanonicalSolution.find`; `pretyping/coercionops.ml` `lookup_path_between` |
| 15 | Autorewrite, Rocqlib, schemes, keys | Recorded: each rewrite base, each `lib_ref` and `lib_ref_opt`, each `DeclareScheme.lookup_scheme`, and the Keys table | `tactics/autorewrite.ml`, `library/rocqlib.ml`, `tactics/declareScheme.ml`, `pretyping/keys.ml` |
| 16 | ML-registered tables | In key item 2: the binary's digest, and every loaded plugin with its file digests, in load order. A table an ML module fills is fixed by those | `proof_record_env.ml` `toolchain`; `vernac/mltop.ml` `get_loaded_modules` |
| 17 | Fresh names | Composite of rows 1, 3, 6 and 20; the lexer keyword state is inside key item 1, the parsed sentences | `proof_record_env.ml`; `toplevel/vernac.ml` |
| 18 | Counters | Writes: the universe levels each declaration creates are recorded in order. A proof that advances a counter with no accessor is not separated from one that does not, so this row is the one the record states least precisely; P3 refuses a replay whose write set it cannot make again | `vernac/declare.ml` `declare_constant` |
| 19 | `Proof using` | Recorded: the declared set of section variables at the proof's start, absent when the proof declares none | `vernac/declare.ml` `record_using` |
| 20 | Lib state: module path, section prefix | Key item 3, in the `position` field. `module_path` is the path the `.glob` writes (sections excluded), `section_path` adds the open sections | `proof_record_env.ml` `position` |
| 21 | Commands inside a proof, `abstract`, Program obligations | Ineligible: a sentence that the classifier does not call a proof step (`command_in_proof`); an `abstract` or other sub-proof (`subproof`); a proof opened inside another (`nested_proof`) | `toplevel/vernac.ml`; `proofs/subproof.ml` `build_constant_by_tactic`; `lib/proof_recorder.ml` `open_proof` |
| 22 | Time and timeouts | Ineligible: every `Control.timeout`, which is the one point `Timeout`, `timeout` and Ltac2 `timeout` pass through (`timeout`) | `lib/control.ml` `timeout` |
| 23 | Files and external processes | Ineligible: `native_compute` (`native_compute`) and the external prover `csdpcert` that `psatz` calls (`external_prover`). Micromega's certificate caches are already blocked in grading | `kernel/nativelib.ml` `compile`; `plugins/micromega/coq_micromega.ml` `really_call_csdpcert` |
| 24 | Resource limits | Recorded in the header: `stack_limit` (in key item 2), `memory_cap`, `rlimit_as`, `rlimit_data`, `overcommit_memory`. The cap is recorded and never compared (GRADE, 12:19Z); replay is refused when an address-space limit is set or `overcommit_memory` is 2 | `lib/proof_limits.ml` |
| M1 | Abbreviations | Recorded: each `find_opt` and `find_interp`, by kernel name | `interp/abbreviation.ml` |
| M2 | Reserved types | Recorded: each `find_reserved_type`, by identifier root | `interp/reserve.ml` |
| M3 | Generalizable variables | Recorded: one digest of the table at each proof's start | `proof_record_env.ml`; `interp/implicit_quantifiers.ml` `generalizable_idents` |
| M4 | Schemes created (write) | Write: each scheme the proof created, by name | `tactics/ind_tables.ml` `define` |
| M5 | Universe constraint sources (write) | Write: the constant whose declaration wrote a constraint-source record | `vernac/declare.ml` `declare_constant` |
| M6 | `-skip-qed-typecheck` unchecked mark (write) | Not stored: replay writes the mark of the grade compile's own flags. The header records which flag the recording compile ran under, and `kernel_check` records whether the kernel typed each proof | `lib/proof_record.mli` `skip_qed_typecheck`, `kernel_check` |
| M7 | Template default levels | Recorded: one digest of the table at each proof's start | `proof_record_env.ml`; `engine/uState.ml` `template_default_univs` |
| S2.1 | Parser state, load paths, loaded libraries | In key item 2: every loaded library in load order with its `.vo` digest, and the safe-loaded ones. The grammar is inside key item 1, the parsed sentences | `proof_record_env.ml` `toolchain`; `vernac/library.ml` `library_digest`, `safe_loaded_libraries` |
| N1 | Printing state | Ineligible: Ltac2 `Message.to_string`, the one primitive that turns printed text into data (`message_to_string`) | `plugins/ltac2/tac2core.ml` |
| N2 | `stepl`/`stepr` lemmas | Ineligible: the tables are filled by the commands `Declare Left Step` and `Declare Right Step`, which inside a proof are already `command_in_proof`; a `stepl` whose table a later command changed is caught by key item 1, the parsed sentences, plus row 6 on the lemma it names | `toplevel/vernac.ml` |
| N3 | Prop inductives with dependent elimination | Recorded: each `is_prop_but_default_dependent_elim`, by inductive | `tactics/elimschemes.ml` |
| N4 | Default solver tactics | Recorded through row 13: `Obligation Tactic` and `Set Firstorder Solver` are options, and the digest of every option's value is taken at each proof's start | `proof_record_env.ml` `read_at_start` |
| N5 | smpl databases | Outside this tree: smpl is a pinned plugin. A `Smpl Add` inside a proof is `command_in_proof`; a database an earlier command changed is not yet recorded, so a smpl proof is left to P3's plugin check | smpl `src/smpl.mlg` |

Catch-all handlers (79 in Rocq, 7 in coqhammer, 2 in rocq-read-file):

| Disposition | Sites | Reason |
|---|---|---|
| Instrumented: ineligible when a critical exception is caught | `pretyping/evarconv.ml:282,285,1022`; `pretyping/evarsolve.ml:1786`; `tactics/equality.ml:466`. Each now tests `CErrors.noncritical` and marks the running proof, so the scan no longer lists it and its ruling is gone | reason `catchall` |
| Ineligible when the tactic appears | coqhammer `hhpartac.ml` (4): `best`, `sbest`, `hbest` | `parallel-race` |
| Ineligible when the command appears | rocq-read-file `read_file.ml:23,40`: `ReadFileBytes`, `ReadFileInt63`, `ReadFileString` | `readfile-command` |
| Ruled: allocation precondition | coqhammer `hammer_errors.ml` (2), `hhlib.ml` (1) | `allocation-precondition`, `string-prefix` |
| Ruled: no critical exception reaches it | guards on `noncritical`, `precatchable_exception`, `is_sync_anomaly` (33); `!Flags.in_debugger` (3); a specific exception (1) | `narrow-guard`, `debugger-only`, `specific-exception` |
| Ruled: re-raises | 18 | `reraises` (7), `reraises-annotated` (5), `reraised-by-caller` (4), `reraises-unless-noncritical` (1), `reraises-async` (1) |
| Ruled: outside elaboration | 24 | `driver` (13), `printing-only` (5), `external-process` (3), `error-printing` (2), `toplevel-convert` (1) |

## Status

- The census check, its tests, the rulings and the run output: commit `0cbbab654e`.
- The record format, its strict reader and the structural digest (`lib/proof_record.{ml,mli}`): commit
  `cdf4e081a7`.
- The recorder: `rocq compile -proof-record` and `-proof-record-tables`, every choke point of the table
  above, and the five instrumented handlers.
