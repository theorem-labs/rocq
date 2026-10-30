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
- `rulings/*.json`: one rulings file per audited source tree, and `rulings/channels.json` for the
  recorder's read sites in the Rocq tree. Each file names the commit it was audited at.
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

The same command also checks the recorder's own read sites. It lists every `Proof_recorder.read`,
`read_by` and `ineligible` call and every `register_tables` record, keyed
`read:<path>:<row>/<channel>` or `ineligible:<path>:<reason>`, and checks them against
`rulings/channels.json` (`--channels` names another file; by default it is the `channels.json` beside
the rulings file, when that file names the same `source`). A new channel, or an existing channel read
in a new file, must add `{"row": "<row the code passes>"}` there, and a new reason must add
`{"ineligible": "@<reason>"}` with its text in `reasons`; else the check reports `UNMAPPED`, and an
entry whose site is gone reports `STALE`.

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
| `read` | `Proof_recorder.read`, `Proof_recorder.read_by`, and a record with `row` and `channel` fields or an update that sets one (the `register_tables` entries); checked against `rulings/channels.json` |
| `ineligible` | `Proof_recorder.ineligible`, and a record with `reason` and `detail` fields; checked against `rulings/channels.json` |
| `recorder-open` | `open Proof_recorder`, `include`, `module X = Proof_recorder` or `Proof_recorder.( ... )`, which could hide reads from the scan |

A site key has no line number: `<kind>:<path>:<name>`. The name is the registered string for Summary,
object and option sites. For a catch-all it is the enclosing top-level binding plus the handler's
pattern and the start of its body. A repeated key gets a suffix `#2`, `#3`. So a key survives edits that
move lines, and changes when the handler itself changes. A `read` site's name is `<row>/<channel>` and an
`ineligible` site's name is the reason, one key per file. When a wrapper of the same file takes the row,
channel or reason as a parameter, the scan follows each call of the wrapper to the literal it passes. A
value that is still not a literal is named by its enclosing binding and the expression as written.

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
| theorem-labs/rocq, recorder read sites (`rulings/channels.json`) | the commit that last changed `rulings/channels.json` (`git log -1 -- dev/tools/census/rulings/channels.json`), a child of e16e9d2ae4 on 9.2/proof-replay | the same | 100: read 76, ineligible 24 | 0 problems |
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

"Recorded" means the record holds a read with its key and value digest, at the code named.
"Ineligible" means a proof that does it stores no term, with the reason in its record entry. Every row
below is implemented on this branch; the recorder is `lib/proof_recorder.ml`, and
`rocq compile -proof-record` writes the record (`lib/proof_record.mli` is the format). The `reason`
column names the string the record entry carries.

A read is recorded either at its choke point, keyed by what it asks for, or as one digest of the whole
table at each proof's start. The second is coarser: the proof then depends on a table it may not have
read. It is the answer for a table with many read points, or with read points behind a process-wide
cache that no choke point can reach (a `lazy` of a `lib_ref`). Those reads go in the proof's
`start_tables`, which a matcher compares exactly like `reads`; the sources register with
`Proof_recorder.register_tables`.
| Row | Channel | How it is recorded, or the check that makes a proof ineligible | Code |
|---|---|---|---|
| 1 | Global env: constants, inductives, constructors, projections, rewrite rules, modules, module types | Recorded: each lookup, with a digest of the value found, or absent. Channels `constant`, `constant_exists`, `rewrite_rules`, `inductive`, `inductive_exists`, `module`, `modtype`. An object of a REQUIRED library is recorded by that library's `.vo` digest, which pins every object the library holds; only the objects of the library being compiled are digested. A constant's rewrite rules are digested either way: the file being compiled can add a rule to a symbol of a required library. Each key is recorded once per proof | `kernel/environ.ml` `Recorded`, `lookup_constant[_opt\|_key]`, `mem_constant`, `lookup_rewrite_rules`, `lookup_mind_key`, `mem_mind`, `lookup_module`, `lookup_modtype` |
| 1 | Retroknowledge | In key item 2: only `Register` writes it, and the loaded libraries are part of the key | `vernac/proof_record_env.ml` `toolchain` |
| 2 | Universes and constraints | Recorded once per proof, at `Qed`: the proof's footprint (every level a universe-graph check, enforcement or addition names while the proof is recorded) and the order the start-of-proof global graph induces on its global levels, compared pairwise with universe checking on (a graph under `Unset Universe Checking` proves every constraint, and a proof can check its own against it), with the graph's checking mode beside it. A whole-graph query on the global graph, or more than 64 global levels, records the whole graph's digest instead. The starting universe state (local levels and constraints, unification variables, local qualities, minimization hints) is in the statement key. The quality graph remains a whole start read. Writes: the levels and constraints each declaration adds | `kernel/uGraph.ml` query hook; `proof_record_env.ml` `note_universe_query`, `record_universe_footprint`; `declare.ml` `start_proof_core`; `vernac/declare.ml` `declare_constant` |
| 3 | Section context, variable opacity | Recorded: a digest of the named context and of `Decls.variable_opacity` over it, at each proof's start | `proof_record_env.ml` `read_at_start` |
| 4 | Typing flags, conversion oracle | Recorded: one digest of `Environ.typing_flags` at each proof's start. The oracle is a field of that record (`Environ.oracle env = (typing_flags env).conv_oracle`), so the digest covers every oracle query | `proof_record_env.ml` `read_at_start`; `kernel/environ.ml:324,329` |
| 5 | `simpl` behaviour | Recorded: each `ReductionBehaviour.get`, by constant, and one digest of the whole database at each proof's start. `simpl` does not use the wrapper: it takes the raw table with `Db.get`, reads the whole never-unfold set and calls `get_from_db`, so only the table read covers it | `pretyping/reductionops.ml` `ReductionBehaviour.get`, `register_tables`; `pretyping/tacred.ml:662,722-738,871` |
| 6 | Nametabs | Recorded: each `locate`, `locate_upto`, `locate_all`, `of_path` and `exists`, in every nametab, with the value found or absent, and one digest of each warning table (`xrefwarntab`, `ltac2-ctortab-warnings`) at each proof's start. The channel is the table's own summary name. The warning tables are the reason a constant that gains `#[deprecated]` changes nothing else: its type, its body and its name are the same, and a later proof that names it errors under `Set Warnings "+deprecated-reference"`. The record's lookup is the same one the caller gets, so a legacy-path warning is printed once | `library/nametab.ml` `MakeImperative`, `MakeWarned`, `register_tables` |
| 7 | Hint databases | Recorded: each database the proof searches, by name; the domain of the database set at each `auto with *`/`autounfold` enumeration (key `*domain`); and every database at each proof's start. The digest is of an IMMUTABLE SUMMARY of the database, not of the database value: the transparent state, the cut path, the unfold sets, the next hint id, the `use_dn` flag, the name, and per entry the `KerName.Set.t` of hint uids and the modes. Every hint has a fresh uid from `HINT-COUNTER`, assigned by the same command sequence in the same order, so the uid set identifies the hints. The summary leaves out `sentry_bnet`, the discrimination net, which a lookup fills IN PLACE inside the same database value and which is a cache, not state | `tactics/hints.ml` `Hint_db.digest`, `searchtable_map`, `current_db`, `current_db_names`, `register_tables` |
| 8 | Typeclasses, instances | Recorded: the `classes` and `instances` tables, by name, with a digest, on each read and at each proof's start, plus the list of ACTIVE typeclass solvers (key `active`). Ineligible: a resolution that asks an active solver (`plugin_hook`, detail `typeclass_solver: <names>`). A solver and its condition are plugin closures, and what they do can depend on plugin state that neither their name nor the plugin's files fix (rocq-elpi's TC solver reads its mode table and runs its accumulated program). Rocq registers no solver, so a stock compile reads the empty list | `pretyping/typeclasses.ml` `read_classes`, `read_instances`, `register_tables`; `tactics/class_tactics.ml` `find_solver` |
| 9 | Ltac definitions and aliases | Recorded: each `interp_ltac`, `is_ltac_for_ml_tactic`, `interp_alias`, `check_alias`, by kernel name. The nametab lookup that finds the name is row 6; the ML tactic table is row 16 | `plugins/ltac/tacenv.ml` |
| 10 | Ltac2 definitions | Recorded: each `interp_global`, `interp_constructor`, `interp_projection`, `interp_type`, `interp_alias`, `interp_notation`, by kernel name (as `Lib.kername_key` writes it: `KerName.to_string` is not injective), and the same read when the compiled-global cache HITS, which returns a value without asking the table. The recorded value is the source definition, never the compiled `valexpr`, which holds closures. The primitive map is row 16. Replay: each of the six channels has an evaluator that reads the name back (`Lib.kername_of_key`) and digests the table entry with the record sites' `recorded_ltac2` | `plugins/ltac2/tac2env.ml` `find`, `record_global`; `plugins/ltac2/tac2interp.ml` `eval_global` |
| 11 | Notations, scopes, number and string notations | Recorded: each `interp_notation` and each `interp_prim_token`, the failing lookup included, under a key that encodes the whole query injectively, with its length prefixes: the entry (`InConstrEntry`, or `InCustomEntry` with its name as `Lib.kername_key` writes it), the notation text, and every scope item in order. The value holds the interpretation and `not_user_warns`, so a notation that gains `#[deprecated]` changes it. A number's value is the term and scope it is read as, with the compiled file's locations left out (every node carries the token's location, which the key does not hold). The scope SELECTION is recorded on its own: the scope stack (key `scopes`), each delimiter lookup, and each `find_arguments_scope`, so an `Open Scope`, a delimiter reassignment or an `Arguments ... %scope` is seen although the parsed sentence does not move. Replay: the `notation` evaluator reads the query back from its key (`notation_query_of_key`) and asks it again (`find_notation_interpretation`); the `prim_token` evaluator reads a term query back and asks it again at a location of the compiled file, with the universe counters put back and no warning printed (`replay_prim_token_query`); a pattern query, whose answer also depends on its caller's check, is a miss | `interp/notation.ml` `current_scopes`, `interp_notation`, `interp_prim_token_gen`, `find_delimiters_scope`, `find_arguments_scope` |
| 12 | Implicit arguments, argument renaming, bidirectionality | Recorded: each `Impargs.implicits_of_global` with the renaming applied; each `Arguments_renaming` read at its own accessor, by reference, so the consumers that do not pass through `impargs` (inductive elaboration, SSR elimination) are covered; and each `get_bidirectionality_hint`, which decides how many arguments are typed before the expected type is used. Replay: `Arguments_renaming.globref_of_string` reads each key back, a variable's (section variable or hypothesis) as its name | `interp/impargs.ml` `implicits_of_global`; `pretyping/arguments_renaming.ml`; `pretyping/pretyping.ml` |
| 13 | Options, option tables, `Set Warnings` | Recorded: one digest of `Goptions.get_tables ()` (every option's current value) and one of `CWarnings.get_flags ()`, at each proof's start | `proof_record_env.ml` `read_at_start` |
| 14 | Canonical structures, coercions, records | Recorded: the record-structure table by inductive, the canonical-solution table by projection, `Structure.find_from_projection` and `PrimitiveProjections.find_opt` with their absences, the coercion graph at the LOWEST lookup (`lookup_path_between_class`, which the function-class, sort-class, reversible and pattern searches all reach), the `class_tab` and `coercion_tab` reads (`class_info`, `class_exists`, `coercion_info`, `reachable_from`), and the active coercion and canonical-solution hook lists. Ineligible: a proof that asks an active hook (`plugin_hook`, detail `coercion_hooks: <names>` or `canonical_hooks: <names>`): a hook is a plugin closure whose answer can depend on plugin state (rocq-elpi's hooks run the elpi program `Elpi CoercionFallbackTactic` or `Elpi CS` names). Rocq registers no hook, so a stock compile reads the empty lists | `pretyping/structures.ml`; `pretyping/coercionops.ml` `lookup_path_between_class`, `class_info`; `pretyping/coercion.ml` `apply_hooks`; `pretyping/evarconv.ml` `apply_hooks` |
| 15 | Autorewrite, Rocqlib, schemes, keys, plugin tables | Recorded: each rewrite base that `autorewrite` or the `hints` strategy of `rewrite_strat` looks up, absent bases included (`find_base`, which both reach); each `lib_ref`, `lib_ref_opt`, `has_ref`, `check_ref` and the Rocqlib domain, plus one digest of the WHOLE Rocqlib table at each proof's start, which is the only sound answer to the about 120 process-wide `lazy` values that cache a `lib_ref` result and never ask again; each `DeclareScheme.lookup_scheme`; the Keys table; the ring and field carrier tables at their lookup, absences included; the three Zify registration tables before `init_cache` copies them, each keyed by its Summary name (replay: `recorded_zify_table` digests the table the key names); and the SSR view-adaptor database at `AdaptorDb.get` | `tactics/autorewrite.ml` `find_base`; `library/rocqlib.ml`; `tactics/declareScheme.ml`; `pretyping/keys.ml`; `plugins/ring/ring.ml`; `plugins/micromega/zify.ml`; `plugins/ssr/ssrview.ml` |
| 16 | ML-registered tables | In key item 2: the binary's digest, and every loaded plugin with its file digests, in load order. A table an ML module fills when it loads is fixed by those. A closure a plugin installs LATER is not: it can read plugin state that commands change (unicoq's `Set Use Unicoq` installs its unifier, and `Unset` does not remove it). Ineligible: an ML tactic whose plugin is NOT one of this tree's (`ml_tactic`, detail `<plugin>.<tactic>`), because the census audited this tree only. That is the fence over coqhammer's forking `best`/`sbest`/`hbest`, over smpl, and over any plugin added later. Also ineligible, for the proof open at the time and every later proof of the process (the fence is checked when a proof opens and when it closes): a process-wide closure setter called more times than Rocq's own modules call it (`plugin_hook`, detail the setter: `Evarconv.set_evar_conv`, `Evarconv.set_solve_evars`, `Typeclasses.set_solve_all_instances`, `Typeclasses.set_solve_one_instance`, `Namegen.set_reserved_typed_name`, `CClosure.set_conv`, `Coercionops.install_path_comparator`, `Tactics.declare_intro_decomp_eq`, `Equality.set_eq_dec_scheme_kind`, `Ind_tables.set_declare_definition_scheme` and `set_register_definition_scheme`, `Declare.Obls.set_default_tactic`, `Ssrcommon.set_ssrautoprop_tac` (the refs behind the last four are no longer exported), `Proof_bullet.register_behavior` (any registration beyond Rocq's two), `Tac2env.set_compiled_global` (which nothing in this tree calls: an entry of the compiled-global cache runs in place of the Ltac2 definition row 10 records), and a redefinition through `Tacenv.register_ml_tactic ~overwrite`, `Tac2env.define_primitive` or `Tac2env.define_ml_object`, which would put another closure under an audited plugin's name) | `proof_record_env.ml` `toolchain`; `plugins/ltac/tacinterp.ml` `TacML`; `plugins/ltac2/tac2env.ml` `interp_primitive`, `set_compiled_global`; `lib/proof_recorder.ml` `closure_setter`, `close_proof` |
| 17 | Fresh names | Composite of rows 1, 3, 6 and 20, plus the lexer keyword state: `fresh "s"` gives `s0` when `s` is a keyword, and a `Reserved Notation` that makes `s` one does not change the parsed sentences, because a string literal is not reparsed. Recorded: each keyword test `fresh` makes, by string (channel `keyword`). Elsewhere the keyword state changes how a proof parses, which is inside key item 1, the parsed sentences | `proof_record_env.ml`; `toplevel/vernac.ml`; `plugins/ltac/tacinterp.ml` `interp_fresh_id` |
| 18 | Counters | Recorded: each counter's value at the proof's start (channel `counter_start`). Writes: the advance of each counter the proof made — `univ_level`, `sort_quality`, `evar`, `meta`, `hint_counter`, `rewrite_hint_counter`, `ssr_abstract_id` — and the universe levels and constraints each declaration adds. An empty counter list now means no advance | `engine/univGen.ml`, `engine/evd.ml`, `engine/evarutil.ml`, `tactics/hints.ml`, `tactics/autorewrite.ml`, `plugins/ssr/ssripats.ml`; `vernac/declare.ml` `declare_constant` |
| 19 | `Proof using` | Recorded: the declared set at the proof's start (channel `proof_using`, absent when none), the interpreted set at the later `Proof using ...` sentence on its own channel `proof_using_set`, so the opening absence cannot hide it, keyed by the sentence's expression without its locations (`proof_using_key`), and each named-collection lookup with the digest of its expression, absent collections included. Replay: the `proof_using_set` evaluator reads the expression back (`proof_using_of_key`) and interprets it with the sentence's `interpret_proof_using` on the proof as it started (`replay_start`); a statement with an undefined unification variable is a miss, since only through one could the set depend on the sentences before it. The `proof_using_collection` evaluator looks the name up again with the record site's `recorded_proof_using_collection` | `vernac/declare.ml` `record_using`, `set_proof_using`; `vernac/proof_using.ml` |
| 20 | Lib state: module path, section prefix | Key item 3, in the `position` field. `module_path` is the path the `.glob` writes (sections excluded), `section_path` adds the open sections | `proof_record_env.ml` `position` |
| 21 | Commands inside a proof, `abstract`, Program obligations, mutual proofs, `par:` | Ineligible: a sentence that the classifier does not call a proof step (`command_in_proof`); an `abstract` or other sub-proof (`subproof`); a proof opened inside another (`nested_proof`); a proof that declares more than one constant (`mutual`), which one entry cannot join to its objects; a sentence under a control flag (`control_flag`: `Time`, `Instructions`, `Profile`, `Redirect`, `Timeout`, `Fail`, `Succeed`), whose result depends on the clock, on the output channel, or on a state restored behind the recorder's back; a `par:` goal selector (`par`), which `rocq compile` runs in tactic worker processes by default whatever the async mode, so the tactic's reads happen where no recorder runs and this process only installs the term a worker returns; and a recorder that holds a proof the live proof stack does not (`recorder_desync`). An `Abort` writes no entry and frees the recorder, so the proofs after it keep theirs | `toplevel/vernac.ml`; `proofs/subproof.ml`; `lib/proof_recorder.ml` `open_proof`, `drop_proof`; `vernac/vernacControl.ml` `under_one_control`; `vernac/comTactic.ml` `solve_parallel`; `vernac/vernacentries.ml` `vernac_abort`; `vernac/vernacstate.ml` `discard_all` |
| 22 | Time and timeouts | Ineligible: every `Control.timeout`, which is the one point `Timeout`, `timeout` and Ltac2 `timeout` pass through (`timeout`), and the `Timeout` control itself (`control_flag`). A watchdog that does not pass through `Control.timeout` is in a plugin, and an ML tactic of a plugin this tree does not hold is already `ml_tactic` (row 16) | `lib/control.ml` `timeout`; `vernac/vernacControl.ml`; `plugins/ltac/tacinterp.ml` |
| 23 | Files and external processes | Ineligible: `native_compute` (`native_compute`) and the external prover `csdpcert` that `psatz` calls (`external_prover`). Micromega's certificate caches are already blocked in grading | `kernel/nativelib.ml` `compile`; `plugins/micromega/coq_micromega.ml` `really_call_csdpcert` |
| 24 | Resource limits | Recorded in the header: `stack_limit` (in key item 2), `memory_cap`, `rlimit_as`, `rlimit_data`, `overcommit_memory`. The cap is recorded and never compared (GRADE, 12:19Z); replay is refused when an address-space limit is set or `overcommit_memory` is 2 | `lib/proof_limits.ml` |
| M1 | Abbreviations | Recorded: each `find_opt` and `find_interp`, by kernel name (as `Lib.kername_key` writes it). Replay: the evaluator reads the name back (`Lib.kername_of_key`) and digests the entry with the record site's `recorded_abbreviation` | `interp/abbreviation.ml` |
| M2 | Reserved types | Recorded: each `find_reserved_type`, by identifier root. Replay: the evaluator looks the root up again with the record site's `recorded_reserved_type` | `interp/reserve.ml` |
| M3 | Generalizable variables | Recorded: one digest of the table at each proof's start | `proof_record_env.ml`; `interp/implicit_quantifiers.ml` `generalizable_idents` |
| M4 | Schemes created (write) | Write: each scheme the proof created, by name | `tactics/ind_tables.ml` `define` |
| M5 | Universe constraint sources (write) | Write: the constant whose declaration wrote a constraint-source record | `vernac/declare.ml` `declare_constant` |
| M6 | `-skip-qed-typecheck` unchecked mark (write) | Not stored: replay writes the mark of the grade compile's own flags. The header records which flag the recording compile ran under, and `kernel_check` records whether the kernel typed each proof | `lib/proof_record.mli` `skip_qed_typecheck`, `kernel_check` |
| M7 | Template default levels | Recorded: one digest of the table at each proof's start | `proof_record_env.ml`; `engine/uState.ml` `template_default_univs` |
| S2.1 | Parser state, load paths, loaded libraries | In key item 2: every loaded library in load order with its `.vo` digest, and the safe-loaded ones. The grammar is inside key item 1, the parsed sentences | `proof_record_env.ml` `toolchain`; `vernac/library.ml` `library_digest`, `safe_loaded_libraries` |
| N1 | Printing state | Ineligible: Ltac2 `Message.to_string`, the one primitive that turns printed text into data (`message_to_string`) | `plugins/ltac2/tac2core.ml` |
| N2 | `stepl`/`stepr` lemmas | Recorded: the selected `transitivity-steps-l` or `transitivity-steps-r` table, before `stepl` or `stepr` searches it. A `Declare Left Step` that is removed leaves the lemma in place and takes it out of the search list, which no other read sees | `plugins/ltac/extratactics.mlg` |
| N3 | Prop inductives with dependent elimination | Recorded: each `is_prop_but_default_dependent_elim`, by inductive | `tactics/elimschemes.ml` |
| N4 | Default solver tactics | Recorded: the stored tactic at the `tactic_option` getter, by option name, absent included. `Obligation Tactic` and `Set Firstorder Solver` are Summary-backed tactic options, not Goptions options, so the row-13 snapshot does not hold them | `vernac/tactic_option.ml` |
| N5 | smpl databases | Ineligible: smpl is not one of this tree's plugins, so its ML tactics are `ml_tactic` (row 16) and a proof that runs one stores no term. `Smpl Add` inside a proof is also `command_in_proof` | `plugins/ltac/tacinterp.ml` `TacML`; smpl `src/smpl.mlg` |

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
