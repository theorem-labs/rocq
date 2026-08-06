# Restricted model policy plugin

This plugin installs an opt-in, pre-effect policy for untrusted source compiled
with `rocq compile`. It does not change Rocq's kernel, elaborator, resolver, or
normal execution mode.

The trusted driver must first load the complete dependency closure, then load
the plugin from a final trusted bootstrap file:

```text
rocq compile \
  -q \
  -native-compiler off \
  -require Trusted.Dependency \
  -l RestrictedBootstrap.v \
  Model.v
```

where `RestrictedBootstrap.v` contains only:

```coq
Declare ML Module "rocq-runtime.plugins.restricted_model".
```

Loading the plugin snapshots the libraries currently present in memory and
registers a `Stm.document_add_hook`. The hook sees each subsequently parsed
command before STM classification, syntactic interpretation, or execution.
Later `Require` commands are accepted only when they resolve uniquely to a
library which remains loaded and was present in that snapshot.

The initial policy rejects filesystem and dynamic-code effects, kernel-checking
changes, state rollback, and unknown top-level extensions. Ordinary Gallina and
the sequential Ltac/Ltac2 proof-command adapters remain unchanged. Parallel
proof-command adapters are deliberately not enabled yet.

This plugin covers the `rocq compile` document-add path. The trusted driver is
still responsible for:

- invoking one source file per process;
- disabling rcfiles, native compilation, and asynchronous proofs;
- presenting dependencies read-only and providing a fresh output directory;
- loading the policy after every trusted dependency and before model source;
- carrying forward only the expected artifact after a successful exit;
- retaining the OS sandbox and final aggregate kernel check.

Interactive STM query APIs are outside this initial compile-only boundary.
