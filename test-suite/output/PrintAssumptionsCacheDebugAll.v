(* -*- coq-prog-args: ("-native-compiler" "no"); -*- *)
(* Print Assumptions reuses traversals across queries in one environment.
   The reuse has no debug flag: Set Debug "all" turns on every flag there is,
   and the second query, which replays the first one's traversal, must print
   exactly what it prints without the reuse. "-misc" because that flag makes
   the document manager run the external program dot, whose messages depend
   on the machine. "-native-compiler no" because on a build configured with
   -native-compiler yes the file is also compiled to native code, and the
   native-compiler flag then prints that compilation. *)

Axiom ax : Prop.
Definition f := ax.
Print Assumptions f.
Set Debug "all,-misc".
Print Assumptions f.
