(* flag is inlined into the bytecode of probe (Register Inline). The edited
   tree changes flag only: probe's stored body is the same, and its bytecode
   is not. *)
Definition flag : bool := true.
Register Inline flag.
Definition probe (_ : unit) : bool := flag.
