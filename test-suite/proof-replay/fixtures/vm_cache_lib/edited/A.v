(* probe calls flag at run time (no inlining). The edited tree changes flag
   only. *)
Definition flag : bool := false.
Definition probe (_ : unit) : bool := flag.
