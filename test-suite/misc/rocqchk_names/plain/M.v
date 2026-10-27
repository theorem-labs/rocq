From BadNames Require A.

(* The test renames zqxfoo to zqx, a line break, then oo, in the library
   segment of M.vo only, so this type names a constant that no library
   declares. An axiom's body compiles to bytecode without a lookup, so the
   load of the admitted M does not resolve it. *)
Axiom model : A.zqxfoo.
