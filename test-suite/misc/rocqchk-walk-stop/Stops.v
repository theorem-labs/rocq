(* The honest library that misc/rocqchk_walk_stop_summary.sh compiles, and
   that forge.ml turns, one shape to a copy, into a library coqc refuses to
   write. Each comment names the shape and what forge.ml makes of the
   modules under it. Here every module is one coqc writes: the -o summary
   reads each implementation to its end and lists the axiom ax of F's body
   under RC, RE and RW, and no p, which every implementation defines. *)
Inductive unit : Set := tt.

Module Type T. Parameter p : unit. End T.
Module Type Empty. End Empty.
Module Type HasC. Declare Module C : T. End HasC.
Module Type S. End S.

Module Defines. Definition p := tt. End Defines.
Module Outer. Module C := Defines. End Outer.
Module A. End A.
Module F (X : S). Axiom ax : unit. End F.

(* alias-cycle: Self := Self. *)
Module Self : T := Defines.

(* alias-two-cycle: Ping := Pong and Pong := Ping. Pong's type declares
   nothing, so that the summary reads the cycle only for Ping.p, and the
   walk meets it at Pong's alias. *)
Module Ping : T := Defines.
Module Pong : Empty := Defines.

(* implementation-cycle: Up := Down and Down := Up.C. Down's type declares
   nothing, so that the summary reads them only for Up.C.p. *)
Module Up : HasC := Outer.
Module Down : Empty := Outer.C.

(* functor-implementation: NotF, which is not a functor, gets a functor's
   expression, Defines under one parameter that its type does not have. *)
Module NotF : T := Defines.

(* with-functor: RW := (F with Module ... := A) A. *)
Module RW := F A.

(* expression-arguments: Gexpr's expression binds two parameters, and its
   type has one. *)
Module Gexpr (X : S) := F X.
Module RE := Gexpr A.

(* path-chain: Chain.M := Chain, and Chain.G (X : S) := X.M.G X.M. RC then
   resolves Chain.M.G, Chain.M.M.G, and so on, a path one label longer at
   each step. *)
Module Chain.
  Module M := A.
  Module G (X : S) := F X.
End Chain.
Module RC := Chain.G Chain.

(* argument-chain: G := G A. RG then resolves G again at each step, with
   one argument more. *)
Module G0 (X : S) (Y : S). End G0.
Module G := G0 A.
Module RG := G A.
