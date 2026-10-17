(* -*- mode: coq; coq-prog-args: ("-vok") -*- *)
(* Print Assumptions reuses traversals across queries in one environment.
   In -vok mode the body of a Qed lemma from a library loaded without its
   proofs cannot be read, so [foo] is reported as an axiom. Nothing whose walk
   meets that body is reused, so it is reported the same way every time it is
   reached, directly or through a constant an earlier query walked. *)

Require Import TestSuite.for_vos.

Definition use_foo := foo.
Definition use_both := foo + bar.

Print Assumptions use_both.
Print Assumptions use_both.
Print Assumptions foo.
Print Assumptions use_foo.
Print Assumptions bar.
Print Assumptions use_both.
