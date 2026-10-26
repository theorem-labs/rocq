(* misc/proof-record-plugin-hooks.sh compiles this file with -proof-record
   as it is, and once with the TestSetLibraryClosures line commented out.
   Loading Ltac2 and ssreflect runs their own calls of the fenced setters they
   own, which must trip nothing (stock counts not too low); the probe's one
   extra call of each must trip the fence (stock counts not too high). *)

(* Ltac2 is imported, so the proofs below run in its proof mode, where
   [exact I] is its own notation; ssreflect is only loaded, not imported. *)
From Ltac2 Require Import Ltac2.
From Corelib Require ssreflect.

Declare ML Module "coq-test-suite.library_closures".

Lemma before_library : True.
Proof. exact I. Qed.

(* The Ltac2 global whose compiled form TestSetLibraryClosures replaces; no
   proof runs it. *)
Ltac2 probe_target () := ().

TestSetLibraryClosures.

Lemma after_library : True.
Proof. exact I. Qed.
