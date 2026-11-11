Declare ML Module "coq-test-suite.bad_name".

(* The default schemes take their names from the strict Nameops.add_suffix,
   which refuses a type name that holds a line break. *)
Unset Elimination Schemes.

(* A mutual block labelled zqxind, whose second type is named zqxtwo, a line
   break, then zqxforged. *)
Test Line Break Inductive zqxind zqxtwo zqxforged.
