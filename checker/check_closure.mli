(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The statement report of [rocqchk -statement-report FILE]. *)

type request = {
  req_name : string;  (** a label, printed back as given *)
  req_model : string;  (** the constant whose closure is reported *)
  req_trusted : string option;  (** the constant whose type it must have *)
}

val read_requests : string -> request list
(** One request per line, [<name> <model> [<trusted>|-]], the tokens
    separated by single spaces; a constant is named by the string
    [Names.Constant.to_string] prints. Blank lines and lines starting with [#]
    are skipped. A tab or carriage return on any line is an error.
    @raise CErrors.UserError on any other line. *)

val print : jobs:int -> Environ.env ->
  (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> request list -> unit
(** Print the report, one line per message on the feedback channel:

    {v
STATEMENT REPORT 3
statement <name> <model> <trusted|-> <verdict> <axiom-count> <flag-count>
axiom <name> <constant> <canonical>
resolved <name> <field> <canonical>
flag <name> <kind> <object> <canonical>
END STATEMENT REPORT
    v}

    The number after [STATEMENT REPORT] is the format version: 3. Format 2
    had no canonical column on [flag] lines and no [?] token; a reader of 2
    must not read 3. A reader
    must take a report as whole only when it reads the [END STATEMENT
    REPORT] line: a report that stops (an anomaly inside the report's own
    module lookups, for instance) has printed the statements before it and
    no end line, and the checker still exits 0. [<constant>]
    is the path the closure reached the axiom by, as [Names.Constant.to_string]
    prints it; [<canonical>] is that constant's canonical kernel name, always
    printed. It is the canonical half of the key the final environment
    stores the constant under. A constant or inductive only an
    implementation holds prints [?] followed by the term's own canonical
    name there ([?P.A:B.C.ax]): that half comes from the term that names it,
    which nothing ties to a declaration, so a reader must never join on a
    token that starts with [?] (no identifier contains it). The name after
    the [?] only keeps two such axioms apart. Two paths to one constant share a
    canonical name, and two kernel
    names never print alike: [<canonical>] is the root of the module path,
    [:], then the modules under it and the label separated by dots. The root
    is the library's dirpath ([P.A:B.ax] is [ax] of module [B] of library
    [P.A]; [P.A.B:ax] is [ax] of library [P.A.B]) or, for a functor argument
    or a bound module, [<dirpath#name#n>]. No identifier contains [:], [<]
    or [#].

    A [flag] line names the object by its path and the same canonical token
    as an [axiom] line (the environment key's, or [?] and the term's for an
    object only an implementation holds), so two objects of one printed
    path that rely on the same condition give two flag lines.

    A [resolved] line, after the statement's [axiom] lines and before its
    [flag] lines, names an interface field without a body in the final
    environment that the closure read through the implementation defining
    it; the field is printed by its path and canonical name. It is not
    counted in [<axiom-count>], and it does not say the field is free of
    axioms: what the implementation rests on is listed as [axiom] lines, and
    an opaque body that cannot be read is both [resolved] and an [axiom].

    A request's model is looked up first among the constants of the final
    environment, by the string [Names.Constant.to_string] prints. Only a name
    no constant there prints as is looked up in the module implementations,
    the way [Print Assumptions] finds a constant a seal hides: a field of a
    sealed module that its interface leaves out, or one an [Include] in it
    brings. Every such match is collected: one is answered as usual, more than
    one with the verdict [ambiguous] and no axiom or flag line, none with
    [model-missing]. A request that names a trusted constant is answered
    only from the final environment: a model one implementation alone holds
    answers [model-missing] there, and one several implementations hold
    answers [ambiguous]. A name two constants of the final
    environment print as (a library [P.A] with a module [B], and a library
    [P.A.B]) answers [ambiguous] as a model and [trusted-ambiguous] as a
    trusted constant. The implementation lookup splits the name at every
    dot, so a hidden module or label named [..] is not found there and
    answers [model-missing]. A name the final environment holds is never
    looked up in an implementation.

    The verdict is [match] when [Definition f := model] ([Polymorphic] when
    the trusted constant is) is accepted for the field [Parameter f : T] of a
    sealing module type, T being the trusted constant's type and universes:
    the model's type is cumulative to T, a needed universe constraint being
    added when it is consistent with the environment (a polymorphic model at
    a monomorphic T is taken at fresh universes; a polymorphic T requires the
    model's universe context to be T's, and adds no constraint). It is
    [universes-differ] when the types need universe constraints the
    environment or T's context refuses, when the universe contexts differ,
    and for every polymorphic model whose universe context has sort variables
    or constraints: elaborating the definition can minimize those, and the
    check does not replay it, so the sealing may still accept such a model.
    It is [mismatch] when the types are not convertible, and otherwise
    [model-missing], [trusted-missing], [ambiguous] (the model name denotes
    several constants), [trusted-ambiguous] (the trusted name does), or
    [not-requested] (no trusted constant).

    The verdict is about the two constants as the kernel stores them.
    Implicit arguments are elaboration data that the kernel never sees, so a
    model declared with maximal implicit arguments reads [match] when its
    type is the statement's. Whether a bare alias [Definition f := model]
    then elaborates depends on the context it is written in, which this
    checker does not see.

    The axioms are the constants
    without a body that the selected proof witness of the model constant's
    body and type reaches. A public term uses a body-bearing declaration in
    the final environment; a bodyless public declaration uses its module
    implementation, and its dependencies continue in that implementation
    view. This keeps an implementation proof's typing conditions from being
    replaced by an independent signature proof. Literal and array terms
    also reach their registered primitive type. The flags are the relaxed
    typing conditions of what they reach:
    [type-in-type], [unsafe-fixpoint], [unchecked-eliminations],
    [assumed-positive], [uip] and [indices-not-mattering]. Statements keep
    request order; axioms and flags are sorted.

    With [jobs] above 1, up to [jobs - 1] forked processes read and walk the
    opaque bodies of the environment while the requests are walked
    ([CheckWorkers.Forked]), and the walk takes what they computed when it
    has come. The report is the one printed with [jobs] at 1: a
    process only computes what the main process would compute, and the main
    process computes whatever a process did not send in time. *)
