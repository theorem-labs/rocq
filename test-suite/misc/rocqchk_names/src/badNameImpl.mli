
val declare_axiom : Names.Id.t -> Names.Id.t -> unit
(** [declare_axiom before after] declares an axiom in [Set] whose name is
    [before], a line break, then [after]. *)

val declare_inductive : Names.Id.t -> Names.Id.t -> Names.Id.t -> unit
(** [declare_inductive first before after] declares a mutual block of two
    inductive types in [Set]: [first], which gives the block its label, and a
    type whose name is [before], a line break, then [after]. *)

val declare_constructor : Names.Id.t -> Names.Id.t -> Names.Id.t -> unit
(** [declare_constructor typename before after] declares an inductive type
    [typename] in [Set] whose only constructor is named [before], a line
    break, then [after]. *)

val declare_bad_parameter :
  bad_path:bool -> Names.Id.t -> Names.Id.t -> Names.Id.t -> Names.Id.t -> unit
(** [declare_bad_parameter ~bad_path name ty before after] adds to the kernel a
    module type [name], a functor of one parameter of the module type [ty].
    With [bad_path], the parameter's path holds [before], a line break, then
    [after]; otherwise its identifier does. *)
