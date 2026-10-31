(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The OCaml type of what every object kind of this build stores in a .vo
   (BET-342, the payload part of [rocq-library-label --vo-representation]).

   An object segment of a .vo holds, per object, the name of its kind and
   the marshalled payload of that kind ([Libobject.Dyn]). The name is
   printed by [--vo-representation] already. This tool prints the payload's
   OCaml type, so that a change to how a payload is represented -- a field
   added to a record, a constructor renamed or moved, a type alias changed
   underneath -- changes that printing, and so fails
   test-suite/misc/vo-format.sh until [vo_magic] moves
   (tools/configure/configure.ml).

   It reads the typed trees dune writes (.cmt, and .cmti, which carries the
   declarations of a module with no implementation) under the build
   directories it is given, which are the
   directories whose code [rocq-library-label] links (checker/dune). Nothing
   else is read: no load path and no typing environment is rebuilt, so the
   printing is a function of those trees alone. A tree holds the typedtree
   as the type checker left it, before any optimisation, so dune's dev and
   release profiles give one printing; and only forms of compiler-libs
   that OCaml 4.14 up to 5.5 agree on are read (see below), so the
   compiler's version does not change the printing either.

   For every reference to [Libobject.declare_object] and its siblings
   ([declare_object_full], [declare_named_object], [declare_named_object_full]
   and [declare_named_object_gen] -- together the whole of what registers a
   kind, since they alone reach [Libobject.Dyn.create]), it takes the type
   the type checker gave that reference, which is the declared type
   instantiated at that site, and reads from it the type of the value the
   kind's [Dyn] holds. It then expands that type: an alias is resolved, a
   record and a variant are printed with their fields or constructors in
   order and with their runtime representation, an object type with its
   methods, and a type whose definition is in no tree is named and said to
   be [opaque], with why.

   A printed line carries a short token where it must say why, never a
   sentence: the lines are pinned by test-suite/misc/vo-format.sh, so a
   reworded sentence would be a changed line and would ask for a .vo
   format version it does not need. The tokens are these, and what each
   one means is here:
   - [payload_unresolved ... free-variable]: a site whose payload type
     holds a type variable -- one piece of code that registers a kind per
     call, at a type its callers choose ([Goptions.declare_option] is the
     one such site). The names of such kinds are built at run time too, so
     the object part does not say which they are either. The line prints
     what the payload does pin (['_] for the variable) and, after
     [; reaches], the declared types the site's own toplevel value names,
     whose definitions are printed with the rest: for an option that is
     [Goptions.option_kind], so the four types an option can store are
     pinned. Which option stores which is pinned too, by the
     [option_payload] lines rocq-library-label prints beside this part
     (checker/library_label.ml);
   - [; in-functor M]: the reference is in the body of the functor [M], so
     it is one kind per application of [M], at types the application
     chooses. What it stores is printed through the functor's body, so it
     is pinned when the body names it (Zify's table stores [Constr.t]) and
     not when it is the functor's parameter. [Goptions.MakeRefTable] and
     [Goptions.MakeStringTable] are the second case, and the element type
     each of their applications chooses is printed as a [table_payload]
     line;
   - [opaque NAME REASON]: a type reached from a payload whose definition
     no tree holds. The reasons are [abstract] (abstract in the module
     that defines it), [functor-application] (built by one),
     [functor-argument-or-local] (declared by a functor's argument or a
     local module), [functor-result] (its module's tree declares no such
     type), [another-package] (outside the scanned directories: the OCaml
     standard library, zarith), [alias-holds-itself] (an alias whose body
     holds it again, printed where it is expanded), [object] and
     [first-class-module] (an object type or a module type reached where
     no name is), [self-holding] (for [<cycle>]) and [free-variable] (for
     ['_]). The kernel part of [--vo-representation] covers the kernel
     types among them through checker/values.ml, where it describes them;
     a [Dyn] tag among them hides the value behind it, so a stored Ltac
     expression is pinned down to its generic arguments and no further;
   - ['_]: a type variable the typed tree leaves free. A variant's
     existentials are named (['e0], ...) and a polymorphic field's
     universals are named (['p0], ...), so what is left is a variable no
     declaration binds;
   - [<cycle>]: a type that holds itself with no declaration between, which
     an object type and a polymorphic variant can be.

   Usage: vo_payloads [--ml] DIR... -- each DIR is searched for typed trees,
   and a DIR that holds none is an error: a directory this list names and
   the dependencies of the rule in checker/dune do not is a directory
   nothing builds in a tree built from clean, so the two lists cannot drift
   apart there without a build failing. --ml wraps the printing in an OCaml
   module, which is how checker/dune puts it in rocq-library-label. *)

open Types

let fatal fmt =
  Printf.ksprintf (fun s -> prerr_endline ("vo_payloads: " ^ s); exit 2) fmt

(* {1 What is read from compiler-libs}

   One text compiles and prints the same on every compiler this build
   supports (OCaml 4.14 to 5.5), which it does by reading only the forms
   that did not change across them: [Path.flatten] rather than [Path.head]
   (which [Pextra_ty], new in 5.1, breaks), [Btype.fold_type_expr] rather
   than the shape of a [Ttuple] (labelled components since 5.4), one level
   of [Tast_iterator] rather than the shape of a [Texp_apply] argument
   ([apply_arg] since 5.4), [Longident.last] rather than a
   [label_description] (moved to [Data_types] in 5.5), a catch-all on
   [type_kind] ([Type_abstract] took an argument in 5.2, [Type_external]
   arrived in 5.5), and a catch-all on [type_desc] ([Tfunctor] arrived in
   5.5). *)

type kind =
  | Abstract of type_expr option
  | Record of label_declaration list * string
  | Variant of constructor_declaration list * string
  | Open

let kind (decl : type_declaration) =
  match decl.type_kind with
  | Type_record (labels, repr) ->
    let repr =
      match repr with
      | Record_regular -> "record"
      | Record_float -> "record[float]"
      | Record_unboxed _ -> "record[unboxed]"
      | Record_inlined _ -> "record[inlined]"
      | Record_extension _ -> "record[extension]"
    in
    Record (labels, repr)
  | Type_variant (constructors, repr) ->
    let repr =
      match repr with
      | Variant_regular -> "variant"
      | Variant_unboxed -> "variant[unboxed]"
    in
    Variant (constructors, repr)
  | Type_open -> Open
  (* [Type_abstract], which carries the origin of the type since 5.2, and
     [Type_external], new in 5.5: neither says how a value is represented. *)
  | _ -> Abstract decl.type_manifest

type arguments =
  | Tuple of type_expr list
  | Inline of label_declaration list

let constructor_arguments = function
  | Cstr_tuple tys -> Tuple tys
  | Cstr_record labels -> Inline labels

let field_present k =
  match field_kind_repr k with Fpublic | Fprivate -> true | Fabsent -> false

(* The components of a tuple type, in order. *)
let tuple_components ty = List.rev (Btype.fold_type_expr (fun acc t -> t :: acc) [] ty)

(* The arguments of an application, in order and without the ones a partial
   application leaves out: the children of the node, minus the function. *)
let apply_arguments ~fn application =
  let acc = ref [] in
  let it =
    { Tast_iterator.default_iterator with
      expr = (fun _ sub -> if sub != fn then acc := sub :: !acc) }
  in
  Tast_iterator.default_iterator.expr it application;
  List.rev !acc

(* {1 Names} *)

(* dune's wrapped libraries reach a module through an alias module [Lib__],
   so one typed tree names a module [Lib__.M] where another names it
   [Lib__M]. The two are one module and must print as one. *)
let normalize_name s =
  match String.split_on_char '.' s with
  | [] -> s
  | first :: rest ->
    let b = Buffer.create (String.length s) in
    Buffer.add_string b first;
    List.iter
      (fun part ->
         let n = Buffer.length b in
         let alias = n >= 2 && Buffer.nth b (n - 1) = '_' && Buffer.nth b (n - 2) = '_' in
         if not alias then Buffer.add_char b '.';
         Buffer.add_string b part)
      rest;
    Buffer.contents b

let path_name p = normalize_name (Path.name p)

(* [Path.head] fails on a functor application, which a type of this build
   can be named through ([CMap.Make(Int).t]). *)
let path_root p =
  match Path.flatten p with `Ok (id, _) -> Some id | `Contains_apply -> None

let functor_applied p =
  match Path.flatten p with `Contains_apply -> true | `Ok _ -> false

(* A path that applies a functor, written out with every name local to the
   unit it is written in qualified by that unit: [Set.Make(Self).t] of one
   unit and of another are two names, where [Path.name] gives one.
   [Path.flatten] refuses such a path, so the path is walked; the catch-all
   is for the forms a later compiler adds ([Pextra_ty], OCaml 5.1). *)
let[@warning "-11"] qualified_path ~scope p =
  let unit = List.hd scope in
  let rec go = function
    | Path.Pident id when Ident.persistent id || Ident.is_predef id -> Ident.name id
    | Path.Pident id -> unit ^ "." ^ Ident.name id
    | Path.Pdot (p, s) -> go p ^ "." ^ s
    | Path.Papply (f, a) -> go f ^ "(" ^ go a ^ ")"
    | p -> Path.name p
  in
  normalize_name (go p)

(* A path whose root is not a compilation unit is written in, and declared
   in, one unit: a module of that unit, a functor's argument, or a local
   module. *)
let local_path p =
  match path_root p with
  | None -> false
  | Some head -> not (Ident.persistent head) && not (Ident.is_predef head)

let last_component s =
  match String.rindex_opt s '.' with
  | None -> s
  | Some i -> String.sub s (i + 1) (String.length s - i - 1)

let penultimate_component s =
  match String.rindex_opt s '.' with
  | None -> ""
  | Some i -> last_component (String.sub s 0 i)

(* {1 What the typed trees are read for} *)

(* Every type declaration of every tree read, under the name a use of the
   type prints, with the module path it is declared in (the path its own
   body's names are read in). An implementation's declaration is kept over
   an interface's: it is the one that says how a value is represented,
   where an interface often makes the type abstract. A type declared inside
   a functor is registered under the functor's own path: a use inside that
   functor finds it ([Goptions.MakeTable.option_mark]), a use of the
   functor's result cannot name it, so from there it is [opaque]. *)
let declarations : (string, string list * type_declaration) Hashtbl.t =
  Hashtbl.create 1997

(* The modules whose trees were read, to tell a type this build defines
   somewhere the tool cannot follow from a type of another package. *)
let units : (string, unit) Hashtbl.t = Hashtbl.create 997

(* The module aliases of every tree read, under the name a use prints:
   dune's main module of a wrapped library is a file of them
   ([module Tacexpr = Ltac_plugin__Tacexpr]), and a unit renames its own
   modules ([module Constant = KerPair] in kernel/names.ml), so one module
   has a name through the alias and another in the tree that declares it. *)
let aliases : (string, string) Hashtbl.t = Hashtbl.create 997

(* One reference to a kind-registering function of [Libobject]. *)
type site = {
  s_scope : string list;   (* the module path the reference is written in *)
  s_binding : string list; (* the module and value names around it *)
  s_name : string option;  (* the kind's name, when the site names it *)
  s_stored : stored;       (* the type of what the kind stores *)
  (* The type of the toplevel value the reference is written in. A site
     that stores a variable registers a kind per call, and this type says
     what its callers can choose: [Goptions.declare_option] takes the
     [option_kind] whose four constructors are the option types. *)
  s_value : type_expr option;
  (* The functor whose body holds the reference, if any: such a site is one
     kind per application of that functor, at types the application chooses
     and the functor's own body does not name. *)
  s_functor : string option;
}
and stored = One of type_expr | Pair of type_expr * type_expr | Unknown of string

let sites : site list ref = ref []

(* One application of [Goptions.MakeRefTable] or [Goptions.MakeStringTable]:
   a table is a kind, and what it stores is the element type the application
   chooses, which the functor's body names only through its parameter. *)
type table = {
  t_name : string;            (* the module path of the application *)
  t_scope : string list;      (* the module path it is written in *)
  t_element : Path.t option;  (* the argument module, whose [t] it stores *)
}

let tables : table list ref = ref []

let table_functions = [ "MakeRefTable"; "MakeStringTable" ]

(* Every module bound to a functor application, under its full path: a
   table's argument can be one ([Detyping.PrintingCasesIf] is
   [PrintingFlags.PrintingInductiveMake (...)]), and then the type it
   stores is the functor's own. *)
let module_applications : (string, string) Hashtbl.t = Hashtbl.create 97

let registering_functions =
  [ "declare_object"; "declare_object_full"; "declare_named_object";
    "declare_named_object_full"; "declare_named_object_gen" ]

(* The functions that take a kind's name and build the declaration one of
   the above is applied to. *)
let naming_functions =
  [ "default_object"; "local_object"; "local_object_nodischarge";
    "global_object"; "global_object_nodischarge"; "superglobal_object";
    "superglobal_object_nodischarge"; "object_with_locality" ]

let libobject_function names p =
  let n = path_name p in
  penultimate_component n = "Libobject" && List.mem (last_component n) names

(* What a kind stores is what its [Dyn] value holds, which the type of the
   registering function at this site gives: [_ -> 'a -> obj] and
   [_ -> 'a Dyn.tag] store ['a], and [_ -> Id.t -> 'a -> obj] stores the
   pair (library/libobject.ml). *)
let stored_of_type fn ty =
  let rec arrows acc ty =
    match get_desc ty with
    | Tarrow (_, dom, cod, _) -> arrows (dom :: acc) cod
    | _ -> (List.rev acc, ty)
  in
  match get_desc ty with
  | Tarrow (_, _declaration, result, _) ->
    begin match arrows [] result with
      | ([], res) ->
        begin match get_desc res with
          | Tconstr (p, [ arg ], _) when last_component (path_name p) = "tag" -> One arg
          | _ -> Unknown (Printf.sprintf "%s returns a value this tool does not read" fn)
        end
      | ([ stored ], _) -> One stored
      | ([ id; stored ], _) -> Pair (id, stored)
      | (l, _) ->
        Unknown (Printf.sprintf "%s returns a function of %d arguments" fn (List.length l))
    end
  | _ -> Unknown (Printf.sprintf "%s is used without its declaration argument" fn)

(* The kind's name, when the site writes it: the [object_name] field, or the
   first argument of the function that builds the declaration. Both are read
   from the argument of the registering function, not guessed from the
   constants near it. A site that builds its name at run time (an option's
   nickname, a functor's argument) has none. *)
let name_of_argument arg =
  let found = ref [] in
  let add s = if not (List.mem s !found) then found := s :: !found in
  let string_of_expression e =
    match e.Typedtree.exp_desc with
    | Typedtree.Texp_constant (Asttypes.Const_string (s, _, _)) -> Some s
    | _ -> None
  in
  let it =
    { Tast_iterator.default_iterator with
      expr = (fun self e ->
          begin match e.Typedtree.exp_desc with
            | Typedtree.Texp_record { fields; _ } ->
              Array.iter
                (fun (_, def) ->
                   match def with
                   | Typedtree.Overridden (lid, v)
                     when Longident.last lid.Location.txt = "object_name" ->
                     (match string_of_expression v with Some s -> add s | None -> ())
                   | _ -> ())
                fields
            | Typedtree.Texp_apply (({ exp_desc = Texp_ident (p, _, _); _ } as fn), _)
              when libobject_function naming_functions p ->
              List.iter
                (fun v -> match string_of_expression v with Some s -> add s | None -> ())
                (apply_arguments ~fn e)
            | _ -> ()
          end;
          Tast_iterator.default_iterator.expr self e)
    }
  in
  it.Tast_iterator.expr it arg;
  match List.sort String.compare !found with
  | [] -> None
  | [ s ] -> Some s
  | l -> Some (String.concat "|" l)

let add_type scope name (decl : type_declaration) =
  let name = String.concat "." (scope @ [ name ]) in
  if not (Hashtbl.mem declarations name) then
    Hashtbl.add declarations name (scope, decl)

let add_declaration scope (d : Typedtree.type_declaration) =
  add_type scope (Ident.name d.typ_id) d.typ_type

(* [include M] puts M's declarations in the including module, under its
   names: [Names.DirPath.t] is declared in [Names.DirPath.Self] and included
   (kernel/names.ml). The included signature is the one the type checker
   inferred, so a type that is concrete there stays concrete. *)
let add_included scope (signature : Types.signature) =
  List.iter
    (function
      | Types.Sig_type (id, decl, _, _) -> add_type scope (Ident.name id) decl
      | _ -> ())
    signature

let add_alias scope id (p : Path.t) =
  let name = String.concat "." (scope @ [ Ident.name id ]) in
  (* A module of this unit is named by its own name alone wherever in the
     unit it is declared, and the name it is written beside is the one the
     alias is written in: [module MySet = A.Set] inside
     [Goptions.MakeTable] aliases [Goptions.MakeTable.A.Set], and
     [module Constant = KerPair] in [Names] aliases [Names.KerPair]. *)
  let target =
    if local_path p then String.concat "." (scope @ [ path_name p ])
    else path_name p
  in
  if name <> target && not (Hashtbl.mem aliases name) then
    Hashtbl.add aliases name target

(* A module's implementation: its type declarations, its module aliases and
   its references to the registering functions. *)
let collect_structure ~register_sites modname structure =
  let bindings : (string * type_expr) list ref = ref [] in
  let modules = ref [] in
  let functors = ref [] in
  let scope () = modname :: List.rev !modules in
  let record_site fn ty arg =
    if register_sites then
      let s_name = match arg with None -> None | Some a -> name_of_argument a in
      sites :=
        { s_scope = scope ();
          s_binding = List.rev (List.map fst !bindings @ !modules);
          s_name;
          s_stored = stored_of_type fn ty;
          s_value = (match List.rev !bindings with (_, ty) :: _ -> Some ty | [] -> None);
          s_functor = (match !functors with f :: _ -> Some f | [] -> None) }
        :: !sites
  in
  let it =
    { Tast_iterator.default_iterator with
      structure_item = (fun self item ->
          begin match item.Typedtree.str_desc with
            | Typedtree.Tstr_type (_, decls) -> List.iter (add_declaration (scope ())) decls
            | Typedtree.Tstr_include { incl_type; _ } -> add_included (scope ()) incl_type
            | Typedtree.Tstr_module
                { mb_id = Some id; mb_expr = { mod_desc = Tmod_ident (p, _); _ }; _ } ->
              add_alias (scope ()) id p
            | _ -> ()
          end;
          Tast_iterator.default_iterator.structure_item self item);
      module_binding = (fun self mb ->
          (* The module path the binding is written in, before its own name
             is pushed: the path its argument's names are read in. *)
          let outer = scope () in
          let pushed =
            match mb.Typedtree.mb_id with
            | Some id -> modules := Ident.name id :: !modules; true
            | None -> false
          in
          let rec functor_body (m : Typedtree.module_expr) =
            match m.Typedtree.mod_desc with
            | Typedtree.Tmod_functor _ -> true
            (* [module F : S = functor ...] wraps the functor. *)
            | Typedtree.Tmod_constraint (m, _, _, _) -> functor_body m
            | _ -> false
          in
          let is_functor = functor_body mb.Typedtree.mb_expr in
          (* [module Table = Goptions.MakeRefTable (A)]: the kind it
             registers stores [A.t]. *)
          let rec applied (m : Typedtree.module_expr) =
            match m.Typedtree.mod_desc with
            | Typedtree.Tmod_constraint (m, _, _, _) -> applied m
            | Typedtree.Tmod_apply ({ mod_desc = Tmod_ident (f, _); _ }, argument, _)
              when libobject_function table_functions f
                || (penultimate_component (path_name f) = "Goptions"
                    && List.mem (last_component (path_name f)) table_functions) ->
              let element =
                match argument.Typedtree.mod_desc with
                | Typedtree.Tmod_ident (a, _)
                  when last_component (path_name f) = "MakeRefTable" -> Some a
                | _ -> None
              in
              Some element
            | _ -> None
          in
          begin match applied mb.Typedtree.mb_expr with
            | Some t_element ->
              tables :=
                { t_name = String.concat "." (scope ()); t_scope = outer; t_element }
                :: !tables
            | None -> ()
          end;
          begin match mb.Typedtree.mb_expr.Typedtree.mod_desc with
            | Typedtree.Tmod_apply ({ mod_desc = Tmod_ident (f, _); _ }, _, _) ->
              Hashtbl.replace module_applications
                (String.concat "." (scope ())) (path_name f)
            | _ -> ()
          end;
          if is_functor then functors := String.concat "." (scope ()) :: !functors;
          Tast_iterator.default_iterator.module_binding self mb;
          if is_functor then functors := List.tl !functors;
          if pushed then modules := List.tl !modules);
      value_binding = (fun self vb ->
          let pushed =
            match Typedtree.pat_bound_idents vb.Typedtree.vb_pat with
            | id :: _ ->
              bindings := (Ident.name id, vb.Typedtree.vb_pat.pat_type) :: !bindings;
              true
            | [] -> false
          in
          Tast_iterator.default_iterator.value_binding self vb;
          if pushed then bindings := List.tl !bindings);
      expr = (fun self e ->
          match e.Typedtree.exp_desc with
          | Typedtree.Texp_apply (({ exp_desc = Texp_ident (p, _, _); _ } as fn), _)
            when libobject_function registering_functions p ->
            let arguments = apply_arguments ~fn e in
            record_site (last_component (path_name p)) fn.Typedtree.exp_type
              (match arguments with a :: _ -> Some a | [] -> None);
            (* The function is this site; only its arguments are searched on,
               so that its own identifier is not a second site. *)
            List.iter (fun a -> self.Tast_iterator.expr self a) arguments
          | Typedtree.Texp_ident (p, _, _) when libobject_function registering_functions p ->
            record_site (last_component (path_name p)) e.Typedtree.exp_type None
          | _ -> Tast_iterator.default_iterator.expr self e)
    }
  in
  it.Tast_iterator.structure it structure

(* The declarations of an interface. Every .cmti is read this way, after
   every .cmt, so an implementation's declaration wins; for a module that
   has no implementation ([Constrexpr], [Declarations], [Glob_term] and the
   other files of types) these are the only declarations there are. *)
let collect_signature modname signature =
  let modules = ref [] in
  let scope () = modname :: List.rev !modules in
  let it =
    { Tast_iterator.default_iterator with
      signature_item = (fun self item ->
          begin match item.Typedtree.sig_desc with
            | Typedtree.Tsig_type (_, decls) | Typedtree.Tsig_typesubst decls ->
              List.iter (add_declaration (scope ())) decls
            | Typedtree.Tsig_include { incl_type; _ } -> add_included (scope ()) incl_type
            | Typedtree.Tsig_module
                { md_id = Some id; md_type = { mty_desc = Tmty_alias (p, _); _ }; _ } ->
              add_alias (scope ()) id p
            | _ -> ()
          end;
          Tast_iterator.default_iterator.signature_item self item);
      (* A module type declares types that no module of this name holds. *)
      module_type_declaration = (fun _ _ -> ());
      module_declaration = (fun self md ->
          let pushed =
            match md.Typedtree.md_id with
            | Some id -> modules := Ident.name id :: !modules; true
            | None -> false
          in
          Tast_iterator.default_iterator.module_declaration self md;
          if pushed then modules := List.tl !modules)
    }
  in
  it.Tast_iterator.signature it signature

let read_tree file =
  let cmt = try Cmt_format.read_cmt file with _ -> fatal "cannot read %s" file in
  let modname = normalize_name cmt.Cmt_format.cmt_modname in
  match cmt.Cmt_format.cmt_annots with
  | Cmt_format.Implementation structure ->
    Hashtbl.replace units modname ();
    (* [Libobject] itself: its uses of these functions are their
       definitions, not registrations. Its types are read as any other
       module's. *)
    collect_structure ~register_sites:(modname <> "Libobject") modname structure
  | Cmt_format.Interface signature ->
    Hashtbl.replace units modname ();
    collect_signature modname signature
  | _ -> ()

(* The typed trees under [dir], implementations and interfaces apart. *)
let trees dir =
  let implementations = ref [] and interfaces = ref [] in
  let rec walk dir =
    let entries = try Sys.readdir dir with Sys_error _ -> [||] in
    Array.sort String.compare entries;
    Array.iter
      (fun e ->
         let p = Filename.concat dir e in
         if Sys.is_directory p then walk p
         else if Filename.check_suffix p ".cmt" then implementations := p :: !implementations
         else if Filename.check_suffix p ".cmti" then interfaces := p :: !interfaces)
      entries
  in
  if not (Sys.file_exists dir) then fatal "no such directory: %s" dir;
  walk dir;
  (List.sort String.compare !implementations, List.sort String.compare !interfaces)

(* {1 Printing a type} *)

let opaques : (string, string) Hashtbl.t = Hashtbl.create 97
let printed_declarations : (string, string) Hashtbl.t = Hashtbl.create 97

(* The least reason a name is opaque for, so that a name reached from a new
   place keeps the line it had. *)
let note_opaque name reason =
  match Hashtbl.find_opt opaques name with
  | Some r when String.compare r reason <= 0 -> ()
  | _ -> Hashtbl.replace opaques name reason

(* The types OCaml itself defines: their representation is the compiler's,
   not this build's, so they are printed and not expanded. *)
let predefined =
  [ "int"; "char"; "string"; "bytes"; "float"; "bool"; "unit"; "exn"; "array";
    "list"; "option"; "int32"; "int64"; "nativeint"; "lazy_t";
    "extension_constructor"; "floatarray" ]

let variable_name i =
  if i < 26 then Printf.sprintf "'%c" (Char.chr (Char.code 'a' + i))
  else Printf.sprintf "'v%d" i

(* The names under which a type written in the module path [scope] can be
   declared, innermost first, with every module alias resolved. *)
let rec resolve_alias ?(fuel = 8) name =
  if fuel <= 0 then name
  else
    let components = String.split_on_char '.' name in
    let rec longest k =
      if k = 0 then name
      else
        let prefix = String.concat "." (List.filteri (fun i _ -> i < k) components) in
        match Hashtbl.find_opt aliases prefix with
        | Some target ->
          resolve_alias ~fuel:(fuel - 1)
            (String.concat "." (target :: List.filteri (fun i _ -> i >= k) components))
        | None -> longest (k - 1)
    in
    longest (List.length components - 1)

let candidate_names scope p =
  let name = path_name p in
  let names =
    if not (local_path p) then [ name ]
    else
      (* A local module is declared somewhere in this unit, so every name it
         could have starts with the unit's. *)
      let rec outwards prefix =
        String.concat "." (prefix @ [ name ])
        :: (match List.rev prefix with
            | [] | [ _ ] -> []
            | _ :: shorter -> outwards (List.rev shorter))
      in
      outwards scope
  in
  List.fold_left
    (fun acc n -> if List.mem n acc then acc else acc @ [ n ])
    [] (List.map resolve_alias names)

(* The object and variant types being printed. A declaration stops the walk
   on a type that holds itself ([print_declaration] prints it once and names
   it afterwards), but an object type and a polymorphic variant have no
   declaration to stop at ([< m : 'a > as 'a], [[`A of 'a] as 'a]). *)
let printing : type_expr list ref = ref []

let guarded ty print =
  (* By identity, not by [get_id]: an identifier is unique inside one typed
     tree, and these types are read from many. *)
  if List.memq ty !printing then begin
    note_opaque "<cycle>" "self-holding";
    "<cycle>"
  end
  else begin
    printing := ty :: !printing;
    let printed = print () in
    printing := List.tl !printing;
    printed
  end

(* The methods of an object type, by name. *)
let methods_of fields =
  let rec collect ty acc =
    match get_desc ty with
    | Tfield (name, kind, ty, rest) ->
      collect rest (if field_present kind then (name, ty) :: acc else acc)
    | _ -> acc
  in
  List.sort (fun (a, _) (b, _) -> String.compare a b) (collect fields [])

(* The types a type holds, in the order they are written. One list, so that
   a walk added here reaches every form the others do. *)
let children ty =
  match get_desc ty with
  | Tarrow (_, dom, cod, _) -> [ dom; cod ]
  | Ttuple _ -> tuple_components ty
  | Tconstr (_, tys, _) -> tys
  | Tobject (fields, _) -> List.map snd (methods_of fields)
  | Tvariant row ->
    List.concat_map
      (fun (_, field) ->
         match row_field_repr field with
         | Rpresent (Some ty) -> [ ty ]
         | Reither (_, tys, _) -> tys
         | Rpresent None | Rabsent -> [])
      (row_fields row)
  | Tpoly (body, _) -> [ body ]
  | _ -> []

(* Every variable [ty] holds gets a name in [env], in the order it is met;
   [fresh] says which family of names to draw from. A node is visited once:
   by identity, since an identifier is unique inside one typed tree and
   these types are read from many. *)
let name_variables ~fresh env ty =
  let walked = ref [] in
  let rec walk ty =
    match get_desc ty with
    | Tvar _ | Tunivar _ ->
      let id = get_id ty in
      if not (List.mem_assoc id !env) then env := (id, fresh ()) :: !env
    | _ when List.memq ty !walked -> ()
    | _ ->
      walked := ty :: !walked;
      List.iter walk (children ty)
  in
  walk ty

(* The aliases being expanded. An alias can stand for a type that holds it
   again ([Tacexpr.g_dispatch] is an object whose [tacexpr] method holds the
   tactic expressions that are written over [g_dispatch]), so expanding it
   inside itself would not end; it is printed by name there. *)
let expanding : string list ref = ref []

(* Whether the type printed last held a variable no declaration binds, which
   is what makes a site's payload unresolved. *)
let free_variable = ref false

(* The declaration a path names, under the first of its candidate names
   that one is registered for. *)
let find_declaration scope p =
  List.find_map
    (fun name ->
       match Hashtbl.find_opt declarations name with
       | Some decl -> Some (name, decl)
       | None -> None)
    (candidate_names scope p)

(* The declared types a type names, each under the name a use of it prints,
   with an alias followed into its body. It stops at a record or a variant:
   that type's own definition is printed on its own line, so naming it is
   enough. It is a walk of its own, not a by-product of printing, so what it
   answers does not depend on what was printed before it. *)
let reached_names ~scope ty =
  let found = Hashtbl.create 17 and walked = ref [] in
  let rec walk ~scope ty =
    if not (List.memq ty !walked) then begin
      walked := ty :: !walked;
      List.iter (walk ~scope) (children ty);
      match get_desc ty with
      | Tconstr (p, _, _) ->
        begin match find_declaration scope p with
          | None -> ()
          | Some (name, (owner, decl)) ->
            if not (Hashtbl.mem found name) then begin
              Hashtbl.replace found name ();
              match kind decl with
              | Abstract (Some manifest) -> walk ~scope:owner manifest
              | _ -> ()
            end
        end
      | _ -> ()
    end
  in
  walk ~scope ty;
  List.sort String.compare (Hashtbl.fold (fun k () acc -> k :: acc) found [])

(* [env] sends the identifier of a variable of the declaration being printed
   to its printing; [scope] is the module path the type being printed is
   written in. *)
let[@warning "-11"] rec print_type ~scope env ty =
  match get_desc ty with
  | Tvar _ | Tunivar _ ->
    begin match List.assoc_opt (get_id ty) env with
      | Some printed -> printed
      | None ->
        free_variable := true;
        note_opaque "'_" "free-variable";
        "'_"
    end
  | Tarrow (_, dom, cod, _) ->
    Printf.sprintf "(%s -> %s)" (print_type ~scope env dom) (print_type ~scope env cod)
  | Ttuple _ ->
    "(" ^ String.concat " * " (List.map (print_type ~scope env) (tuple_components ty)) ^ ")"
  | Tconstr (p, args, _) -> print_constructor ~scope env p args
  | Tobject (fields, _) ->
    (* An object type is a payload's type parameter in [Tacexpr], where it
       says which arguments a tactic expression holds. *)
    guarded ty @@ fun () ->
    "< "
    ^ String.concat "; "
        (List.map
           (fun (n, ty) -> n ^ " : " ^ print_type ~scope env ty)
           (methods_of fields))
    ^ " >"
  | Tfield _ | Tnil ->
    let name = "<object>" in
    note_opaque name "object"; name
  | Tvariant row ->
    (* A polymorphic variant can hold itself with no declaration between
       ([[`A of 'a] as 'a]), as an object type can. *)
    guarded ty @@ fun () ->
    let fields =
      List.map
        (fun (label, field) ->
           match row_field_repr field with
           | Rpresent None | Reither (_, [], _) -> "`" ^ label
           | Rabsent -> "`" ^ label ^ " (absent)"
           | Rpresent (Some ty) ->
             Printf.sprintf "`%s of %s" label (print_type ~scope env ty)
           | Reither (_, tys, _) ->
             Printf.sprintf "`%s of %s" label
               (String.concat " & " (List.map (print_type ~scope env) tys)))
        (List.sort (fun (a, _) (b, _) -> String.compare a b) (row_fields row))
    in
    "[" ^ String.concat " | " fields ^ "]"
  | Tpoly (ty, []) -> print_type ~scope env ty
  | Tpoly (body, variables) ->
    (* A polymorphic field ([Util.Empty.t]'s [abort]): its variables are
       bound here, and are not free. *)
    let names = List.mapi (fun i _ -> Printf.sprintf "'p%d" i) variables in
    let env = List.map2 (fun v n -> (get_id v, n)) variables names @ env in
    Printf.sprintf "%s. %s" (String.concat " " names) (print_type ~scope env body)
  | Tpackage _ ->
    let name = "<module>" in
    note_opaque name "first-class-module"; name
  | _ ->
    (* [get_desc] follows [Tlink] and [Tsubst]. What is left is a form of
       [type_desc] a later compiler added ([Tfunctor], OCaml 5.5), which the
       payload types of this build do not reach; the catch-all is what lets
       one text compile on every version. *)
    fatal "a type of a form this tool does not read, in %s" (String.concat "." scope)

and print_constructor ~scope env p args =
  let candidates = candidate_names scope p in
  let name = List.hd candidates in
  let applied name args =
    match args with
    | [] -> name
    | [ a ] -> a ^ " " ^ name
    | l -> "(" ^ String.concat ", " l ^ ") " ^ name
  in
  if List.mem name predefined then
    applied name (List.map (print_type ~scope env) args)
  else
    match find_declaration scope p with
    | Some (name, (owner, decl)) ->
      begin match kind decl with
        | Abstract (Some _) when List.mem name !expanding ->
          note_opaque name "alias-holds-itself";
          applied name (List.map (print_type ~scope env) args)
        | Abstract (Some manifest) ->
          (* An alias: what it stands for is what a .vo holds. *)
          expanding := name :: !expanding;
          let printed =
            print_type ~scope:owner (instantiate ~scope ~owner env decl args) manifest
          in
          expanding := List.tl !expanding;
          printed
        | Abstract None ->
          note_opaque name "abstract";
          applied name (List.map (print_type ~scope env) args)
        | Record _ | Variant _ | Open ->
          print_declaration ~scope:owner name decl;
          applied name (List.map (print_type ~scope env) args)
      end
    | None ->
      (* The path names no declaration this tool read. A path that applies a
         functor is written out with every local name of it qualified by the
         unit it is written in, so that two units' [Set.Make(Self)] are two
         names. *)
      let name = if functor_applied p then qualified_path ~scope p else name in
      let reason =
        if functor_applied p then "functor-application"
        else if local_path p then "functor-argument-or-local"
        else if Hashtbl.mem units (List.hd (String.split_on_char '.' name)) then "functor-result"
        else "another-package"
      in
      note_opaque name reason;
      applied name (List.map (print_type ~scope env) args)

(* What a use of a declaration instantiates inside its body. A parameter is
   paired with the argument at the use: a parameter under a
   [constraint 'a = < term : 't; ... >] (plugins/ltac/tacexpr.mli) is an
   object type, and pairing its methods with the argument's binds the
   variables the body reads, so that they print as the use's types and not
   as ['_]. *)
and instantiate ~scope ~owner env decl args =
  let bound = ref [] in
  (* An argument is often written as an abbreviation of what it stands for
     ([g_dispatch] for the object of methods in plugins/ltac/tacexpr.mli),
     and the parameter is the shape itself, so the abbreviation is resolved
     before the two are paired, in the module it is declared in. *)
  let rec expand ~fuel arg_scope arg =
    if fuel <= 0 then (arg_scope, arg)
    else
      match get_desc arg with
      | Tconstr (p, [], _) ->
        begin match find_declaration arg_scope p with
          | Some (_, (owner, decl)) when decl.type_params = [] ->
            begin match kind decl with
              | Abstract (Some manifest) -> expand ~fuel:(fuel - 1) owner manifest
              | _ -> (arg_scope, arg)
            end
          | _ -> (arg_scope, arg)
        end
      | _ -> (arg_scope, arg)
  in
  let rec pair param (arg_scope, arg) =
    (* A method's type is universally quantified over nothing
       ([Tpoly (t, [])]); the two sides are paired under that wrapper. *)
    let strip t = match get_desc t with Tpoly (t, []) -> t | _ -> t in
    let param = strip param and arg = strip arg in
    let shaped () =
      match get_desc param, get_desc arg with
      | (Tobject _ | Ttuple _ | Tarrow _), Tconstr _ -> expand ~fuel:4 arg_scope arg
      | _ -> (arg_scope, arg)
    in
    match get_desc param with
    | Tvar _ | Tunivar _ ->
      let id = get_id param in
      if not (List.mem_assoc id !bound) then
        bound := (id, print_type ~scope:arg_scope env arg) :: !bound
    | Tobject (fields, _) ->
      let arg_scope, arg = shaped () in
      begin match get_desc arg with
        | Tobject (arg_fields, _) ->
          let arg_methods = methods_of arg_fields in
          List.iter
            (fun (name, ty) ->
               match List.assoc_opt name arg_methods with
               | Some arg_ty -> pair ty (arg_scope, arg_ty)
               | None -> ())
            (methods_of fields)
        | _ -> ()
      end
    | Ttuple _ ->
      let arg_scope, arg = shaped () in
      begin match get_desc arg with
        | Ttuple _ ->
          let ps = tuple_components param and a = tuple_components arg in
          if List.length ps = List.length a then
            List.iter2 (fun p a -> pair p (arg_scope, a)) ps a
        | _ -> ()
      end
    | Tconstr (p, ps, _) ->
      begin match get_desc arg with
        | Tconstr (q, a, _)
          when List.length ps = List.length a
            (* The parameter's path is written in the declaring module, the
               argument's at the use. *)
            && candidate_names owner p = candidate_names arg_scope q ->
          List.iter2 (fun p a -> pair p (arg_scope, a)) ps a
        | _ -> ()
      end
    | Tarrow (_, d, c, _) ->
      let arg_scope, arg = shaped () in
      begin match get_desc arg with
        | Tarrow (_, d', c', _) -> pair d (arg_scope, d'); pair c (arg_scope, c')
        | _ -> ()
      end
    | _ -> ()
  in
  let rec walk params args =
    match params, args with
    | p :: ps, a :: rest -> pair p (scope, a); walk ps rest
    | _ -> ()
  in
  walk decl.type_params args;
  !bound

and print_declaration ~scope name decl =
  if not (Hashtbl.mem printed_declarations name) then begin
    (* Registered before its body is printed: a type that holds itself must
       stop here. *)
    Hashtbl.add printed_declarations name "";
    (* A declaration prints the same wherever it is reached from: neither
       the aliases the use was expanding nor what that use's own payload
       held belongs to it. *)
    let saved_expanding = !expanding and saved_free = !free_variable in
    let saved_printing = !printing in
    expanding := [];
    printing := [];
    (* [name_variables] is why a parameter under a constraint reads well: it
       names not only the parameter itself but every variable its methods
       hold. *)
    let parameters = decl.type_params in
    let variables = ref [] and named = ref 0 in
    let parameter_variable () =
      let n = variable_name !named in
      incr named; n
    in
    List.iter (name_variables ~fresh:parameter_variable variables) parameters;
    let env = List.rev !variables in
    let printed_parameters = List.map (print_type ~scope env) parameters in
    let label env l =
      Printf.sprintf "%s%s : %s"
        (match l.ld_mutable with
         | Asttypes.Mutable -> "mutable "
         | Asttypes.Immutable -> "")
        (Ident.name l.ld_id) (print_type ~scope env l.ld_type)
    in
    (* A constructor of a generalised variant writes its arguments in its
       own variables: [cd_res] says which of them the type's parameters are
       at this constructor, and the ones it does not reach are the
       constructor's existentials, named ['e0] and on. The result is
       printed, so that which parameter a constructor holds is part of the
       printing. *)
    let constructor c =
      let variables = ref env in
      begin match c.cd_res with
        | Some res ->
          begin match get_desc res with
            | Tconstr (_, result_arguments, _) ->
              List.iteri
                (fun i a ->
                   match get_desc a with
                   | (Tvar _ | Tunivar _)
                     when not (List.mem_assoc (get_id a) !variables)
                       && i < List.length printed_parameters ->
                     variables := (get_id a, List.nth printed_parameters i) :: !variables
                   | _ -> ())
                result_arguments
            | _ -> ()
          end
        | None -> ()
      end;
      let existentials = ref 0 in
      let existential () =
        let n = Printf.sprintf "'e%d" !existentials in
        incr existentials; n
      in
      let arguments = constructor_arguments c.cd_args in
      begin match arguments with
        | Tuple tys -> List.iter (name_variables ~fresh:existential variables) tys
        | Inline labels ->
          List.iter (fun l -> name_variables ~fresh:existential variables l.ld_type) labels
      end;
      begin match c.cd_res with
        | Some res -> name_variables ~fresh:existential variables res
        | None -> ()
      end;
      let env = !variables in
      let printed_arguments =
        match arguments with
        | Tuple [] -> ""
        | Tuple tys -> " of " ^ String.concat " * " (List.map (print_type ~scope env) tys)
        | Inline labels -> " of {" ^ String.concat "; " (List.map (label env) labels) ^ "}"
      in
      let result =
        match c.cd_res with None -> "" | Some res -> " : " ^ print_type ~scope env res
      in
      Ident.name c.cd_id ^ printed_arguments ^ result
    in
    let body =
      match kind decl with
      | Record (labels, repr) ->
        Printf.sprintf "%s {%s}" repr (String.concat "; " (List.map (label env) labels))
      | Variant (constructors, repr) ->
        Printf.sprintf "%s %s" repr
          (String.concat " | " (List.map constructor constructors))
      | Open -> "extensible"
      | Abstract _ -> assert false (* its caller handles it *)
    in
    let printed_parameters =
      match printed_parameters with
      | [] -> ""
      | [ a ] -> a ^ " "
      | l -> "(" ^ String.concat ", " l ^ ") "
    in
    Hashtbl.replace printed_declarations name
      (Printf.sprintf "type %s%s = %s" printed_parameters name body);
    expanding := saved_expanding;
    printing := saved_printing;
    free_variable := saved_free
  end

(* {1 The printing} *)

let site_path site = String.concat "." (List.hd site.s_scope :: site.s_binding)


(* What a site is called in the printing. A kind the site names is named by
   that alone: the value and module names around the reference are where to
   look for it, not what it stores, and a renamed local binding must not
   fail the test. A site that builds its kind's name at run time has no
   other handle, so for those the path is the name. *)
let site_key site =
  match site.s_name with
  | Some name -> name
  | None -> "? " ^ site_path site

let print_sites b sites =
  (* Every site is numbered inside its key, from the order the sites were
     read in, which is their order in the file that holds them. Numbering
     them all, rather than only the keys that repeat, is what lets a site
     added to a file leave the lines of the sites before it as they were. *)
  let seen = Hashtbl.create 97 in
  let lines =
    List.map
      (fun site ->
         let key = site_key site in
         let n = match Hashtbl.find_opt seen key with None -> 1 | Some n -> n + 1 in
         Hashtbl.replace seen key n;
         let where = Printf.sprintf "%s#%d" key n in
         (* The types the site's own toplevel value reaches: what a caller of
            a site that stores a variable can choose. Their definitions are
            printed with the rest, so [Goptions.option_kind] and its four
            constructors are pinned there; the names alone are in the line,
            so that an unrelated argument added to that value does not
            rewrite it. *)
         let value () =
           match site.s_value with
           | None -> ""
           | Some ty ->
             let variables = ref [] and named = ref 0 in
             let fresh () =
               let n = variable_name !named in
               incr named; n
             in
             name_variables ~fresh variables ty;
             ignore (print_type ~scope:site.s_scope (List.rev !variables) ty);
             match reached_names ~scope:site.s_scope ty with
             | [] -> ""
             | names -> " ; reaches " ^ String.concat ", " names
         in
         (* A reference inside a functor's body is one kind per application
            of that functor, at the types the application chooses. *)
         let functor_note =
           match site.s_functor with
           | None -> ""
           | Some name ->
             Printf.sprintf " ; in-functor %s" name
         in
         (* Only a line that does not pin its payload names the types its
            own value's type reaches. *)
         let unresolved printed reason =
           Printf.sprintf "payload_unresolved %s %s%s%s%s"
             where printed reason (value ()) functor_note
         in
         let resolved printed =
           if !free_variable then
             unresolved printed
               " free-variable"
           else Printf.sprintf "payload %s %s%s" where printed functor_note
         in
         free_variable := false;
         match site.s_stored with
         | Unknown reason -> unresolved "?" (" " ^ reason)
         | One ty -> resolved (print_type ~scope:site.s_scope [] ty)
         | Pair (id, ty) ->
           let printed_id = print_type ~scope:site.s_scope [] id in
           let printed = print_type ~scope:site.s_scope [] ty in
           resolved (Printf.sprintf "(%s * %s)" printed_id printed))
      sites
  in
  List.iter
    (fun l -> Buffer.add_string b l; Buffer.add_char b '\n')
    (List.sort String.compare lines)

(* What each table of [Goptions] stores: [MakeStringTable] holds strings,
   and [MakeRefTable (A)] holds [A.t], which the functor's own body cannot
   name. Without this the element type of a table would be pinned nowhere,
   as the type an option stores was before [option_payload]. *)
let print_tables b =
  (* A type named rather than reached from a payload: its definition is
     printed as any other, an alias is followed, and the name is read in the
     unit it is written in as well as globally. *)
  let print_named ~scope name =
    let candidates =
      List.map resolve_alias
        [ name; String.concat "." (List.hd scope :: [ name ]) ]
    in
    match
      List.find_map
        (fun n -> match Hashtbl.find_opt declarations n with
           | Some decl -> Some (n, decl)
           | None -> None)
        candidates
    with
    | None -> note_opaque name "functor-result"; name
    | Some (name, (owner, decl)) ->
      begin match kind decl with
        | Abstract (Some manifest) -> print_type ~scope:owner [] manifest
        | Abstract None -> note_opaque name "abstract"; name
        | Record _ | Variant _ | Open ->
          print_declaration ~scope:owner name decl;
          name
      end
  in
  List.iter
    (fun l -> Buffer.add_string b l; Buffer.add_char b '\n')
    (List.sort String.compare
       (List.map
          (fun table ->
             let element =
               match table.t_element with
               | None -> "string"
               | Some argument ->
                 let path = Path.Pdot (argument, "t") in
                 (match find_declaration table.t_scope path with
                  | Some _ -> print_constructor ~scope:table.t_scope [] path []
                  | None ->
                    (* The argument is itself a functor application: what it
                       stores is the type that functor's body declares. *)
                    let name =
                      String.concat "." (table.t_scope @ [ path_name argument ])
                    in
                    (match Hashtbl.find_opt module_applications (resolve_alias name) with
                     | Some functor_name ->
                       print_named ~scope:table.t_scope (functor_name ^ ".t")
                     | None -> print_constructor ~scope:table.t_scope [] path []))
             in
             Printf.sprintf "table_payload %s %s" table.t_name element)
          !tables))

let representation () =
  let b = Buffer.create 65536 in
  Buffer.add_string b "object_payloads 1\n";
  (* The sites in the order they were read, which is the order they are
     numbered in; the lines themselves are sorted by [print_sites]. *)
  print_sites b (List.rev !sites);
  print_tables b;
  let add_lines table render =
    List.iter
      (fun l -> Buffer.add_string b l; Buffer.add_char b '\n')
      (List.sort String.compare (Hashtbl.fold (fun k v acc -> render k v :: acc) table []))
  in
  add_lines printed_declarations (fun _ line -> line);
  add_lines opaques (fun name reason -> Printf.sprintf "opaque %s %s" name reason);
  Buffer.contents b

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let as_module, dirs =
    match args with
    | "--ml" :: dirs -> true, dirs
    | dirs -> false, dirs
  in
  if dirs = [] then fatal "usage: vo_payloads [--ml] DIR...";
  (* A directory with no typed tree is one this list and checker/dune's
     dependencies disagree about. *)
  let per_directory =
    List.map
      (fun dir ->
         let implementations, interfaces = trees dir in
         if implementations = [] then
           fatal "no .cmt under %s: it is not built, or not a directory this rule depends on"
             dir;
         (implementations, interfaces))
      dirs
  in
  (* Implementations first: a type an interface makes abstract is read from
     the implementation that defines it. *)
  List.iter (fun (implementations, _) -> List.iter read_tree implementations) per_directory;
  List.iter (fun (_, interfaces) -> List.iter read_tree interfaces) per_directory;
  if !sites = [] then
    fatal "no reference to Libobject.declare_object under %s" (String.concat " " dirs);
  let text = representation () in
  if as_module then begin
    print_string
      "(* Generated by checker/vo_payloads.ml from the typed trees of this\n\
      \   build; see checker/dune. *)\n\
       let payloads = {vo_payloads|";
    print_string text;
    print_string "|vo_payloads}\n"
  end
  else print_string text
