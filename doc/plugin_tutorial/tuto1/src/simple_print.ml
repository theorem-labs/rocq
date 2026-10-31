(* A more advanced example of how to explore the structure of terms of
  type constr is given in the coq-dpdgraph plugin. *)

let simple_body_access ~opaque_access gref =
  let open Names.GlobRef in
  match gref with
  | VarRef _ ->
    failwith "variables are not covered in this example"
  | IndRef _ ->
    failwith "inductive types are not covered in this example"
  | ConstructRef _ ->
    failwith "constructors are not covered in this example"
  | ConstRef cst ->
    (* most commands should not use body_of_constant and opaque accessors,
       but for printing it's ok. [Global.body_of_constant] rather than
       [body_of_constant_body], because only [body_of_constant] logs what it
       reads for the keep rule (D18): its answer tells an axiom from an
       opaque proof, and [MyPrint] fails on the first, so a [Fail MyPrint c]
       observes it. *)
    match Global.body_of_constant opaque_access cst with
    | Some(e, _, _) -> EConstr.of_constr e
    | None -> failwith "This term has no value"

