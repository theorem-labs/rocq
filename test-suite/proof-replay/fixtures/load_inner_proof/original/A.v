(* Gate review, INFRA-361 gap 2. [inner] runs inside the [Load]: it is
   ineligible and leaves no candidate open. The path is relative: the .vo
   keeps the loaded file's path, and the runner builds replay and stock in
   two directories. *)
Load "./Loaded.v".
