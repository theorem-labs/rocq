(* Y is the first build, where [c] is proved with [ax1]. *)
Require Y.
Print Assumptions Y.c.
(* X.vo is a copy of the second build's Y.vo, so it holds library Y and not
   X, and this Require fails. It reads X.vo, but a library's intern fills no
   table until the name in the file is checked, so Y keeps the opaque proofs
   it was loaded with: [c]'s proof still uses [ax1], and the query after this
   one must say so, with the traversal reuse as without it. *)
Fail Require X.
Print Assumptions Y.c.
