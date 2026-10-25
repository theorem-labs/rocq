(* Y is the first build, where [c] is proved with [ax1]. *)
Require Y.
Print Assumptions Y.c.
(* X.vo is a copy of the second build's Y.vo, so it holds library Y and not
   X, and this Require fails. Before it fails, it reads X.vo and records its
   opaque proofs as those of Y, which is loaded: the environment stays the
   same, and [c]'s proof now uses [ax2]. *)
Fail Require X.
Print Assumptions Y.c.
