(* Gate review, INFRA-361 gap 2. [inner] runs inside the [Load]: it is
   ineligible and leaves no candidate open. The edited Loaded.v changes the
   body of [k]: [reads_loaded] unfolds it and misses on that read. [after]
   replays. The path is relative: the .vo keeps the loaded file's path, and
   the runner builds replay and stock in two directories. *)
Load "./Loaded.v".

Lemma reads_loaded : k = 3.
Proof. unfold k. reflexivity. Qed.

Lemma after : 1 = 1.
Proof. reflexivity. Qed.
