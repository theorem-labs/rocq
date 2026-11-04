(* Reifying a stuck match on a proof-irrelevant inductive must leave its
   inversion indices alone: the FCaseInvert arm of CClosure.to_constr has
   already reified them, so substituting them again renames a de Bruijn index
   (first test) or an abstract universe (second test). *)
Set Universe Polymorphism.
Set Definitional UIP.

Inductive seq {A : Type} (x : A) : A -> SProp :=
| srefl : seq x x.

(* the term half: `q` shifts the environment, which is what makes the second
   substitution land on the wrong variable *)
Definition reify_lazy :=
  Eval lazy in
  (fun (A : Type) (x y : A) (e : seq x y) =>
     (fun (q : A) (p : seq x y) =>
        match p in seq _ z return Type with
        | srefl _ => unit
        end) x e).

(* the universe half: a polymorphic body is checked with Var levels, so
   applying the instance twice renames a universe. `honest` below is accepted
   only when the indices are left alone AND the parameters, return clause and
   branches are substituted (rocq-prover/rocq#22381). *)

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y : A} (e : seq x y) : P x -> P y :=
  match e in seq _ y return P x -> P y with
  | srefl _ => fun v => v
  end.

Axiom ax@{a b c d | a < c, b < c, c < d} : @seq@{d} Type@{c} Type@{a} Type@{b}.

(* stuck: the index Type@{b} is not convertible to the parameter Type@{a} *)
Definition choice@{a b c d | a < c, b < c, c < d} : Type@{c} :=
  match ax@{a b c d} in seq _ z return Type@{c} with
  | srefl _ => Type@{a}
  end.

Axiom inh@{a b c d | a < c, b < c, c < d} : choice@{a b c d}.

(* the weak head of `force` is `T -> unit`, with `T` the stuck match reached
   through `choice`, at the root of the result: an identity lift *)
Definition force@{a b c d t | a < c, b < c, c < d, d < t} : Type@{c} :=
  let T := (fun _ : unit => choice@{a b c d}) tt in
  @transport@{t t} Type@{c} (fun X : Type@{c} => X -> Type@{c})
    T (match ax@{a b c d} in seq _ z return Type@{c} with
       | srefl _ => Type@{a}
       end)
    (@srefl@{t} Type@{c} T)
    (fun _ : T => T -> unit)
    inh@{a b c d}.

Definition payload@{a b c d | a < c, b < c, c < d} : choice@{a b c d} -> unit :=
  fun _ => tt.

Definition honest@{a b c d t | a < c, b < c, c < d, d < t} : unit :=
  (payload@{b a c d} : force@{b a c d t}) inh@{b a c d}.

Definition honest_id@{a b c d t | a < c, b < c, c < d, d < t} : unit :=
  (payload@{a b c d} : force@{a b c d t}) inh@{a b c d}.
