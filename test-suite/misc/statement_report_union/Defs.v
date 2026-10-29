(* Objects for misc/statement_report_union.sh, compiled with -noinit. For
   each row, a model, a trusted constant [t_<row>] and a module type
   [S_<row>] whose field [f] has the trusted constant's type. The sealing
   of every row but [part] needs universe constraints that [c < a] allows
   alone; [part]'s is refused. Some pairs of rows need constraints that
   contradict each other. *)

Universe a b c.
Constraint c < a.

Parameter m_a : Type@{a}.
Parameter m_b : Type@{b}.
Parameter m_part : forall _ : Type@{b}, Type@{a}.
Polymorphic Definition m_poly@{u} : forall _ : Type@{u}, Type@{u} := fun A => A.

(* Sealing adds [a <= b]. *)
Parameter t_ab : Type@{b}.
Module Type S_ab. Parameter f : Type@{b}. End S_ab.

(* Sealing adds [b <= c]: with [a <= b], [a <= b <= c < a]. *)
Parameter t_bc : Type@{c}.
Module Type S_bc. Parameter f : Type@{c}. End S_bc.

(* The domains need [b = c], which contradicts [a <= b]; the codomains then
   need [a <= c], which contradicts [c < a], so sealing is refused. *)
Parameter t_part : forall _ : Type@{c}, Type@{c}.
Module Type S_part. Parameter f : forall _ : Type@{c}, Type@{c}. End S_part.

(* One instance of the model, its fresh universe equal to [a]. *)
Parameter t_p_a : forall _ : Type@{a}, Type@{a}.
Module Type S_p_a. Parameter f : forall _ : Type@{a}, Type@{a}. End S_p_a.

(* Another instance, its fresh universe equal to [c]: each sealing declares
   its own fresh universe, so this does not contradict [p_a]. *)
Parameter t_p_c : forall _ : Type@{c}, Type@{c}.
Module Type S_p_c. Parameter f : forall _ : Type@{c}, Type@{c}. End S_p_c.

(* The fresh universe [u] needs [u = a] and [u <= b], so [a <= b]. *)
Parameter t_p_ab : forall _ : Type@{a}, Type@{b}.
Module Type S_p_ab. Parameter f : forall _ : Type@{a}, Type@{b}. End S_p_ab.
