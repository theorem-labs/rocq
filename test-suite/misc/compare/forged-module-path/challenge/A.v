(* The permitted axioms are the task's givens, named by the names they
   print. A module path and a library path print alike: the constant g of a
   module Q of the library Top.P prints Top.P.Q.g, the name of the given g
   of the library Top.P.Q. The bad answers declare such a module in the file
   they may change and prove thm from it; the pre-checked Top.P.Q is not
   compared declaration by declaration, so only the kernel name of the
   axiom tells the forgery from the given (dispatch://AENGENVS-153). *)

Require Top.P.
Require Top.P.Q.

Theorem thm : 0 = 1 /\ 1 = 2 /\ 2 = 3.
Proof.
Admitted.
