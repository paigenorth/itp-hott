Require Export UniMath.Foundations.All.

(* Exercise 1*)

(* The unit type is contractible.*)

Print unit.

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
    Admitted.

(* Exericse 2 *)

(* The empty type is a proposition. *)

Theorem empty_is_prop : isaprop (∅).
    Admitted.

(* Exercise 3 *)

(* Every contractible type is a proposition. *)

Theorem contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
    Admitted.

(* Exercise 4 *)

(* If a proposition is inhabited, then it is contractible.*)

Theorem inhab_prop_is_contr {P : UU} (p : P) (h : isaprop P) : iscontr P.
    Admitted.

(* Exercise 5 *)

(* If a type has h-level n, then it has h-level n+1.*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
    Admitted.