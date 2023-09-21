Require Export UniMath.Foundations.All.

(* Exercise 1*)

(* ~weq A B~ is the type of equivalences from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    Admitted.

(* Exercise 2 *)

(* A contractible type is connected.*)

Theorem contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
    Admitted.

(* Exercise 3 *)

(* Any contractible type is equivalent to the unit type.*)

(* Hint: use ~contr_is_prop~ and ~unit_iscontr~ that were shown in the last exercise set. *)

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
    Admitted.

(* Exercise 4*)

(* Difficult *)

(* Every statement ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
    Admitted.